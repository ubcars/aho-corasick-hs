import Data.Char
import Data.List
import Data.Maybe
import Control.Monad
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Sequence as Seq
import System.Environment
import System.IO

-- Compare runtimes of Aho-Corasick to Rabin-Karp in ghci by entering
-- :set +s
-- then running
-- ahoCorasick "some string" ["search", "strings"]
-- rabinKarp   "some string" ["search", "strings"]

{- Aho-Corasick -}

-- Counts type alias, for convenience
type Counts = Map.Map [Char] (Int, [Int])

-- Outputs the number of occurrences and locations of patterns within the text
-- e.g. ahoCorasick "ABCDEFGAGCAAGAGAGCA" ["A", "AG", "C", "CAA", "GAG", "GC", "GCA"] = [("A",(7,[1,8,11,12,14,16,19])),("AG",(4,[8,12,14,16])),("C",(3,[3,10,18])),("CAA",(1,[10])),("GAG",(3,[7,13,15])),("GC",(2,[9,17])),("GCA",(2,[9,17]))]
ahoCorasick :: String -> [String] -> [(String, Int, [Int])]
ahoCorasick _ [] = []
ahoCorasick text dictstrs = map (\ (str, (count, indices)) -> (str, count, indices)) (Map.toList counts)
  where trie = addlinks (createtrie dictstrs)
        initcounts = Map.fromList [(dictstr, (0, []))| dictstr <- dictstrs]
        counts = count' text trie rindex initcounts 1

-- Helper for ahoCorasick
count' :: [Char] -> Trie -> Int -> Counts -> Int -> Counts
count' [] trie state counts index = counts
count' (c:rest) trie state counts index = count' rest trie currentState updatedCounts (index + 1)
        where currentState = count'' c trie state
              updatedCounts = count''' trie currentState counts index

-- Helper for count'
count'' :: Char -> Trie -> Int -> Int
count'' c trie state
         | Map.member c child = nextStateFound
         | state == rindex = state
         | otherwise = count'' c trie nextStateFail
         where node = trie IntMap.! state
               child = children node
               nextStateFound = child Map.! c
               nextStateFail = flink node

-- Helper for count'
count''' :: Trie -> Int -> Counts -> Int -> Counts
count''' trie checkState counts index
         | (leaffor node) /= "" = count''' trie nextState updatedCounts index
         | (dlink node) /= -1 = count''' trie nextState counts index
         | otherwise = counts
         where node = trie IntMap.! checkState
               nextState = flink node
               indexOfMatch = index + 1 - length (leaffor node)
               updatedCounts = Map.adjust (\ (x,y) -> (x + 1, y ++ [indexOfMatch])) (leaffor node) counts

-- Represents a state in the AC trie
data Node = Node { pchar    :: Char             -- Char encountered to move from parent to this node
                 , pindex   :: Int              -- Index of parent node in trie
                 , leaffor  :: [Char]           -- Word for which this node is a leaf
                 , children :: Map.Map Char Int -- Indexes of child nodes in trie
                 , flink    :: Int              -- Failure link:    index of node representing the longest prefix which is a suffix of the string represented by this node
                 , dlink    :: Int              -- Dictionary link: index of node representing a dictionary string which should be counted but is a substring of the string represented by this node
                 } deriving (Show)

-- Empty node
emptynode = Node { pchar    = '_'
                 , pindex   = -1
                 , leaffor  = ""
                 , children = Map.empty
                 , flink    = -1
                 , dlink    = -1
                 }

-- Trie type alias, for convenience
type Trie = IntMap.IntMap Node

-- Index of root node of trie
rindex = 0

-- Empty trie containing only root node
emptytrie = IntMap.insert rindex emptynode IntMap.empty

-- Create trie from list of strings
-- e.g. createtrie ["a", "ab"] => [Node { pchar = '_', children = ['a'] }, Node { pchar = 'a', children = ['b'], leaffor = "a" }, Node { pchar = 'b', children = [], leaffor = "ab" }]
createtrie :: [[Char]] -> Trie
createtrie strs = foldl (\ trie str -> Main.insert str trie) emptytrie strs

-- Insert single string into trie
-- e.g. insert "ab" emptytrie = [Node { pchar = '_', children = ['a'] }, Node { pchar = 'a', children = ['b'] }, Node { pchar = 'b', children = [], leaffor = "ab" }
insert :: [Char] -> Trie -> Trie
insert [] trie = trie
insert (h:t) trie = insertat (h:t) (h:t) trie rindex

-- Helper for insert
-- Insert string into trie as a child of the node at pindex
insertat :: [Char] -> [Char] -> Trie -> Int -> Trie
insertat _ [] trie _ = trie
insertat str (h:t) trie pindex = insertat str t nexttrie nextpindex
  where pnode = trie IntMap.! pindex
        cindex     = case Map.lookup h (children pnode) of
          Nothing -> -1
          Just i  -> i
        nextpindex = if cindex == -1
          then IntMap.size trie
          else cindex
        nexttrie   = if cindex == -1
          then IntMap.insert nextpindex cnode trie'
          else IntMap.update (\ node -> Just node { leaffor = if t == "" then str else leaffor node }) nextpindex trie
        cnode      = emptynode { leaffor = if t == "" then str else leaffor emptynode, pindex = pindex, pchar = h }
        children'  = Map.insert h nextpindex (children pnode)
        trie'      = IntMap.update (\ _ -> Just pnode { children = children' }) pindex trie

-- Add failure and dictionary links to trie
addlinks :: Trie -> Trie
addlinks trie = if size == 0 then trie else addlinks' trie queue
  where size  = IntMap.size trie
        queue = rindex Seq.:<| Seq.empty

-- Helper for addlinks
-- Add failure and dictionary links to trie performing breadth-first traversal using a queue
addlinks' :: Trie -> Seq.Seq Int -> Trie
addlinks' trie Seq.Empty = trie
addlinks' trie (nindex Seq.:<| queue) = addlinks' nexttrie nextq
  where node          = trie IntMap.! nindex
        istrivialnode = (nindex == rindex) || (pindex node == rindex)
        nextq         = foldl (\ q i -> q Seq.:|> i) queue (Map.elems (children node))
        nexttrie      = IntMap.insert nindex (node { flink = flink', dlink = dlink' }) trie
          where pnode  = trie IntMap.! (pindex node)
                pflink = flink pnode
                flink' = if istrivialnode
                  then rindex
                  else calcflink trie node pflink
                dlink' = if istrivialnode
                  then dlink node -- -1
                  else calcdlink trie node flink'

-- Recursively calculate failure link for a non-trivial node (node with depth > 1)
calcflink :: Trie -> Node -> Int -> Int
calcflink trie node pflink
  | Map.member pch (children pfnode)   = (children pfnode) Map.! pch
  | pflink == rindex                   = rindex
  | otherwise                          = calcflink trie node (flink pfnode)
  where pch    = pchar node
        pfnode = trie IntMap.! pflink

-- Calculate dictionary link for a non-trivial node (node with depth > 1)
calcdlink :: Trie -> Node -> Int -> Int
calcdlink trie node flink = if leaffor fnode == "" then dlink fnode else flink
  where fnode = trie IntMap.! flink

{- end Aho-Corasick -}

{- Rabin-Karp -}

-- a prime number used to hash more unique values
prime = 1761471161

-- the number of ascii character codes
ascii = 256

-- takes a text and a list of patterns and outputs the number and location of occurrences for each pattern
-- e.g. rabinKarp "abcdeababa" ["a", "ab", "aba", "cb", "cd", "def"] => [("a", 4, [1,6,8,10]), ("ab", 3, [1,6,8]), ("aba", 2, [6,8]), ("cb", 0, []), ("cd", 1, [3]), ("def", 0, [])]
rabinKarp :: String -> [String] -> [(String, Int, [Int])]
rabinKarp text [] = []
rabinKarp text (pattern:rest) = if length pattern == 0
  then [(pattern, 0, [])]
  else [(pattern, count, occurrences)] ++ rabinKarp text rest
    where m = length pattern
          occurrences = map fst $ filter match $ zip [1..] $ scanl next (hash text m) $ scope (m+1) text
          count = length occurrences
          next curr chars = reHash curr (head chars) (last chars) m
          match (start, textHash) = textHash == patternHash && pattern == substring text start m
          patternHash = hash pattern m

-- outputs the substring starting at start with a length of len
-- e.g. substring "abcde" 2 3 => "bcd"
substring :: [a] -> Int -> Int -> [a]
substring text start len = take len $ drop (start - 1) text

-- creates and appends all possible scopes with a length of size characters
-- e.g. scope 3 "abcd" => ["abc", "bcd"]
scope :: Int -> [a] -> [[a]]
scope size [] = []
scope size (x:xs) = if length (x:xs) >= size then take size (x:xs) : scope size xs else scope size xs

-- given a string and an integer m, outputs the hashed value of the first m characters of that string
-- hash = ((asc^(m-1) * ascii char) + (asc^(m-2) * ascii char) + ... + (asc^0 * ascii char)) % q where asc = 256, q = 1761471161
hash :: [Char] -> Int -> Int
hash = hash2 ascii prime
hash2 asc q string m = foldl (\acc x -> (asc * acc + ord x) `mod` q) 0 $ take m string

-- given a hash value, the first character used in that hash value (firstChar), and a new character (nextChar), outputs a new hash value
-- the new hash value is the result of removing the hashing of firstChar and then adding the hashing nextChar
-- reHash = ((previousHash - ((asc^(m-1) % q) * ascii firstChar)) % q * asc + ascii nextChar) % q where asc = 256, q = 1761471161
reHash :: Int -> Char -> Char -> Int -> Int
reHash = reHash2 ascii prime
reHash2 asc q previousHash firstChar nextChar m =
  (removedFirstChar `mod` fromIntegral q * fromIntegral asc + ord nextChar) `mod` fromIntegral q
  where
    removed = if m > 0 then (fromIntegral asc ^ fromIntegral (m-1)) `mod` fromIntegral q else 0
    removedFirstChar = previousHash - fromIntegral removed * ord firstChar

{- end Rabin-Karp -}