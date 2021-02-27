import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Sequence as Seq
import System.Environment
import System.IO


-- Counts type alias, for convenience
type Counts = Map.Map [Char] (Int, [Int])

-- Outputs the number of occurrences and locations of patterns within the text
{- e.g. count ["A", "AG", "C", "CAA", "GAG", "GC", "GCA"] "ABCDEFGAGCAAGAGAGCA" = fromList [("A",(7,[1,8,11,12,14,16,19])),("AG",(4,[8,12,14,16])),("C",(3,[3,10,18])),("CAA",(1,[10])),("GAG",(3,[7,13,15])),("GC",(2,[9,17])),("GCA",(2,[9,17]))] -}
count :: [[Char]] -> [Char] -> Counts
count [] _ = Map.empty
count dictstrs text = count' text trie rindex counts 1
  where trie = addlinks (createtrie dictstrs)
        counts = Map.fromList [(dictstr, (0, []))| dictstr <- dictstrs]

-- Helper for count
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
createtrie strs = foldl (\ trie str -> insert str trie) emptytrie strs

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
                  else calcflinkrec trie node pflink
                dlink' = if istrivialnode
                  then dlink node -- -1
                  else calcdlink trie node flink'

-- Recursively calculate failure link for a non-trivial node (node with depth > 1)
calcflinkrec :: Trie -> Node -> Int -> Int
calcflinkrec trie node pflink
  | Map.member pch (children pfnode)   = (children pfnode) Map.! pch
  | pflink == rindex                   = rindex
  | otherwise                          = calcflinkrec trie node (flink pfnode)
  where pch    = pchar node
        pfnode = trie IntMap.! pflink

-- Calculate dictionary link for a non-trivial node (node with depth > 1)
calcdlink :: Trie -> Node -> Int -> Int
calcdlink trie node flink = if leaffor fnode == "" then dlink fnode else flink
  where fnode = trie IntMap.! flink


-- outputs the list sorted from greatest to least
-- sorts the texts by the number of unique patterns and the total number of patterns they contain
customSort :: (Ord d, Ord e) => [(a, b, c, d, e)] -> [(a, b, c, d, e)]
customSort []     = []
customSort ((a1,b1,c1,d1,e1):xs) = (customSort greater) ++ [(a1,b1,c1,d1,e1)] ++ (customSort lesser)
    where
        lesser  = filter (\(a2,b2,c2,d2,e2) -> (d2 < d1) || (d2 == d1 && e2 < e1)) xs
        greater = filter (\(a2,b2,c2,d2,e2) -> (d2 > d1) || (d2 == d1 && e2 >= e1)) xs



-- run on the command line using aho text.txt pat1 pat2 ... patn
-- e.g. aho text.txt a ab aba cb cd def => line 1: text = abcdeababa; 4 unique matches; 10 total matches; [("a"(4,[1,6,8,10])),("ab",(3,[1,6,8])),("aba",(2,[6,8])),("cd",(1,[3]))]
main = do
  args <- getArgs
  let (file:patterns) = args

  content <- readFile file
  let linesOfFiles = lines content
      matched = map (\(idx, line) -> (idx, line, hasMatch patterns line)) . filter (\(a,b) -> b /= []) $ zip [1..] linesOfFiles

  mapM_ putStrLn $ map statement $ customSort $ map (\(idx,line,lst) -> (idx, line, lst, unique lst, total lst)) matched
  where
    hasMatch pat txt = filter (\(a,(b,c)) -> b > 0) $ Map.toList (count pat txt)
    unique lst = length lst
    total lst =  foldr  (\(a,(b,c)) acc -> b + acc) 0 lst
--    statement (a,b,c,d,e) = "line " ++ show a ++ ": text = " ++ b ++ "; " ++ show d ++ " unique matches; " ++ show e ++ " total matches; " ++ show c
    statement (a,b,c,d,e) = "line " ++ show a ++ "; " ++ show d ++ " unique matches; " ++ show e ++ " total matches; " ++ show c
