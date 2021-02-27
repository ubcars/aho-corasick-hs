import Data.Char
import Data.List 
import Data.Maybe
import Control.Monad
import System.Environment
import System.IO


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


-- outputs the list sorted from greatest to least
-- sorts the texts by the number of unique patterns and the total number of patterns they contain
customSort :: (Ord c, Ord d) => [(a, b, c, d, e)] -> [(a, b, c, d, e)]
customSort []     = []
customSort ((a1,b1,c1,d1,e1):xs) = (customSort greater) ++ [(a1,b1,c1,d1,e1)] ++ (customSort lesser)
    where
        lesser  = filter (\(a2,b2,c2,d2,e2) -> (c2 < c1) || (c2 == c1 && d2 < d1)) xs
        greater = filter (\(a2,b2,c2,d2,e2) -> (c2 > c1) || (c2 == c1 && d2 >= d1)) xs



-- run on the command line using rk text.txt pat1 pat2 ... patn
-- e.g. rk text.txt a ab aba cb cd def => line 1: text = abcdeababa; 4 unique matches; 10 total matches; [("a",4,[1,6,8,10]),("ab",3,[1,6,8]),("aba",2,[6,8]),("cd",1,[3])]
main = do
  args <- getArgs
  let (file:patterns) = args

  content <- readFile file
  let linesOfFiles = lines content

  mapM_ putStrLn $ map statement $ customSort $ map (\(idx, line) -> (idx, line, unique line patterns, total line patterns, matched line patterns)) . filter (\(a,b) -> b /= []) $ zip [1..] linesOfFiles
  where
--    statement (a,b,c,d,e) = "line " ++ show a ++ ": text = " ++ b ++ "; " ++ show c ++ " unique matches; " ++ show d ++ " total matches; " ++ show e
    statement (a,b,c,d,e) = "line " ++ show a ++ "; " ++ show c ++ " unique matches; " ++ show d ++ " total matches; " ++ show e
    matched txt pat = filter (\(a,b,c) -> b > 0) $ rabinKarp txt pat
    unique txt pat = length $ matched txt pat   
    total txt pat =  foldr  (\(a,b,c) acc -> b + acc) 0 $ matched txt pat
