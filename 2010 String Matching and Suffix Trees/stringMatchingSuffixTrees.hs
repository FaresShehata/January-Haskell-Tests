import Data.List hiding (insert, partition)
import Data.Ord


data SuffixTree = Leaf Int | Node [(String, SuffixTree)] 
                deriving (Eq, Show)

------------------------------------------------------

isPrefix :: String -> String -> Bool
isPrefix p s = p == take (length p) s

removePrefix :: String -> String -> String
-- Pre: p is a prefix of s
removePrefix p s = drop (length p) s

suffixes :: [a] -> [[a]]
suffixes xs = take (length xs) (iterate tail xs)

isSubstring :: String -> String -> Bool
isSubstring s1 s2 = or $ map (isPrefix s1) (suffixes s2)

findSubstrings :: String -> String -> [Int]
findSubstrings s1 s2 = elemIndices True $ map (isPrefix s1) (suffixes s2)

------------------------------------------------------

getIndices :: SuffixTree -> [Int]
getIndices (Leaf n) = [n]
getIndices (Node ats) = concatMap getIndices $ map snd ats


partition :: Eq a => [a] -> [a] -> ([a], [a], [a])
partition xs ys = p' xs ys True
  where
    p' xs ys False = ([], xs, ys)
    p' [] ys _     = ([], [], ys)
    p' xs [] _     = ([], xs, [])
    p' xxs@(x:xs) yys@(y:ys) inPrefix
      | inPrefix'   = (x:p, xs', ys')
      | otherwise   = (p, xxs, yys)
      where
        inPrefix' = x == y && inPrefix
        (p, xs', ys') = p' xs ys inPrefix'


findSubstrings' :: String -> SuffixTree -> [Int]
findSubstrings' "" (Leaf i) = [i]
findSubstrings' _  (Leaf _) = []
findSubstrings' s  (Node ats) = concatMap (fs' s) ats
  where
    fs' s (a, t)
      -- s is a prefix of a
      | p == s    = getIndices t
      -- a is a prefix of s
      | p == a    = findSubstrings' s' t
      | otherwise = []
      where
        (p, s', a') = partition s a

------------------------------------------------------

insert :: (String, Int) -> SuffixTree -> SuffixTree
insert (s, n) (Leaf i) = Node [("", Leaf i), (s, Leaf n)]
insert sn (Node ats) = Node (i' sn ats)
  where
    i' :: (String, Int) -> [(String, SuffixTree)] -> [(String, SuffixTree)]
    i' (s, n) [] = [(s, Leaf n)]
    i' sn@(s, n) (at@(a, t) : ats)
      -- no common prefix
      | p == ""    = at : i' sn ats
      | p == a     = (a, insert sn t) : ats
      | otherwise  = (p, Node [(s', Leaf n), (a', t)]) : ats
      where
        (p, s', a') = partition s a

-- This function is given
buildTree :: String -> SuffixTree 
buildTree s
  = foldl (flip insert) (Node []) (zip (suffixes s) [0..])

------------------------------------------------------
-- Part IV

suffixes' :: SuffixTree -> [String]
suffixes' (Leaf _) = []
suffixes' (Node ats) =  concatMap as' ats
  where
    as' (a, t) = a : map (a++) (filter (/= "") (suffixes' t))

prefixes :: String -> [String]
prefixes s = map reverse $ suffixes $ reverse s

allSubstrings :: String -> [String]
allSubstrings s = concatMap prefixes $ suffixes s

-- First try
-- longestRepeatedSubstring :: SuffixTree -> String
-- -- Pre: Tree represents a correct suffix tree for a string
-- longestRepeatedSubstring (Node ats) = longest
--   where
--     s = head [a | (a, t) <- ats, isLeaf t]
--     isLeaf t | Leaf _ <- t = True | otherwise = False

--     ss = allSubstrings s

--     repeats = case nub (ss \\ nub ss) of
--       [] -> ss
--       l  -> l
    
--     longest = foldr1 (\s1 s2 -> if length s1 > length s2 then s1 else s2) repeats


-- chatGPT doesn't work
-- longestRepeatedSubstring :: SuffixTree -> String
-- longestRepeatedSubstring tree = go tree []
--   where
--     go :: SuffixTree -> [String] -> String
--     go (Leaf _) candidates = maximumBy (comparing length) candidates
--     go (Node children) candidates =
--       foldl' (\acc (label, child) -> go child (label:acc)) candidates children

-- longestRepeatedSubstring :: SuffixTree -> String
-- longestRepeatedSubstring t = fst $ lrs t 0 ""
--   where
--     lrs (Leaf _)   n "" = (n,"")
--     lrs (Node ats) l s  = undefined
--       where

-- Basically I copied Tony Field
longestRepeatedSubstring :: SuffixTree -> String
longestRepeatedSubstring = concat . snd  . lrs'
  where
    lrs' :: SuffixTree -> (Int, [String])
    -- lrs' (Leaf _) = (0, [])
    lrs' (Node ats)
      = maximum $ (0, []) : [(length a + n, a:ss) | (a, t@(Node _)) <- ats, let (n, ss) = lrs' t]


------------------------------------------------------
-- Example strings and suffix trees...

s1 :: String
s1 
  = "banana"

s2 :: String
s2 
  = "mississippi"

t1 :: SuffixTree
t1 
  = Node [("banana", Leaf 0), 
          ("a", Node [("na", Node [("na", Leaf 1), 
                                   ("", Leaf 3)]), 
                     ("", Leaf 5)]), 
          ("na", Node [("na", Leaf 2), 
                       ("", Leaf 4)])]

t2 :: SuffixTree
t2 
  = Node [("mississippi", Leaf 0), 
          ("i", Node [("ssi", Node [("ssippi", Leaf 1), 
                                    ("ppi", Leaf 4)]), 
                      ("ppi", Leaf 7), 
                      ("", Leaf 10)]), 
          ("s", Node [("si", Node [("ssippi", Leaf 2), 
                                   ("ppi", Leaf 5)]), 
                      ("i", Node [("ssippi", Leaf 3), 
                                  ("ppi", Leaf 6)])]), 
          ("p", Node [("pi", Leaf 8), 
                      ("i", Leaf 9)])]
