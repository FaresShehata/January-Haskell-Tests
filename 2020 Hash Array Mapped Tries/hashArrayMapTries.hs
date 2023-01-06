module Tries where

import Data.List hiding (insert)
import Data.Bits

import Types
import HashFunctions
import Examples

--------------------------------------------------------------------
-- Part I

-- Use this if you're counting the number of 1s in every
-- four-bit block...
bitTable :: [Int]
bitTable
  = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]

countOnes :: Int -> Int
countOnes n
  | 0 <= n && n <= 15 = bitTable !! n
  | otherwise         = countOnes (shiftR n 4) + countOnes (n .&. (bit 4 - 1))

countOnesFrom :: Int -> Int -> Int
countOnesFrom i n
  = countOnes (n .&. (bit i - 1))

getIndex :: Int -> Int -> Int -> Int
getIndex n i bs
  = (shiftR n (i * bs)) .&. (bit bs - 1)

-- Pre: the index is less than the length of the list
replace :: Int -> [a] -> a -> [a]
replace 0 (x:xs) x'
  = x' : xs
replace i (x:xs) x'
  = x : replace (i - 1) xs x'

-- Pre: the index is less than or equal to the length of the list
insertAt :: Int -> a -> [a] -> [a]
insertAt 0 x' xs 
  = x' : xs
insertAt i x' (x:xs)
  = x : insertAt (i - 1) x' xs

--------------------------------------------------------------------
-- Part II

sumTrie :: (Int -> Int) -> ([Int] -> Int) -> Trie -> Int
sumTrie _ leaf (Leaf ns)
  = leaf ns
sumTrie term leaf (Node bv sns)
 = sum $ map (sumTrie' term leaf) sns
  where
    sumTrie' :: (Int -> Int) -> ([Int] -> Int) -> SubNode -> Int
    sumTrie' term _ (Term n)
      = term n
    sumTrie' term leaf (SubTrie t)
      = sumTrie term leaf t


--
-- If you get the sumTrie function above working you can uncomment
-- these three functions; they may be useful in testing.
--
trieSize :: Trie -> Int
trieSize t
  = sumTrie (const 1) length t

binCount :: Trie -> Int
binCount t
  = sumTrie (const 1) (const 1) t

meanBinSize :: Trie -> Double
meanBinSize t
  = fromIntegral (trieSize t) / fromIntegral (binCount t)


member :: Int -> Hash -> Trie -> Int -> Bool
member v h t bs = member' 0 t
  where
    member' :: Int -> Trie -> Bool
    member' _ (Leaf vs) = v `elem` vs
    member' l (Node bv sns)
      | not $ testBit bv i = False
      | Term v'    <- sn   = v == v'
      | SubTrie t' <- sn   = member' (l + 1) t'
      where
        i = getIndex h l bs
        n = countOnesFrom i bv
        sn = sns !! n


--------------------------------------------------------------------
-- Part III

insert :: HashFun -> Int -> Int -> Int -> Trie -> Trie
insert hf maxDepth bs v t = insert' v 0 t
  where
    insert' :: Int -> Int -> Trie -> Trie
    insert' v _ (Leaf vs)
      = Leaf $ v : filter (/= v) vs
    insert' v l _
      | l >= maxDepth - 1 = Leaf [v]
    insert' v l (Node bv sns)
      | testBit bv i = Node bv (replace n sns (go (sns !! n)))
      | otherwise    = Node (setBit bv i) (insertAt n (Term v) sns)
      where
        i = getIndex (hf v) l bs
        n = countOnesFrom i bv

        go :: SubNode -> SubNode
        go (SubTrie t') = SubTrie $ insert' v (l + 1) t'
        go sn@(Term v')
          | v == v'   = sn
          | otherwise = SubTrie $ insert' v (l + 1) t'
          where
            t' = insert' v' (l + 1) empty

buildTrie :: HashFun -> Int -> Int -> [Int] -> Trie
buildTrie hf maxDepth bs vs
  = foldr (\v t -> insert hf maxDepth bs v t) empty vs
