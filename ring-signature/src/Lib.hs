{-# LANGUAGE MultiWayIf #-}
module Lib where

import Crypto.Number.Basic
import Crypto.Number.F2m
import Crypto.Number.Generate
import Crypto.Number.ModArithmetic
import Crypto.Number.Prime
import Data.Maybe
import Crypto.Hash
import Crypto.Number.Serialize
import qualified Data.ByteString.Char8 as BS
import Data.Char
import Data.List
import Control.Monad
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map


-- p q g
data Group = Group Integer Integer Integer
    deriving (Show, Eq)
-- x
data Private = Private Integer 
    deriving (Show, Eq)    
-- h = g ^ x (mod p) 
data Public = Public Integer 
    deriving (Show, Eq)


type Random = Integer
type Message = Integer
type Sign = (Integer, Map.Map Int Integer, Integer)

genSig :: Group -> Random -> [Random] -> Map.Map Int Public -> 
  Public -> Private -> Message -> Sign 
genSig gk@(Group p q g) u sis pks pk@(Public ypi) sk@(Private xpi) m = sign where 
  -- h = H2(L)
  h = secondH gk (stringBytestring . show $pks)
  -- y_tilde = h ^ xpi  
  ytilde = expSafe h xpi p
  --get the index of ypi in pks
  pi = fst . head . filter (\(x, y) -> y == pk) $Map.assocs pks
  -- compute C_pi+1 
  cpi_plus_one = (pi+1, firstH gk (stringBytestring $show pks ++ 
    concatMap show [ytilde, m, expSafe g u p, expSafe h u p]))
  -- compute the length of public key
  n = Map.size pks
  -- compute the list [pi+1, pi+2, n-1] ++ [0, 1, ... pi-1]
  indices = [(pi+1) .. (n-1)] ++ [0 .. (pi-1)]
  -- for tracking the random numbers because we need to return s0, s1, ... 
  zipsis = Map.fromList . zip indices $sis
  -- computation of rest of c value, seeding cpi_pi+1
  c_pi = Map.fromList . scanl (\(_, ci) i -> (mod (i+1) n, 
    matefirstH gk pks ytilde m h ci (zipsis Map.! i) (pks Map.! i))) 
    cpi_plus_one $indices
  -- compute s_pi, the pi position value and update the Map 
  sisupd = Map.insert pi (mod (u - xpi * c_pi Map.! pi) q) zipsis
  -- return the signature
  sign = (c_pi Map.! 0, sisupd, ytilde)


verifySign :: Group -> Map.Map Int Public -> Sign -> Message -> Bool
verifySign gk@(Group p q g) pks sign@(c0, sis, ytilde) m = ret == c0 where
  -- h = H2(L)
  h = secondH gk (stringBytestring . show $pks)
  -- compute size
  n = Map.size pks
  -- fold over a list [0 .. (n-1)]
  ret = foldl (\ci i -> matefirstH gk pks ytilde m h ci (sis Map.! i) 
    (pks Map.! i)) c0 [0..(n-1)]


matefirstH :: Group -> Map.Map Int Public -> Integer -> Integer -> 
  Integer -> Integer -> Integer -> Public -> Integer
matefirstH gk@(Group p q g) pks yt m h ci si (Public yi) = 
  firstH gk (stringBytestring $(show pks) ++ 
    (concatMap show [yt, m, mod (expSafe g si p * expSafe yi ci p) p, 
      mod (expSafe h si p * expSafe yt ci p) p]))
    

-- https://eprint.iacr.org/2004/027.pdf
-- https://crypto.stackexchange.com/questions/39877/what-is-a-cyclic-group-of-prime-order-q-such-that-the-dlp-is-hard
firstH :: Group -> BS.ByteString -> Integer
firstH (Group _ q _) xs = mod (os2ip . hashWith SHA256 $xs) q 

--https://u.cs.biu.ac.il/~lindell/89-656/group%20example.pdf
secondH :: Group -> BS.ByteString -> Integer
secondH (Group p q _) xs = mod (ret * ret) p where
    ret = mod (os2ip . hashWith SHA256 $xs) q -- prove it if we replace it by p then it will 
    -- still have the same behaviour
    -- (nub . sort  $ map (\x -> mod (x * x) 839) [1..419]) == 
    -- (nub . sort  $ map (\x -> mod (x * x) 839) [1..838])

stringBytestring :: String -> BS.ByteString
stringBytestring = BS.pack

      
{- return p and q such that p = 2 * q + 1-}
generatePrime :: Int -> IO (Integer, Integer)     
generatePrime bitLength  = do 
   p <- generateSafePrime bitLength
   let q = div (p - 1) 2
   return (p, q)

--http://cacr.uwaterloo.ca/hac/about/chap11.pdf#page=29
--https://github.com/mukeshtiwari/verified-counting/blob/main/Elgamal.v#L59
groupGenerator :: Integer -> Integer -> IO Group
groupGenerator p q = 
  generateBetween 1 (p - 1) >>= \genCand ->
  if | and [expSafe genCand q p == 1, expSafe genCand 2 p /= 1] ->  return (Group p q genCand)   
     | otherwise ->  groupGenerator p q 

generateKey :: Group -> IO (Public, Private)
generateKey gk@(Group p q g) = do
    x <- generateMax q
    let 
        pk = Public (expSafe g x p)
        sk = Private x
    return (pk, sk)


test = do
  (p, q) <- Lib.generatePrime 100
  gk <- groupGenerator p q
  (pk, sk) <- generateKey gk
  k1 <- generateBetween 1 10 
  k2 <- generateBetween 1 10
  m <- generateBetween 1 q
  left <- replicateM  (fromInteger k1) (generateKey gk)
  right <- replicateM (fromInteger k2) (generateKey gk)
  u <- generateBetween 1 q
  sis <- replicateM (fromInteger $k1 + k2) (generateBetween 1 q)
  let pks = map fst (left ++ (pk, sk) : right)
      sign = genSig gk u sis (Map.fromList (zip [0..] pks)) pk sk m
      veri = verifySign gk (Map.fromList (zip [0..] pks)) sign m
  return veri      