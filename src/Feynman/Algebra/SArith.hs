{-# LANGUAGE TypeFamilies #-}

{-|
Module      : SArith
Description : Symbolic integer arithmetic
Stability   : experimental
Portability : portable
-}

module Feynman.Algebra.SArith where

import Data.Maybe (isJust, fromJust)
import Data.Bits
import Data.List (unfoldr)
import Data.Word

import Control.Monad

import Test.QuickCheck hiding ((.&.))
import Test.QuickCheck.Property ((==>))

import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial
import Feynman.Algebra.Polynomial.Multilinear

{---------------------------
 Core types
 ----------------------------}

-- | Symbolic (bit-blasted) uintegers. The lowest-order bit is the first bit
type SInt v = [SBool v]

{---------------------------
 Utilities
 ----------------------------}

-- | Returns the width of an SInt
getWidth :: SInt v -> Int
getWidth = length

-- | Truncates or extends a symbolic uint to /n/ bits
setWidth :: MVar v => SInt v -> Int -> SInt v
setWidth sa n = take n sa ++ (replicate (n - length sa) (0))

-- | Unifies the length of two symbolic integers
unifyWidth :: MVar v => SInt v -> SInt v -> (SInt v, SInt v)
unifyWidth s t = (setWidth s n, setWidth t n) where
  n = max (getWidth s) (getWidth t)

-- | Turns a list of Booleans into an SInt
asSUInt :: MVar v => [SBool v] -> SInt v
asSUInt xs = xs ++ [0]

-- | Turns an integer into a symbolic int[n]
makeSInt :: MVar v => Integer -> Int -> SInt v
makeSInt i n = setWidth (makeSNat i) n

-- | Turns a positive integer into a symbolic int of arbitrary length
makeSNat :: MVar v => Integer -> SInt v
makeSNat i
  | i == 0    = [0,0]
  | i < 0     = sNeg $ go (-i)
  | otherwise = go i
  where go 0  = [0]
        go i  = case i `mod` 2 of
          0 -> 0:go (i `shiftR` 1)
          1 -> 1:go (i `shiftR` 1)

-- | Converts a constant bit-blasted integer back to an integer
toNat :: MVar v => SInt v -> Maybe Integer
toNat si = liftM (bitsToInt) $ mapM takeConstant si where
  takeConstant p = case isConstant p of
    True  -> Just $ getConstant p
    False -> Nothing

  bitsToInt :: [FF2] -> Integer
  bitsToInt bits = foldr (+) 0 $ [if testFF2 b then 1 `shiftL` i else 0 | (i,b) <- zip [0..] bits]

-- | Checks whether a symbolic uint is a constant value
isNat :: MVar v => SInt v -> Bool
isNat = isJust . toNat

-- | Forces a symbolic uint to a Nat. Throws an error if it is symbolic
forceNat :: MVar v => SInt v -> Integer
forceNat = fromJust . toNat

-- | If-then-else
ite :: MVar v => SBool v -> SInt v -> SInt v -> SInt v
ite p a b = go $ unifyWidth a b where
  go (a,b) = zipWith (\a b -> p*a + (1 + p)*b) a b

{---------------------------
 Bitwise operators

 And, Or, Xor, Negate, LShift, RShift, LRot, RRot, Popcount
 ----------------------------}

-- | Bitwise AND
sAnd :: MVar v => SInt v -> SInt v -> SInt v
sAnd s t = go $ unifyWidth s t where
  go (s, t) = zipWith (*) s (t ++ repeat 0)

-- | Bitwise XOR
sXor :: MVar v => SInt v -> SInt v -> SInt v
sXor s t = go $ unifyWidth s t where
  go (s, t) = zipWith (+) s (t ++ repeat 0)

-- | Bitwise NOT
sNot :: MVar v => SInt v -> SInt v
sNot = map (1+)

-- | Bitwise OR
sOr :: MVar v => SInt v -> SInt v -> SInt v
sOr s t = sNot $ (sNot s) `sAnd` (sNot t)

-- | Bitshift left (toward higher place bits)
sLShift :: MVar v => SInt v -> SInt v -> SInt v
sLShift x = foldr go x . zip [0..] where
  go (i,bit) x = ite bit (replicate (1 `shiftL` i) 0 ++ x) x

-- | Bitshift right (toward lower place bits)
sRShift :: MVar v => SInt v -> SInt v -> SInt v
sRShift x = foldr go x . zip [0..] where
  go (i,bit) x = ite bit (drop (1 `shiftL` i) x ++ [0]) x

sLRot :: MVar v => SInt v -> SInt v -> SInt v
sLRot x y = (foldr go x $ zip [1 `shiftL` i | i <- [0..]] y) where
  go (i,bit) x = ite bit (drop (n-i) x ++ take (n-i) x) x
  n  = getWidth x

sRRot :: MVar v => SInt v -> SInt v -> SInt v
sRRot x y = (foldr go x $ zip [1 `shiftL` i | i <- [0..]] y) where
  go (i,bit) x = ite bit (drop i x ++ take i x) x
  n  = length x

sPopcount :: MVar v => SInt v -> SInt v
sPopcount s = foldl sPlus (replicate (length s) 0) $ map (\a -> [a,0]) $ s

{---------------------------
 Arithmetic operators

 Plus, Minus, Neg, Times, Div, Mod, Pow
 ----------------------------}

-- | plus(x, y)[i] = x[i] + y[i] + c[i-1]
--            c[i] = x[i] y[i] + (x[i] + y[i]) c[i-1]
--   cast to size of first arg
sPlus :: MVar v => SInt v -> SInt v -> SInt v
sPlus s t = go 0 $ extend $ unifyWidth s t where
  go c ([], [])         = []
  go c (x:xs, y:ys) =
    (c + x + y):(go (x*y + x*c + y*c) (xs, ys))

  extend (s,t) = (setWidth s (n+1), setWidth t (n+1)) where n = getWidth s

-- | Negating a number mod 2^n using 2's complement
sNeg :: MVar v => SInt v -> SInt v
sNeg s = setWidth (sPlus (makeSNat 1) (sNot s)) (getWidth s)

-- | Subtraction mod 2^n
sMinus :: MVar v => SInt v -> SInt v -> SInt v
sMinus s t = sPlus s' (sNeg t') where
  (s',t') = unifyWidth s t

-- | Multiplication mod 2^n
sMult :: MVar v => SInt v -> SInt v -> SInt v
sMult s t = foldr (\a -> (flip setWidth) (2*n) . sPlus a) (makeSNat 0) $ shifts where
  n  = max (getWidth s) (getWidth t)
  s' = setWidth s (2*n)
  t' = setWidth t (2*n)
  shift i p = take (2*n) $ replicate i 0 ++ (map (*p) t')
  shifts    = [shift i p |  (i,p) <- zip [0..] s']

-- | Division mod 2^n. Performs binary long division
sDiv :: MVar v => SInt v -> SInt v -> (SInt v, SInt v)
sDiv s t | all (== 0) t = error "Divide by 0"
         | otherwise    = go ([], makeSNat 0) (n-1) where
             n             = getWidth s
             go (q,r) (-1) = (q,r)
             go (q,r) i    =
               let r' = (s!!i):(setWidth r (n-1)) in
                 go ((sGEq r' t):q, ite (sGEq r' t) (sMinus r' t) r') (i-1)

-- | Quotient mod 2^n
sQuot :: MVar v => SInt v -> SInt v -> SInt v
sQuot s t = res where
  res     = setWidth (fst $ sDiv s' t') n
  (s',t') = unifyWidth s t
  n       = getWidth s'

-- | Quotient mod 2^n
sMod :: MVar v => SInt v -> SInt v -> SInt v
sMod s t = res where
  res     = setWidth (snd $ sDiv s' t') n
  (s',t') = unifyWidth s t
  n       = getWidth s'

-- | Power mod 2^n
sPow :: MVar v => SInt v -> SInt v -> SInt v
sPow s t = foldr sMult (makeSNat 1) powers where
  powers  = map (\(s,t) -> ite t s (makeSNat 1)) $ zip squares t
  squares = [s] ++ [sMult x x | x <- squares]

-- | Singular reduction of an integer mod M. Useful for windowed
--   modular arithmetic when you know i is in the range [0..k*M]
--
--   If /s/ >= /t/, then s - t else s
sMod1 :: MVar v => SInt v -> SInt v -> SInt v
sMod1 s t = ite (sGEq s t) (sMinus s t) s

{---------------------------
 Comparison operators

 <, <=, ==, >, >=
 ----------------------------}


{-
  a3 a2 a1 a0
  b3 b2 b1 b0

  a < b ==> (a3 < b3) xor ( (a3 == b3) and [a0, a1, a2] < [b0, b1, b2] )
  truncates second argument
-}
compByIndex :: MVar v => (SBool v -> SBool v -> SBool v) -> SInt v -> SInt v -> SBool v
compByIndex f s t = go . rev $ unifyWidth s t
  where
    rev (s,t) = (reverse s, reverse t)
    go ([a], [b])   = f a b
    go (a:as, b:bs) = f a b + (iff a b * go (as, bs))
    iff p q         = 1 + p + q

sLT :: MVar v => SInt v -> SInt v -> SBool v 
sLT a b = compByIndex lt a b
  where lt p q = (1+p)*q

sGT :: MVar v => SInt v -> SInt v -> SBool v 
sGT a b = compByIndex gt a b
  where gt p q = p*(1+q)

sLEq :: MVar v => SInt v -> SInt v -> SBool v 
sLEq s t = 1 + sGT s t

sGEq :: MVar v => SInt v -> SInt v -> SBool v 
sGEq s t = 1 + sLT s t

sEq :: MVar v => SInt v -> SInt v -> SBool v
sEq s t = go $ unifyWidth s t where
  go (s, t) = foldl (*) 1 $ zipWith iff s (t ++ repeat 0)
  iff p q               = 1 + p + q

sNEq :: MVar v => SInt v -> SInt v -> SBool v
sNEq s t = 1 + sEq s t

{---------------------------
 Testing
 ----------------------------}

-- Convenience definitions for testing
liftWord :: Word8 -> SInt String
liftWord i = makeSInt (fromIntegral i) 8

forceWord :: SInt String -> Word8
forceWord = fromIntegral . forceNat

forceBool :: SBool String -> Bool
forceBool = testFF2 . getConstant

-- dropSymbolic . liftSymbolic is the identity
prop_SInt_faithful a = (a >= 0) ==> a == (forceWord . liftWord $ a)

-- Plus commutes with liftSymbolic
prop_sAnd_correct a b = (a >= 0) && (b >= 0) ==>
  forceWord (sAnd (liftWord a) (liftWord b)) == a .&. b

prop_sXor_correct a b = (a >= 0) && (b >= 0) ==>
  forceWord (sXor (liftWord a) (liftWord b)) == a `xor` b

prop_sOr_correct a b = (a >= 0) && (b >= 0) ==>
  forceWord (sOr (liftWord a) (liftWord b)) == a .|. b

-- fails for a=0
prop_sNot_correct a = (a >= 0) ==>
  forceWord (sNot (liftWord a)) == complement a

prop_sLShift_correct a b = (a >= 0) && (b >= 0) ==>
  forceWord (sLShift (liftWord a) (liftWord b)) == a `shiftL` (fromIntegral b)

prop_sRShift_correct a b = (a >= 0) && (b >= 0) ==>
  forceWord (sRShift (liftWord a) (liftWord b)) == a `shiftR` (fromIntegral b)

prop_sLRot_correct a b = (a >= 0) && (b >= 0) ==>
  forceWord (sLRot (liftWord a) (liftWord b)) == a `rotateL` (fromIntegral b)

prop_sRRot_correct a b = (a >= 0) && (b >= 0) ==>
  forceWord (sRRot (liftWord a) (liftWord b)) == a `rotateR` (fromIntegral b)

prop_sPopcount_correct a = (a >= 0) ==>
  forceWord (sPopcount (liftWord a)) == fromIntegral (popCount a)

prop_sPlus_correct a b = (a >= 0) && (b >= 0) ==>
  forceWord (sPlus (liftWord a) (liftWord b)) == a + b

prop_sNeg_correct a = (a >= 0) ==>
  forceWord (sNeg (liftWord a)) == (-a)

prop_sMinus_correct a b = (a >= 0) && (b >= 0) ==>
  forceWord (sMinus (liftWord a) (liftWord b)) == a - b

prop_sMult_correct a b = (a >= 0) && (b >= 0) ==>
  forceWord (sMult (liftWord a) (liftWord b)) == a * b

prop_sQuot_correct a b = (a >= 0) && (b > 0) ==>
  forceWord (sQuot (liftWord a) (liftWord b)) == a `quot` b

prop_sMod_correct a b = (a >= 0) && (b > 0) ==>
  forceWord (sMod (liftWord a) (liftWord b)) == a `mod` b

prop_sPow_correct a b = (a >= 0) && (b >= 0) ==>
  forceWord (sPow (liftWord a) (liftWord b)) == a ^ b

prop_sLT_correct a b = (a >= 0) && (b >= 0) ==>
  forceBool (sLT (liftWord a) (liftWord b)) == (a < b)

prop_sLEq_correct a b = (a >= 0) && (b >= 0) ==>
  forceBool (sLEq (liftWord a) (liftWord b)) == (a <= b)

prop_sGT_correct a b = (a >= 0) && (b >= 0) ==>
  forceBool (sGT (liftWord a) (liftWord b)) == (a > b)

prop_sGEq_correct a b = (a >= 0) && (b >= 0) ==>
  forceBool (sGEq (liftWord a) (liftWord b)) == (a >= b)

prop_sEq_correct a b = (a >= 0) && (b >= 0) ==>
  forceBool (sEq (liftWord a) (liftWord b)) == (a == b)

tests :: () -> IO ()
tests _ = do
  quickCheck $ prop_SInt_faithful
  quickCheck $ prop_sXor_correct
  quickCheck $ prop_sAnd_correct
  quickCheck $ prop_sOr_correct
  quickCheck $ prop_sNot_correct
  quickCheck $ prop_sLShift_correct
  quickCheck $ prop_sRShift_correct
  quickCheck $ prop_sLRot_correct 
  quickCheck $ prop_sRRot_correct
  quickCheck $ prop_sPopcount_correct
  quickCheck $ prop_sPlus_correct
  quickCheck $ prop_sNeg_correct
  quickCheck $ prop_sMinus_correct
  quickCheck $ prop_sMult_correct
  quickCheck $ prop_sQuot_correct
  quickCheck $ prop_sMod_correct
  --quickCheck $ prop_sPow_correct
  quickCheck $ prop_sLT_correct
  quickCheck $ prop_sLEq_correct
  quickCheck $ prop_sGT_correct
  quickCheck $ prop_sGEq_correct
  quickCheck $ prop_sEq_correct
