{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

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

import Control.Monad (liftM)

import Test.QuickCheck hiding ((.&.))
import Test.QuickCheck.Property ((==>))

import Feynman.Algebra.Base
import Feynman.Algebra.Polynomial
import Feynman.Algebra.Polynomial.Multilinear

{---------------------------
 Core types
 ----------------------------}

data Signed
data Unsigned

-- | Symbolic bit-blasted integers. Lowest-order bit is the first bit.
--   Signed integers are represents via 2's complement with the most significant
--   bit as the sign bit
newtype SBits sign v = SBits { unWrap :: [SBool v] } deriving (Eq,Show)

type SUInt v = SBits Unsigned v
type SInt  v = SBits Signed v

{---------------------------
 Utilities
 ----------------------------}

-- | Type class for things with a (symbolic) sign
class MVar v => SignBit a v | a -> v where
  getSign :: a -> SBool v

instance MVar v => SignBit (SUInt v) v where
  getSign _ = 0

instance MVar v => SignBit (SInt v) v where
  getSign (SBits xs)
    | length xs == 0 = 0
    | otherwise      = head $ reverse xs

{-
-- | Type class for overloading setWidth
class Extendable a where
  setWidth :: SBits a v -> Int -> SBits a v

instance Extendable Unsigned where
  setWidth (SBits xs) n = SBits $ take n xs ++ (replicate (n - length xs) 0)

instance Extendable Signed where
  setWidth (SBits xs) n = SBits $ take n xs ++ (replicate (n - length xs) sgn)
    where sgn | length xs == 0 = 0
              | otherwise      = head $ reverse xs
-}  

-- | Returns the width of a symbolic int
getWidth :: SBits sign v -> Int
getWidth = length . unWrap

-- | Sets the width of a symbolic int
setWidth :: SignBit (SBits a v) v => SBits a v -> Int -> SBits a v
setWidth b@(SBits xs) n = SBits $ take n xs ++ (replicate (n - length xs) (getSign b))

-- | Unifies the length of two symbolic integers
unifyWidth :: SignBit (SBits a v) v => SBits a v -> SBits a v -> (SBits a v, SBits a v)
unifyWidth s t = (setWidth s n, setWidth t n) where
  n = max (getWidth s) (getWidth t)

-- | Turns an arbitrary integer into a symbolic integer in signed or unsigned representation
--
--   The number of bits returned is always lg i + 1. That is, whether the number is positive
--   or negative it's returned in 2's complement, which is then either interpreted
--   uniquely as i or i `mod` lg i + 1
makeSymbolic :: MVar v => Integer -> SBits sign v
makeSymbolic i
  | i < 0     = sNeg . SBits $ go (-i)
  | otherwise = SBits $ go i
  where go 0  = [0]
        go i  = case i `mod` 2 of
          0 -> 0:go (i `shiftR` 1)
          1 -> 1:go (i `shiftR` 1)

-- | Turns an arbitrary integer into a symbolic int
makeSInt :: MVar v => Integer -> SInt v
makeSInt = makeSymbolic

-- | Turns a positive integer into a symbolic uint of arbitrary length
makeSUInt :: MVar v => Integer -> SUInt v
makeSUInt = makeSymbolic

-- | Converts between signed and unsigned representations
convertSign :: SBits s v -> SBits t v
convertSign = SBits . unWrap

-- | Converts a constant bit-blasted integer back to an integer
fromSymbolic :: SignBit (SBits a v) v => SBits a v -> Maybe Integer
fromSymbolic i@(SBits xs) = liftM (shiftSign . bitsToInt) $ mapM takeConstant xs where
  takeConstant p = case isConstant p of
    True  -> Just $ getConstant p
    False -> Nothing

  bitsToInt :: [FF2] -> Integer
  bitsToInt bits = foldr (+) 0 $ [if testFF2 b then 1 `shiftL` i else 0 | (i,b) <- zip [0..] bits]

  shiftSign :: Integer -> Integer
  shiftSign res = if getSign i /= 0 then res - (1 `shiftL` (length xs)) else res

-- | Checks whether a symbolic integer is a constant value
isInteger :: SignBit (SBits a v) v => SBits a v -> Bool
isInteger = isJust . fromSymbolic

-- | Forces a symbolic uint to a Nat. Throws an error if it is symbolic
forceInteger :: SignBit (SBits a v) v => SBits a v -> Integer
forceInteger = fromJust . fromSymbolic

-- | Given x:uint[n], generates the list of indicator polynomials:
--    [x==0, x==1, x==2, ..., x==2^n-1]
indicators :: MVar v => SBits a v -> [SBool v]
indicators (SBits xs) = f $ reverse xs
  where
    f [p]    = [1 + p, p]
    f (p:ps) = map ((1+p)*) (f ps) ++ map (p*) (f ps)

-- | Given f, s:uint[m], t:uint[n], outputs
--    {t==0}s + {t==1}f(s) + ... + {t==i}f^i(s)[i] + ... + {t==2^n-1}(...)
--    in other words, takes the dot product of the list of indicator polynomials with the list [f^i(s)]
--    then sums over each index 
indicatorSum :: MVar v => (SBits a v -> SBits a v) -> SBits a v -> SBits a v -> SBits a v
indicatorSum f s t = SBits $ foldr (zipWith (+)) (repeat 0) ind where
  ind = zipWith (\l ind -> map (ind*) l) (map unWrap $ iterate f s) (indicators t)

-- | If-then-else
ite :: SignBit (SBits a v) v => SBool v -> SBits a v -> SBits a v -> SBits a v
ite p a b = go $ unifyWidth a b where
  go (a,b) = SBits $ zipWith (\a b -> p*a + (1 + p)*b) (unWrap a) (unWrap b)

{---------------------------
 Bitwise operators

 And, Or, Xor, Negate, LShift, RShift, LRot, RRot, Popcount
 ----------------------------}

-- | Bitwise AND
sAnd :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sAnd s t = go $ unifyWidth s t where
  go (SBits s, SBits t) = SBits $ zipWith (*) s (t ++ repeat 0)

-- | Bitwise XOR
sXor :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sXor s t = go $ unifyWidth s t where
  go (SBits s, SBits t) = SBits $ zipWith (+) s (t ++ repeat 0)

-- | Bitwise NOT
sNot :: MVar v => SBits a v -> SBits a v
sNot = SBits . map (1+) . unWrap

-- | Bitwise OR
sOr :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sOr s t = sNot $ (sNot s) `sAnd` (sNot t)

-- | Bitshift left (toward higher place bits)
sLShift :: MVar v => SBits a v -> SBits a v -> SBits a v
sLShift = indicatorSum (SBits . lshift . unWrap)
  where
    lshift x = 0 : x

-- | Bitshift right (toward lower place bits)
sRShift :: MVar v => SBits a v -> SBits a v -> SBits a v
sRShift = indicatorSum (SBits . rshift . unWrap)
  where
    rshift (_:x) = x ++ [0]

-- | Cyclic rotation left (toward higher place bits)
sLRot :: MVar v => SBits a v -> SBits a v -> SBits a v
sLRot = indicatorSum (SBits . lrot . unWrap)
  where
    lrot x = last x : init x

-- | Cyclic rotation right (toward higher place bits)
sRRot :: MVar v => SBits a v -> SBits a v -> SBits a v
sRRot = indicatorSum (SBits . rrot . unWrap)
  where
    rrot (a:x) = x ++ [a]

-- | Hamming weight
sPopcount :: MVar v => SBits a v -> SBits a v
sPopcount (SBits s) = foldl sPlus (SBits $ replicate (length s) 0) $ map (\a -> SBits [a]) $ s

{---------------------------
 Arithmetic operators

 Plus, Minus, Neg, Times, Div, Mod, Pow
 ----------------------------}

-- | plus(x, y)[i] = x[i] + y[i] + c[i-1]
--            c[i] = x[i] y[i] + (x[i] + y[i]) c[i-1]
--   cast to size of first arg
sPlus :: MVar v => SBits a v -> SBits a v -> SBits a v
sPlus (SBits s) (SBits t) = SBits $ unfoldr computePair (0, s, t) where

  computePair (0, []  , [])   = Nothing
  computePair (c, []  , [])   = Just (c, (0, [], []))
  computePair (c, x:xs, [])   = Just (c + x, (x*c, xs, []))
  computePair (c, []  , y:ys) = Just (c + y, (y*c, [], ys))
  computePair (c, x:xs, y:ys) = Just (c + x + y, (x * y + (x + y)*c, xs, ys))

-- | Negating a number mod 2^n using 2's complement
sNeg :: MVar v => SBits a v -> SBits a v
sNeg s = sPlus (makeSymbolic 1) (sNot s)

-- | Subtraction mod 2^n
sMinus :: MVar v => SBits a v -> SBits a v -> SBits a v
sMinus s t = sPlus s (sNeg t)

-- | Multiplication mod 2^n
sMult :: MVar v => SBits a v -> SBits a v -> SBits a v
sMult s t = foldr sPlus (makeSymbolic 0) $ shifts where
  shifts = [SBits $ replicate i 0 ++ map (*p) (unWrap t) | (i,p) <- zip [0..] (unWrap s)]

-- | Division mod 2^n. Performs binary long division
sDiv :: SignBit (SBits a v) v => SBits a v -> SBits a v -> (SBits a v, SBits a v)
sDiv s t | t == makeSymbolic 0 = error "Divide by 0"
         | otherwise           = go (SBits [], makeSymbolic 0) (n-1) where
             n             = getWidth s
             go (q,r) (-1) = (q,r)
             go (q,r) i    =
               let r' = SBits $ ((unWrap s)!!i):(unWrap $ setWidth r (n-1)) in
                 go (SBits $ (sGEq r' t):(unWrap q), ite (sGEq r' t) (sMinus r' t) r') (i-1)

-- | Quotient mod 2^n
sQuot :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sQuot s t = fst $ sDiv s t

-- | Quotient mod 2^n
sMod :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sMod s t = snd $ sDiv s t

-- | Power mod 2^n
sPow :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sPow s t = foldr sMult (makeSymbolic 1) powers where
  powers  = map (\(s,t) -> ite t s (makeSymbolic 1)) $ zip squares (unWrap t)
  squares = [s] ++ [sMult x x | x <- squares]

-- | Singular reduction of an integer mod M. Useful for windowed
--   modular arithmetic when you know i is in the range [0..k*M]
--
--   If /s/ >= /t/, then s - t else s
sMod1 :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sMod1 s t = ite (sGEq s t) (sMinus s t) s

{---------------------------
 Comparison operators

 <, <=, ==, >, >=
 ----------------------------}

-- | Applies a comparison operator by index
--
--   
--   a3 a2 a1 a0
--   b3 b2 b1 b0
--
--   a < b ==> (a3 < b3) xor ( (a3 == b3) and [a0, a1, a2] < [b0, b1, b2] )
compByIndex :: SignBit (SBits a v) v => (SBool v -> SBool v -> SBool v)
                                     -> SBits a v -> SBits a v -> SBool v
compByIndex f s t = go . (\(s,t) -> (reverse . unWrap $ s, reverse . unWrap $ t)) $ unifyWidth s t
  where
    go ([a], [b])   = f a b
    go (a:as, b:bs) = f a b + (iff a b * go (as, bs))
    iff p q         = 1 + p + q

-- | Less than
sLT :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBool v 
sLT = compByIndex lt
  where
    lt p q = (1+p)*q

-- | Greater than
sGT :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBool v 
sGT = compByIndex gt
  where
    gt p q = p*(1+q)

-- | Less than or equal
sLEq :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBool v 
sLEq s t = 1 + sGT s t

-- | Greater than or equal
sGEq :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBool v 
sGEq s t = 1 + sLT s t

-- | Equals
sEq :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBool v
sEq s t = go $ unifyWidth s t where
  go (SBits s, SBits t) = foldl (*) 1 $ zipWith iff s (t ++ repeat 0)
  iff p q               = 1 + p + q

{---------------------------
 Testing
 ----------------------------}

-- Convenience definitions for testing
{-
liftWord :: Word8 -> SUInt String
liftWord i = setWidth (makeSymbolic (fromIntegral i)) 8

forceWord :: SUInt String -> Word8
forceWord = fromIntegral . forceInteger . (flip setWidth) 8

forceBool :: SBool String -> Bool
forceBool = testFF2 . getConstant
-}

liftWord :: Int -> SInt String
liftWord = makeSymbolic . fromIntegral

forceWord :: SInt String -> Int
forceWord = fromIntegral . forceInteger

forceBool :: SBool String -> Bool
forceBool = testFF2 . getConstant

liftInt :: Integer -> SInt String
liftInt = makeSymbolic

-- dropSymbolic . liftSymbolic is the identity
prop_SUInt_faithful a = (a >= 0) ==> a == (forceWord . liftWord $ a)

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
  quickCheck $ prop_SUInt_faithful
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
  quickCheck $ prop_sPow_correct
  quickCheck $ prop_sLT_correct
  quickCheck $ prop_sLEq_correct
  quickCheck $ prop_sGT_correct
  quickCheck $ prop_sGEq_correct
  quickCheck $ prop_sEq_correct
