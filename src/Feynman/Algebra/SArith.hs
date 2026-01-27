{-# LANGUAGE UndecidableInstances #-}
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

instance SignBit (SBits sign v) v => Num (SBits sign v) where
  (+) = sPlus
  (*) = sMult
  negate = sNeg
  abs = sAbs
  signum = SBits . (:[]) . getSign
  fromInteger = makeSymbolic

instance SignBit (SBits sign v) v => Bits (SBits sign v) where
  (.&.) = sAnd
  (.|.) = sOr
  xor   = sXor
  complement = sNot
  shift a b = case b > 0 of
    True -> sLShift a (makeSymbolic $ toInteger b)
    True -> sRShift a (makeSymbolic $ toInteger (-b))
  rotate a b = case b > 0 of
    True -> sLRot a (makeSymbolic $ toInteger b)
    True -> sRRot a (makeSymbolic $ toInteger (-b))
  bitSize = getWidth
  bitSizeMaybe = Just . bitSize
  isSigned = isSign
  testBit = error "Unimplemented"
  bit     = error "Unimplemented"

{---------------------------
 Utilities
 ----------------------------}

-- | Type class for things with a (symbolic) sign
class MVar v => SignBit a v | a -> v where
  isSign  :: a -> Bool
  getSign ::  a -> SBool v
  setSign ::  SBool v -> a -> a

instance MVar v => SignBit (SUInt v) v where
  isSign  _ = False
  getSign _ = 0
  setSign _ = id

instance MVar v => SignBit (SInt v) v where
  isSign  _ = True
  getSign (SBits xs)
    | length xs == 0 = 0
    | otherwise      = head $ reverse xs
  setSign s (SBits xs)
    | length xs == 0 = SBits []
    | otherwise      = SBits . reverse $ s:(tail $ reverse xs)

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
makeSymbolic :: SignBit (SBits sign v) v => Integer -> SBits sign v
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
  ind = zipWith (\l ind -> map (ind*) l) (map unWrap $ iterate f s) (indicators t ++ repeat 0)

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
sNot :: SignBit (SBits a v) v => SBits a v -> SBits a v
sNot = SBits . map (1+) . unWrap

-- | Bitwise OR
sOr :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sOr s t = sNot $ (sNot s) `sAnd` (sNot t)

-- | Bitshift left (toward higher place bits)
sLShift :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sLShift x = foldr go x . zip [0..] . unWrap where
  go (i,bit) x = ite bit (SBits $ replicate (1 `shiftL` i) 0 ++ (unWrap x)) x

-- | Bitshift right (toward lower place bits)
sRShift :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sRShift x = foldr go x . zip [0..] . unWrap where
  go (i,bit) x = ite bit (SBits $ drop (1 `shiftL` i) (unWrap x) ++ [getSign x]) x

-- | Cyclic rotation left (toward higher place bits)
sLRot :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sLRot x = foldr go x . zip [1 `shiftL` i | i <- [0..]] . unWrap where
  go (i,bit) x@(SBits b) = ite bit (SBits $ drop (n-i) b ++ take (n-i) b) x
  n = getWidth x

-- | Cyclic rotation right (toward higher place bits)
sRRot :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sRRot x = foldr go x . zip [1 `shiftL` i | i <- [0..]] . unWrap where
  go (i,bit) x@(SBits b) = ite bit (SBits $ drop i b ++ take i b) x
  n = getWidth x

-- | Hamming weight
sPopcount :: SignBit (SBits a v) v => SBits a v -> SBits a v
sPopcount (SBits s) = foldl sPlus (SBits $ replicate (length s) 0) $ map (\a -> SBits [a]) $ s

{---------------------------
 Arithmetic operators

 Plus, Minus, Neg, Abs, Times, Div, Mod, Pow
 ----------------------------}

-- | plus(x, y)[i] = x[i] + y[i] + c[i-1]
--            c[i] = x[i] y[i] + (x[i] + y[i]) c[i-1]
--   cast to size of first arg
sPlus :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sPlus s t = SBits $ go 0 $ extend $ unifyWidth s t where
  go c (SBits [], SBits [])         = []
  go c (SBits (x:xs), SBits (y:ys)) =
    (c + x + y):(go (x*y + x*c + y*c) (SBits xs, SBits ys))

  extend (s,t) = (setWidth s (n+1), setWidth t (n+1)) where n = getWidth s
  
-- | Negating a number mod 2^n using 2's complement
sNeg :: SignBit (SBits a v) v => SBits a v -> SBits a v
sNeg s = setWidth (sPlus (makeSymbolic 1) (sNot s)) (getWidth s)

-- | Absolute value of a number
sAbs :: SignBit (SBits a v) v => SBits a v -> SBits a v
sAbs s = ite (getSign s) (sNeg s) s

-- | Subtraction mod 2^n
sMinus :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sMinus s t = sPlus s (sNeg t)

-- | Multiplication mod 2^n
sMult :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sMult s t = foldr (\a -> (flip setWidth) (2*n) . sPlus a) (makeSymbolic 0) $ shifts where
  n  = max (getWidth s) (getWidth t)
  s' = setWidth s (2*n)
  t' = setWidth t (2*n)
  shift i p = take (2*n) $ replicate i 0 ++ (map (*p) (unWrap t'))
  shifts    = [SBits $ shift i p |  (i,p) <- zip [0..] (unWrap s')]

-- | Division mod 2^n. Performs (unsigned) binary long division
sDiv :: SignBit (SBits a v) v => SBits a v -> SBits a v -> (SBits a v, SBits a v)
sDiv s t | all (== 0) (unWrap t) = error "Divide by 0"
         | otherwise             = go (SBits [], makeSymbolic 0) (n-1) where
             n             = getWidth s
             go (q,r) (-1) = (q,r)
             go (q,r) i    =
               let r' = SBits $ ((unWrap s)!!i):(unWrap $ setWidth r (n-1)) in
                 go (SBits $ (sGEq r' t):(unWrap q), ite (sGEq r' t) (sMinus r' t) r') (i-1)

-- | Quotient mod 2^n
sQuot :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sQuot s t = ite (getSign s' + getSign t') (sNeg res) res where
  res     = setWidth (fst $ sDiv (sAbs s') (sAbs t')) n
  (s',t') = unifyWidth s t
  n       = getWidth s'

-- | Remainder mod 2^n
sMod :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sMod s t = ite (getSign t') (sNeg res) res where
  res     = setWidth (snd $ sDiv (sAbs s') (sAbs t')) n
  (s',t') = unifyWidth s t
  n       = getWidth s'

-- | Power mod 2^n
sPow :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sPow s t = foldr sMult (makeSymbolic 1) powers where
  powers  = map (\(s,t) -> ite t s (makeSymbolic 1)) $ zip squares (unWrap t)
  squares = [s] ++ [sMult x x | x <- squares]

-- | Power mod 2^n. Fixed bit-width version
sPow' :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBits a v
sPow' s t = foldr sMult' (makeSymbolic 1) powers where
  powers     = map (\(s,t) -> ite t s (makeSymbolic 1)) $ zip squares (unWrap t)
  squares    = [s] ++ [sMult' x x | x <- squares]
  n          = getWidth s
  sMult' a b = setWidth (sMult a b) n

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
compByIndex :: SignBit (SBits a v) v => (SBool v -> SBool v -> SBool v)
                                     -> SBits a v -> SBits a v -> SBool v
compByIndex f s t = go . revUnwrap $ unifyWidth s t
  where
    revUnwrap (s,t) = (reverse . unWrap $ s, reverse . unWrap $ t)
    go ([a], [b])   = f a b
    go (a:as, b:bs) = f a b + (iff a b * go (as, bs))
    iff p q         = 1 + p + q

-- | Less than
sLT :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBool v 
sLT a b = ltSgn + (1+gtSgn)*(compByIndex lt a b)
  where
    ltSgn  = (getSign a)*(1 + getSign b)
    gtSgn  = (1 + getSign a)*(getSign b)
    lt p q = (1+p)*q

-- | Greater than
sGT :: SignBit (SBits a v) v => SBits a v -> SBits a v -> SBool v 
sGT a b = gtSgn + (1+ltSgn)*(compByIndex gt a b)
  where
    ltSgn  = (getSign a)*(1 + getSign b)
    gtSgn  = (1 + getSign a)*(getSign b)
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
liftWord :: Word8 -> SUInt String
liftWord i = setWidth (makeSymbolic (fromIntegral i)) 8

forceWord :: SUInt String -> Word8
forceWord = fromIntegral . forceInteger . (flip setWidth) 8

forceBool :: SBool String -> Bool
forceBool = testFF2 . getConstant

liftInt :: Integer -> SInt String
liftInt = makeSymbolic

forceInt :: SInt String -> Integer
forceInt = forceInteger

-- dropSymbolic . liftSymbolic is the identity
prop_SUInt_faithful a = (a >= 0) ==> a == (forceInt . liftInt $ a)

prop_sAnd_correct a b =
  forceInt (sAnd (liftInt a) (liftInt b)) == a .&. b

prop_sXor_correct a b = 
  forceInt (sXor (liftInt a) (liftInt b)) == a `xor` b

prop_sOr_correct a b = 
  forceInt (sOr (liftInt a) (liftInt b)) == a .|. b

prop_sNot_correct a =
  forceInt (sNot (liftInt a)) == complement a

prop_sLShift_correct a b = (b >= 0) ==>
  forceInt (sLShift (liftInt a) (liftInt b)) == a `shiftL` (fromIntegral b)

prop_sRShift_correct a b = (b >= 0) ==>
  forceInt (sRShift (liftInt a) (liftInt b)) == a `shiftR` (fromIntegral b)

-- Semantics is bitwidth dependent
prop_sLRot_correct a b = (b >= 0) ==>
  forceWord (sLRot (liftWord a) (liftWord b)) == a `rotateL` (fromIntegral b)

-- Semantics is bitwidth dependent
prop_sRRot_correct a b = (b >= 0) ==>
  forceWord (sRRot (liftWord a) (liftWord b)) == a `rotateR` (fromIntegral b)

-- Semantics is bitwidth dependent
prop_sPopcount_correct a =
  forceWord (sPopcount (liftWord a)) == fromIntegral (popCount a)

prop_sPlus_correct a b =
  forceInt (sPlus (liftInt a) (liftInt b)) == a + b

prop_sNeg_correct a = 
  forceInt (sNeg (liftInt a)) == (-a)

prop_sAbs_correct a = 
  forceInt (sAbs (liftInt a)) == abs a

prop_sMinus_correct a b =
  forceInt (sMinus (liftInt a) (liftInt b)) == a - b

prop_sMult_correct a b =
  forceInt (sMult (liftInt a) (liftInt b)) == a * b

prop_sQuot_correct a b = (b /= 0) ==>
  forceInt (sQuot (liftInt a) (liftInt b)) == a `quot` b

-- Haskell implements euclidean modulus, not truncated (C) semantics
prop_sMod_correct a b = (a >= 0) && (b > 0) ==>
  forceInt (sMod (liftInt a) (liftInt b)) == a `mod` b

prop_sPow_correct a b = (abs a < 256) && (b >= 0) && (b < 8) ==>
  forceInt (sPow (liftInt a) (liftInt b)) == a ^ b

-- Semantics is bitwidth dependent
prop_sPow'_correct a b = (b >= 0) ==>
  forceWord (sPow' (liftWord a) (liftWord b)) == a ^ b

prop_sLT_correct a b =
  forceBool (sLT (liftInt a) (liftInt b)) == (a < b)

prop_sLEq_correct a b =
  forceBool (sLEq (liftInt a) (liftInt b)) == (a <= b)

prop_sGT_correct a b =
  forceBool (sGT (liftInt a) (liftInt b)) == (a > b)

prop_sGEq_correct a b =
  forceBool (sGEq (liftInt a) (liftInt b)) == (a >= b)

prop_sEq_correct a b =
  forceBool (sEq (liftInt a) (liftInt b)) == (a == b)

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
  quickCheck $ prop_sPow'_correct
  quickCheck $ prop_sLT_correct
  quickCheck $ prop_sLEq_correct
  quickCheck $ prop_sGT_correct
  quickCheck $ prop_sGEq_correct
  quickCheck $ prop_sEq_correct
