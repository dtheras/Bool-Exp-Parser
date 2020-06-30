{-# LANGUAGE ApplicativeDo     #-}
{-# LANGUAGE OverloadedStrings #-}
-- |
-- Data:        Jun 2020
-- Author:      D. Heras
-- Title:       Bitnum,
-- Status:      Incomplete
-- Description: YARA boolean and numerical expression parser.
-- Compile:     ghc bitnum.hs
-- Use:         $ cat filepath | ./bitnum
--
import Control.Applicative (liftA2, Alternative(..), optional)
import Data.Attoparsec.ByteString (Parser, many', many1', string, parseOnly,
                                   word8, satisfy)
import Data.Attoparsec.ByteString.Char8 (isSpace_w8, decimal)
import Data.Bits (Bits(..))
import Data.ByteString (ByteString, append, null, readFile)
import Data.ByteString.Char8 (lines,pack, hPutStrLn,unpack)
import Data.Foldable (asum)
import Data.Functor (($>))
import Data.Int (Int64)
import Data.Word (Word8)
import Foreign.Marshal.Utils (fromBool)
import Prelude hiding (lines, null, readFile)
import System.IO (stderr)
import System.Posix.Env.ByteString (getArgs)

--------------------------------------------------------------------- Utilities

data T2 a s = T2 {-# UNPACK #-} !a
                 {-# UNPACK #-} !s
                 deriving Show

isHzWhitespace :: Word8 -> Bool
isHzWhitespace w = w == 32 || w == 9

-- Dumb operator as GHC doesn't permit unary prefix operators.
-- Eats whitespace before parser, usually writen like: <-0&
(&) :: (Eq a, Num a) => a -> Parser b -> Parser b
-- 0 or more white space horitzontal only
(&) 0 p = many' (satisfy isHzWhitespace) *> p
-- At least 1 or more whitespace, horizontal only
(&) 1 p = many1' (satisfy isHzWhitespace) *> p
-- Seek parser that must be on a new line
(&) 2 p = do
  many' (satisfy isHzWhitespace)
  satisfy (\w -> w - 10 <= 3)
  many' (satisfy isSpace_w8)
  p
-- Else same effect as 0
(&) _ p = p

-- Eats any horizontal white space before parsers.
liftA20 :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
liftA20 f p1 p2 = liftA2 f (0 & p1) (0 & p2)

asumMap :: (Alternative p, Foldable f) => (a -> p b) -> f a -> p b
asumMap f = foldr ((<|>) . f) empty

tokens :: [T2 Word8 a] -> Parser a
tokens = asumMap (\(T2 s v) -> word8 s $> v)

tokensBS :: [T2 ByteString a] -> Parser a
tokensBS = asumMap (\(T2 s v) -> string s $> v)

parseGroup :: Parser a -> Parser a
parseGroup par = 0& word8 28 *> 0& par <* 0& word8 29

toBool :: (Eq a, Num a) => a -> Bool
toBool = (/=0)

------------------------------------------------------ Numerical Expression AST

data BitVal = BitVal !Int64 | BitGrp !BitOr
  deriving Show

data BitNeg = BitNeg {-# UNPACK #-} !(Int64 -> Int64) {-# UNPACK #-} !BitVal

instance Show BitNeg where
  show (BitNeg _ v) = concat ["BitNeg (_, ", show v, ")"]

data BitMD = BitMD {-# UNPACK #-} !BitNeg
                   {-# UNPACK #-} ![T2 (Int64 -> Int64 -> Int64) BitNeg]

instance Show BitMD where
  show (BitMD n xs) = concat ["BitMD ( ", show n, " [", aux, "])"]
    where aux = foldl (\x (T2 _ n) -> concat [x,", T2(_ ",show n,")"]) "" xs

data BitPM = BitPM {-# UNPACK #-} !BitMD
                   {-# UNPACK #-} ![T2 (Int64 -> Int64 -> Int64) BitMD]

instance Show BitPM where
  show (BitPM n xs) = concat ["BitPM ( ", show n, " [", aux, "])"]
    where aux = foldl (\x (T2 _ n) -> concat [x,", T2(_ ",show n,")"]) "" xs

data BitShift = BitShift {-# UNPACK #-} !BitPM
                         {-# UNPACK #-} !BitPM
                         {-# UNPACK #-} !(Int64 -> Int -> Int64)

instance Show BitShift where
  show (BitShift p1 int _) = concat ["BitShift (",show p1,", ",show int,", _)"]

data BitAnd = BitAnd {-# UNPACK #-} !BitShift {-# UNPACK #-} ![BitShift]
  deriving Show

data BitOr = BitOr {-# UNPACK #-} !BitAnd {-# UNPACK #-} ![BitAnd]
  deriving Show

-------------------------------------------------------- Boolean Expression AST

data BoolVal = Boolean Bool
             | BitEq BitOr
             | BoolGrp BoolOr
             deriving Show

instance Eq BoolVal where
  (Boolean b1) == (Boolean b2) = b1 == b2
  (Boolean b1) == (BitEq   v2) = fromBool b1 == evalBitOr v2
  (Boolean b1) == (BoolGrp g2) = b1 == evalBoolOr g2
  (BitEq   v1) == (Boolean b2) = evalBitOr v1 == fromBool b2
  (BitEq   v1) == (BitEq   v2) = evalBitOr v1 == evalBitOr v2
  (BitEq   v1) == (BoolGrp g2) = evalBitOr v1 == fromBool (evalBoolOr g2)
  (BoolGrp g1) == (Boolean b2) = evalBoolOr g1 == b2
  (BoolGrp g1) == (BitEq   v2) = fromBool (evalBoolOr g1) == evalBitOr v2
  (BoolGrp g1) == (BoolGrp g2) = evalBoolOr g1 == evalBoolOr g2

instance Ord BoolVal where
  (Boolean b1) <= (Boolean b2) = b1 <= b2
  (Boolean b1) <= (BitEq   v2) = fromBool b1 <=  evalBitOr v2
  (Boolean b1) <= (BoolGrp g2) = b1 <= evalBoolOr g2
  (BitEq   v1) <= (Boolean b2) = evalBitOr v1 <= fromBool b2
  (BitEq   v1) <= (BitEq   v2) = evalBitOr v1 <= evalBitOr v2
  (BitEq   v1) <= (BoolGrp g2) = evalBitOr v1 <= fromBool (evalBoolOr g2)
  (BoolGrp g1) <= (Boolean b2) = evalBoolOr g1 <= b2
  (BoolGrp g1) <= (BitEq   v2) = fromBool (evalBoolOr g1) <= evalBitOr v2
  (BoolGrp g1) <= (BoolGrp g2) = evalBoolOr g1 <= evalBoolOr g2

data BoolOrd = BoolOrd BoolVal (BoolVal -> BoolVal -> Bool) BoolVal
             | BoolOrdSol BoolVal

wrap :: Int64 -> BoolVal
wrap s = BitEq (BitOr (BitAnd (BitShift (BitPM (BitMD (BitNeg id (BitVal s)) []) []) (BitPM (BitMD (BitNeg id (BitVal zeroBits)) []) []) const) []) [])

instance Eq BoolOrd where
  v1@BoolOrd{}      == v3@BoolOrd{}      = evalBoolOrd v1 == evalBoolOrd v3
  (BoolOrd v1 p v2) == (BoolOrdSol   v3) = wrap (fromBool $ p v1 v2) == v3
  (BoolOrdSol   v1) == (BoolOrd v3 q v4) = v1 == wrap (fromBool $ q v3 v4)
  (BoolOrdSol   v1) == (BoolOrdSol   v3) = v1 == v3

instance Show BoolOrd where
  show (BoolOrd v1 _ v2) = concat ["BoolOrd (",show v1,", _, ",show v2,")"]
  show (BoolOrdSol    v) = concat ["BoolOrdSol (", show v, ")"]

data BoolEq = BoolEq BoolOrd (BoolOrd -> BoolOrd -> Bool) BoolOrd
            | BoolEqSol BoolOrd

instance Show BoolEq where
  show (BoolEq o1 _ o2) = concat ["BoolEq (",show o1," _ ",show o2,")"]
  show (BoolEqSol o)    = concat ["BoolEqSol (", show o,""]

data BoolNeg = BoolNeg {-# UNPACK #-} !Bool {-# UNPACK #-} !BoolEq
  deriving Show

data BoolAnd = BoolAnd {-# UNPACK #-} !BoolNeg {-# UNPACK #-} ![BoolNeg]
  deriving Show

data BoolOr = BoolOr {-# UNPACK #-} !BoolAnd {-# UNPACK #-} ![BoolAnd]
  deriving Show

newtype BoolExp = BoolExp BoolOr
  deriving Show
---------------------------------------------------------- Evaluating BitEq AST

evalBitVal :: BitVal -> Int64
evalBitVal (BitVal v) = v
evalBitVal (BitGrp v) = evalBitOr v

evalBitNeg :: BitNeg -> Int64
evalBitNeg (BitNeg f v) = f (evalBitVal v)

evalBitMD :: BitMD -> Int64
evalBitMD (BitMD x xs) =
  foldl (\y (T2 o z) -> o y $ evalBitNeg z) (evalBitNeg x) xs

evalBitPM :: BitPM -> Int64
evalBitPM (BitPM x xs) =
  foldl (\y (T2 o z) -> o y $ evalBitMD z) (evalBitMD x) xs

evalBitShift :: BitShift -> Int64
evalBitShift (BitShift e i o) = o (evalBitPM e) (cast i :: Int)
  where cast = fromInteger.toInteger.evalBitPM

evalBitAnd :: BitAnd -> Int64
evalBitAnd (BitAnd x xs) =
  foldl (\y z -> y .&. evalBitShift z) (evalBitShift x) xs

evalBitOr :: BitOr -> Int64
evalBitOr (BitOr x xs) =
  foldl (\y z -> y .|. evalBitAnd z) (evalBitAnd x) xs

----------------------------------------------------------- Evaluating Bool AST

evalBoolVal :: BoolVal -> Bool
evalBoolVal (Boolean b) = b
evalBoolVal (BitEq   b) = toBool $ evalBitOr b
evalBoolVal (BoolGrp b) = evalBoolOr b

evalBoolOrd :: BoolOrd -> Bool
evalBoolOrd (BoolOrd v1 op v2) = v1 `op` v2
evalBoolOrd (BoolOrdSol v    ) = evalBoolVal v

evalBoolEq :: BoolEq -> Bool
evalBoolEq (BoolEq v1 op v2) = v1 `op` v2
evalBoolEq (BoolEqSol v    ) = evalBoolOrd v

evalBoolNeg :: BoolNeg -> Bool
evalBoolNeg (BoolNeg b e) = aux (evalBoolEq e)
  where aux = if b then not else id

evalBoolAnd :: BoolAnd -> Bool
evalBoolAnd (BoolAnd x xs) =
  foldl (\y z -> y || evalBoolNeg z) (evalBoolNeg x) xs

evalBoolOr :: BoolOr -> Bool
evalBoolOr (BoolOr x xs) =
  foldl (\y z -> y || evalBoolAnd z) (evalBoolAnd x) xs

evalBoolExp :: BoolExp -> Bool
evalBoolExp (BoolExp boolOr) = evalBoolOr boolOr

---------------------------------------------------------------- Parsing NumExp

parseBitVal :: Parser BitVal
parseBitVal = 0& (BitVal <$> decimal) <|> (BitGrp <$> parseGroup parseBitOr)

parseBitNeg :: Parser BitNeg
parseBitNeg = liftA20 BitNeg op parseBitVal
  where op = tokens [T2 45 negate, T2 126 complement] <|> pure id

parseBitMD :: Parser BitMD
parseBitMD = liftA20 BitMD parseBitNeg (many' $ liftA20 T2 op parseBitNeg)
  where op = tokens [T2 42 (*), T2 37 div]

parseBitPM :: Parser BitPM
parseBitPM = liftA20 BitPM parseBitMD (many' $ liftA20 T2 op parseBitMD)
  where op = tokens [T2 43 (+), T2 45 (-)]

parseBitShift :: Parser BitShift
parseBitShift = do
  e <-0& parseBitPM
  op <-0& optional (tokensBS [T2 "<<" shiftL, T2 ">>" shiftR])
  case op of
    Just sft -> (\w -> BitShift e w sft) <$> 0& parseBitPM
    Nothing  -> pure $ BitShift e zv const
  where zv = BitPM (BitMD (BitNeg id (BitVal zeroBits)) []) []

parseBitAnd :: Parser BitAnd
parseBitAnd =
  liftA20 BitAnd parseBitShift (many' $ 0& word8 38 *> 0& parseBitShift)

parseBitOr :: Parser BitOr
parseBitOr =
  liftA20 BitOr parseBitAnd (many' $ 0& word8 124 *> 0& parseBitAnd)

--------------------------------------------------------------- Parsing BoolExp

parseBoolVal :: Parser BoolVal
parseBoolVal = 0& asum [
    Boolean <$> tokensBS [T2 "true" True, T2 "false" False]
  , BitEq   <$> parseBitOr
  , BoolGrp <$> parseGroup parseBoolOr
  ]

parseBoolOrd :: Parser BoolOrd
parseBoolOrd = do
  v1 <-0& parseBoolVal
  m  <-0& optional (
            tokensBS [T2 "<" (<), T2 "<=" (<=), T2 ">" (>), T2 ">=" (>=)])
  case m of
    Just op -> do
      v2 <-0& parseBoolVal
      pure $ BoolOrd v1 op v2
    Nothing -> pure $ BoolOrdSol v1

parseBoolEq :: Parser BoolEq
parseBoolEq = do
  v1 <-0& parseBoolOrd
  m  <-0& optional (tokens [T2 61 (==), T2 33 (/=)] <* word8 61)
  case m of
    Just op -> do
      v2 <-0& parseBoolOrd
      pure $ BoolEq v1 op v2
    Nothing -> pure $ BoolEqSol v1

parseBoolNeg :: Parser BoolNeg
parseBoolNeg = liftA20 BoolNeg (isSucc $ string "not") parseBoolEq
   where isSucc :: Parser a -> Parser Bool
         isSucc par = (par $> True) <|> pure False
         {-# INLINE isSucc #-}

parseBoolAnd :: Parser BoolAnd
parseBoolAnd =
  liftA20 BoolAnd parseBoolNeg (many' $ do 0& string "and"; 0& parseBoolNeg)

parseBoolOr :: Parser BoolOr
parseBoolOr =
  liftA20 BoolOr parseBoolAnd (many' $ do 0& string "or"; 0& parseBoolAnd)

parseBoolExp :: Parser BoolExp
parseBoolExp = BoolExp <$> parseBoolOr
-- Having ^^^ may seem sterile but in the future it will
-- keep the data structure abstract to the maintainer(s).

------------------------------------------------------- The Outside World Stuff

puterr :: ByteString -> IO ()
puterr = hPutStrLn stderr

runParse :: ByteString -> IO ()
runParse bs = do
  let succ b = T2 (show b) (show $ evalBoolExp b)
      fail s = T2 "N/A" ("#!error!# " ++ s)
      (T2 mid out) = either fail succ (parseOnly parseBoolExp bs)
  puterr $ pack $ unlines
    ["IN(" ++ unpack bs ++ ")", "MID(" ++ mid ++ ")", "OUT(" ++ out ++ ")"]

main :: IO ()
main = do
  ls <- lines <$> readFile "/dev/stdin"
  case ls of
    []  -> puterr "No input was provided."
    _   -> do
      traverseP runParse ls
      puterr "Done."
  where
    -- Skip empty lines when traversing.
    traverseP f = foldr c (pure ())
      where c x k = if null x then k else f x *> k
            {-# INLINE c #-}
