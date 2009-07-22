------------------------------------------------------------------------------
-- |
-- Module       : Data.Param.TFVec
-- Copyright    : (c) 2009 Christiaan Baaij
-- Licence      : BSD-style (see the file LICENCE)
--
-- Maintainer   : christiaan.baaij@gmail.com
-- Stability    : experimental
-- Portability  : non-portable
--
-- 'TFVec': Fixed sized vectors. Vectors with numerically parameterized size,
--          using type-level numerals from 'tfp' library
--
------------------------------------------------------------------------------

module Data.Param.TFVec
  ( TFVec
  , empty
  , (+>)
  , singleton
  , vectorCPS
  , vectorTH
  , unsafeVector
  , readTFVec
  , length
  , lengthT
  , fromVector
  , null
  , (!)
  , replace
  , head
  , last
  , init
  , tail
  , take
  , drop
  , select
  , (<+)
  , (++)
  , map
  , zipWith
  , foldl
  , foldr
  , zip
  , unzip
  , shiftl
  , shiftr
  , rotl
  , rotr
  , concat
  , reverse
  , iterate
  , iteraten
  , generate
  , generaten
  , copy
  , copyn
  ) where
    

import Types
import Types.Data.Num.Decimal.Literals.TH
import Data.RangedWord

import Data.Generics (Data, Typeable)
import qualified Prelude as P
import Prelude hiding (
  null, length, head, tail, last, init, take, drop, (++), map, foldl, foldr,
  zipWith, zip, unzip, concat, reverse, iterate )
import qualified Data.Foldable as DF (Foldable, foldr)
import qualified Data.Traversable as DT (Traversable(traverse))
import Language.Haskell.TH hiding (Pred)
import Language.Haskell.TH.Syntax (Lift(..))

newtype (NaturalT s) => TFVec s a = TFVec {unTFVec :: [a]}
  deriving (Eq, Typeable)

deriving instance (NaturalT s, Typeable s, Data s, Typeable a, Data a) => Data (TFVec s a)

-- ==========================
-- = Constructing functions =
-- ==========================
                                                  
empty :: TFVec D0 a
empty = TFVec []

(+>) :: a -> TFVec s a -> TFVec (Succ s) a
x +> (TFVec xs) = TFVec (x:xs)

infix 5 +>

singleton :: a -> TFVec D1 a
singleton x = x +> empty

vectorCPS :: [a] -> (forall s . NaturalT s => TFVec s a -> w) -> w
vectorCPS xs = unsafeVectorCPS (toInteger (P.length xs)) xs

-- FIXME: Not the most elegant solution... but it works for now in clash
vectorTH :: Lift a => [a] -> ExpQ
-- vectorTH xs = (vectorCPS xs) lift
vectorTH [] = [| empty |]
vectorTH (x:xs) = [| x +> $(vectorTH xs) |]

unsafeVector :: NaturalT s => s -> [a] -> TFVec s a
unsafeVector l xs
  | fromIntegerT l /= P.length xs =
    error (show 'unsafeVector P.++ ": dynamic/static lenght mismatch")
  | otherwise = TFVec xs

readTFVec :: (Read a, NaturalT s) => String -> TFVec s a
readTFVec = read

readTFVecCPS :: Read a => String -> (forall s . NaturalT s => TFVec s a -> w) -> w
readTFVecCPS str = unsafeVectorCPS (toInteger l) xs
 where fName = show 'readTFVecCPS
       (xs,l) = case [(xs,l) | (xs,l,rest) <- readTFVecList str,  
                           ("","") <- lexTFVec rest] of
                       [(xs,l)] -> (xs,l)
                       []   -> error (fName P.++ ": no parse")
                       _    -> error (fName P.++ ": ambiguous parse")
        
-- =======================
-- = Observing functions =
-- =======================
length :: forall s a . NaturalT s => TFVec s a -> Int
length _ = fromIntegerT (undefined :: s)

lengthT :: NaturalT s => TFVec s a -> s
lengthT = undefined

fromVector :: NaturalT s => TFVec s a -> [a]
fromVector (TFVec xs) = xs

null :: TFVec D0 a -> Bool
null _ = True

(!) ::  ( PositiveT s
        , NaturalT u
        , (s :>: u) ~ True) => TFVec s a -> RangedWord u -> a
(TFVec xs) ! i = xs !! (fromInteger (toInteger i))

-- ==========================
-- = Transforming functions =
-- ==========================
replace :: (PositiveT s, NaturalT u, (s :>: u) ~ True) =>
  TFVec s a -> RangedWord u -> a -> TFVec s a
replace (TFVec xs) i y = TFVec $ replace' xs (toInteger i) y
  where replace' []     _ _ = []
        replace' (_:xs) 0 y = (y:xs)
        replace' (x:xs) n y = x : (replace' xs (n-1) y)
  
head :: PositiveT s => TFVec s a -> a
head = P.head . unTFVec

tail :: PositiveT s => TFVec s a -> TFVec (Pred s) a
tail = liftV P.tail

last :: PositiveT s => TFVec s a -> a
last = P.last . unTFVec

init :: PositiveT s => TFVec s a -> TFVec (Pred s) a
init = liftV P.init

take :: NaturalT i => i -> TFVec s a -> TFVec (Min s i) a
take i = liftV $ P.take (fromIntegerT i)

drop :: NaturalT i => i -> TFVec s a -> TFVec (s :-: (Min s i)) a
drop i = liftV $ P.drop (fromIntegerT i)

select :: (NaturalT f, NaturalT s, NaturalT n, (f :<: i) ~ True, 
          (((s :*: n) :+: f) :<=: i) ~ True) => 
          f -> s -> n -> TFVec i a -> TFVec n a
select f s n = liftV (select' f' s' n')
  where (f', s', n') = (fromIntegerT f, fromIntegerT s, fromIntegerT n)
        select' f s n = ((selectFirst0 s n).(P.drop f))
        selectFirst0 :: Int -> Int -> [a] -> [a]
        selectFirst0 s n l@(x:_)
          | n > 0 = x : selectFirst0 s (n-1) (P.drop s l)
          | otherwise = []
        selectFirst0 _ 0 [] = []

(<+) :: TFVec s a -> a -> TFVec (Succ s) a
(<+) (TFVec xs) x = TFVec (xs P.++ [x])

(++) :: TFVec s a -> TFVec s2 a -> TFVec (s :+: s2) a
(++) = liftV2 (P.++)

infixl 5 <+
infixr 5 ++

map :: (a -> b) -> TFVec s a -> TFVec s b
map f = liftV (P.map f)

zipWith :: (a -> b -> c) -> TFVec s a -> TFVec s b -> TFVec s c
zipWith f = liftV2 (P.zipWith f)

foldl :: (a -> b -> a) -> a -> TFVec s b -> a
foldl f e = (P.foldl f e) . unTFVec

foldr :: (b -> a -> a) -> a -> TFVec s b -> a
foldr f e = (P.foldr f e) . unTFVec

zip :: TFVec s a -> TFVec s b -> TFVec s (a, b)
zip = liftV2 P.zip

unzip :: TFVec s (a, b) -> (TFVec s a, TFVec s b)
unzip (TFVec xs) = let (a,b) = P.unzip xs in (TFVec a, TFVec b)

shiftl :: (PositiveT s, NaturalT n, n ~ Pred s, s ~ Succ n) => 
          TFVec s a -> a -> TFVec s a
shiftl xs x = x +> init xs

shiftr :: (PositiveT s, NaturalT n, n ~ Pred s, s ~ Succ n) => 
          TFVec s a -> a -> TFVec s a
shiftr xs x = tail xs <+ x
  
rotl :: forall s a . NaturalT s => TFVec s a -> TFVec s a
rotl = liftV rotl'
  where vlen = fromIntegerT (undefined :: s)
        rotl' [] = []
        rotl' xs = let (i,[l]) = splitAt (vlen - 1) xs
                   in l : i 

rotr :: NaturalT s => TFVec s a -> TFVec s a
rotr = liftV rotr'
  where
    rotr' [] = []
    rotr' (x:xs) = xs P.++ [x] 

concat :: TFVec s1 (TFVec s2 a) -> TFVec (s1 :*: s2) a
concat = liftV (P.foldr ((P.++).unTFVec) [])

reverse :: TFVec s a -> TFVec s a
reverse = liftV P.reverse

iterate :: NaturalT s => (a -> a) -> a -> TFVec s a
iterate = iteraten (undefined :: s)

iteraten :: NaturalT s => s -> (a -> a) -> a -> TFVec s a
iteraten s f x = let s' = fromIntegerT s in TFVec (P.take s' $ P.iterate f x)

generate :: NaturalT s => (a -> a) -> a -> TFVec s a
generate = generaten (undefined :: s)

generaten :: NaturalT s => s -> (a -> a) -> a -> TFVec s a
generaten s f x = let s' = fromIntegerT s in TFVec (P.take s' $ P.tail $ P.iterate f x)

copy :: NaturalT s => a -> TFVec s a
copy x = copyn (undefined :: s) x

copyn :: NaturalT s => s -> a -> TFVec s a
copyn s x = iteraten s id x

-- =============
-- = Instances =
-- =============
instance Show a => Show (TFVec s a) where
  showsPrec _ = showV.unTFVec
    where showV []      = showString "<>"
          showV (x:xs)  = showChar '<' . shows x . showl xs
                            where showl []      = showChar '>'
                                  showl (x:xs)  = showChar ',' . shows x .
                                                  showl xs

instance (Read a, NaturalT nT) => Read (TFVec nT a) where
  readsPrec _ str
    | all fitsLength possibilities = P.map toReadS possibilities
    | otherwise = error (fName P.++ ": string/dynamic length mismatch")
    where 
      fName = "Data.Param.TFVec.read"
      expectedL = fromIntegerT (undefined :: nT)
      possibilities = readTFVecList str
      fitsLength (_, l, _) = l == expectedL
      toReadS (xs, _, rest) = (TFVec xs, rest)
      
instance NaturalT s => DF.Foldable (TFVec s) where
 foldr = foldr
 
instance NaturalT s => Functor (TFVec s) where
 fmap = map

instance NaturalT s => DT.Traversable (TFVec s) where 
  traverse f = (fmap TFVec).(DT.traverse f).unTFVec

instance (Lift a, NaturalT nT) => Lift (TFVec nT a) where
  lift (TFVec xs) = [|  unsafeTFVecCoerse 
                        $(decLiteralV (fromIntegerT (undefined :: nT))) 
                        (TFVec xs) |]

-- ======================
-- = Internal Functions =
-- ======================
liftV :: ([a] -> [b]) -> TFVec nT a -> TFVec nT' b
liftV f = TFVec . f . unTFVec

liftV2 :: ([a] -> [b] -> [c]) -> TFVec s a -> TFVec s2 b -> TFVec s3 c
liftV2 f a b = TFVec (f (unTFVec a) (unTFVec b))

splitAtM :: Int -> [a] -> Maybe ([a],[a])
splitAtM n xs = splitAtM' n [] xs
  where splitAtM' 0 xs ys = Just (xs, ys)
        splitAtM' n xs (y:ys) | n > 0 = do
          (ls, rs) <- splitAtM' (n-1) xs ys
          return (y:ls,rs)
        splitAtM' _ _ _ = Nothing

unsafeTFVecCoerse :: nT' -> TFVec nT a -> TFVec nT' a
unsafeTFVecCoerse _ (TFVec v) = (TFVec v)

unsafeVectorCPS :: forall a w . Integer -> [a] ->
                        (forall s . NaturalT s => TFVec s a -> w) -> w
unsafeVectorCPS l xs f = reifyNaturalD l 
                        (\(_ :: lt) -> f ((TFVec xs) :: (TFVec lt a)))

readTFVecList :: Read a => String -> [([a], Int, String)]
readTFVecList = readParen' False (\r -> [pr | ("<",s) <- lexTFVec r,
                                              pr <- readl s])
  where
    readl   s = [([],0,t) | (">",t) <- lexTFVec s] P.++
                            [(x:xs,1+n,u) | (x,t)       <- reads s,
                                            (xs, n, u)  <- readl' t]
    readl'  s = [([],0,t) | (">",t) <- lexTFVec s] P.++
                            [(x:xs,1+n,v) | (",",t)   <- lex s,
                                            (x,u)     <- reads t,
                                            (xs,n,v)  <- readl' u]
    readParen' b g  = if b then mandatory else optional
      where optional r  = g r P.++ mandatory r
            mandatory r = [(x,n,u) | ("(",s)  <- lexTFVec r,
                                      (x,n,t) <- optional s,
                                      (")",u) <- lexTFVec t]

-- Custom lexer for FSVecs, we cannot use lex directly because it considers
-- sequences of < and > as unique lexemes, and that breaks nested FSVecs, e.g.
-- <<1,2><3,4>>
lexTFVec :: ReadS String
lexTFVec ('>':rest) = [(">",rest)]
lexTFVec ('<':rest) = [("<",rest)]
lexTFVec str = lex str
                                           