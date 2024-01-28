module Fields where 

import Control.Monad
import Control.Applicative hiding ((<**>))
import Data.List


class Group a where 
    (<+>) :: a -> a -> a
    (<^>) :: a -> Int -> a
    (<->) :: a -> a -> a  
    inverse :: a -> a
    gid   :: a 

class Group a => Ring a where 
    (<**>)   :: a -> a -> a
    (<++>)   :: a -> a -> a

class Ring a => Field a where 
    (</>)  :: a -> a -> a

data Fin a = 
      Fin {ord::Int,gen ::a,pow::Int}
    | Val a
    deriving (Show)

getVal :: (Group a) => Fin a -> a 
getVal (Fin _ gen pow) = gen <^> pow
getVal (Val v)       = v

instance Functor Fin where 
    fmap f (Fin ord gen pow) = Fin ord (f gen) pow 
    fmap f (Val x)       = Val (f x)

instance Group (a->a) where
    (<+>) f g = f.g 
    (<^>) f p = foldr (.) id (replicate (p-1) f)
    gid       = id

data FieldElem s a = FieldElem {runF :: s -> (a,s)}

put :: c -> FieldElem [c] c 
put val = FieldElem $ \s0 -> (val,s0)

instance Monad (FieldElem s) where 
    return = pure
    (>>=) ma f = FieldElem $ \s0 ->
        let
            (a, s1) = runF ma s0
            (b, s2) = runF (f a) s1
        in
            (b, s2)

instance Applicative (FieldElem s) where
    pure x = FieldElem $ \s -> (x,s) 
    (<*>) = ap

instance Functor (FieldElem s) where 
    fmap f ma = (pure f) <*> ma

data GrpElem a = 
    GrpElem {operation::(a->a->a), identity::a, element::a}

instance Group (GrpElem a) where 
    (<+>) (GrpElem f e x) (GrpElem g ef y) = GrpElem f e (f x y) 
    (<^>) (GrpElem f e x)  0            = GrpElem f e e
    (<^>) (GrpElem f e x)  b            = GrpElem f e ((foldr (.) id (replicate (b-1) (f x))) x) 

instance Group (FieldElem [GrpElem a] (GrpElem a)) where 
    (<+>) x y = liftA2 (<+>) x y
    (<^>) x b = 
        FieldElem $ \s0 ->   
        let 
            (a,s1) = runF x s0 
        in (a <^> b,s1)

instance Group (Fin a) where 
    (<+>) (Fin ord x i) (Fin _ _ j) 
        | (i+j+1) > ord = Fin ord x ((i+j+1) `mod` ord)
        | otherwise     = Fin ord x ((i+j) `mod` ord)
    (<->) (Fin ord x i) (Fin _ _ j) 
        | i - j < 0 = Fin ord x (ord - 1 -((j-i)`mod` ord))
        | otherwise = Fin ord x ((i-j) `mod` ord)
    (<^>) (Fin ord x i)  b           = Fin ord x ((i*b) `mod` ord)
    inverse (Fin ord g i)            = Fin ord g (ord-i-1)


type Tuple = (Fin (GrpElem NewInt), Fin (GrpElem NewInt))

data NewInt =
      AddInt Int 
    | MultInt Int
    deriving (Show,Eq)


instance Eq (GrpElem NewInt) where 
    (==) (GrpElem f e x) (GrpElem g ef y) = ((==) x y) && ((==) e ef)

finVal :: Fin (GrpElem NewInt) -> GrpElem NewInt 
finVal x = 
    case (getVal x) of
        GrpElem f e (MultInt a) -> GrpElem f e (MultInt (a `mod` (ord x)))
        GrpElem g y (AddInt a) -> GrpElem g y (AddInt (a `mod` (ord x)))


--get operation-specific element from the field
--this is useful / necessary when defining addition/multiplication wrt the tuple
extract :: GrpElem NewInt -> [Tuple] -> Tuple 
extract val@(GrpElem (*) (MultInt 1) (MultInt v)) vals = 
    let mults = map (\x -> (finVal (snd x), x)) vals
        default_ = vals !! 0
    in case lookup val mults of 
        Just grpform -> grpform 
        Nothing      -> default_
extract val@(GrpElem (+) (AddInt 0) (AddInt v)) vals = 
    let adds = map (\x -> (finVal (fst x), x)) vals
        default_ = vals !! 0
    in case lookup val adds of 
        Just grpform -> grpform 
        Nothing      -> default_

-- 1 or 2 specifies if u wanna act on multiplicative or additive
-- lets u perform an operation on a field without having to deal with the field itself
fieldOp :: Int -> (GrpElem NewInt -> GrpElem NewInt) -> Tuple -> FieldElem [Tuple] Tuple
fieldOp 1 f t = FieldElem $ \s0 ->
    let val = f (getVal (fst t))
    in (extract val s0,s0)
fieldOp 2 f t = FieldElem $ \s0 ->
    let val = f (getVal (snd t))
    in (extract val s0,s0)

instance Group (FieldElem [Tuple] Tuple) where 
    (<+>) ma mb = FieldElem $ \s0 ->
        let ((a1,_),as) = runF ma s0
            ((a2,_),_) = runF mb as
        in (extract (getVal(a1 <+> a2)) as,as)
    (<->) ma mb = FieldElem $ \s0 ->
        let ((a1,_),as) = runF ma s0
            ((a2,_),_) = runF mb as
        in (extract (getVal(a1 <-> a2)) as,as)

pure_new :: NewInt -> GrpElem NewInt 
pure_new (AddInt x) = GrpElem (+) (AddInt 0) (AddInt x)
pure_new (MultInt x) = GrpElem (*) (MultInt 1) (MultInt x)

--forwarding all usual int properties to newint. whats important here is that +
--and * are defined the same, i.e. not wrt group operation
instance Num NewInt where 
    (+) (AddInt x) (AddInt y) = AddInt (x+y)
    (+) (MultInt x) (MultInt y) = MultInt (x+y)
    (-) (AddInt x) (AddInt y) = AddInt (x-y)
    (-) (MultInt x) (MultInt y) = MultInt (x-y)
    (*) (AddInt x) (AddInt y) = AddInt (x*y)
    (*) (MultInt x) (MultInt y) = MultInt (x*y)
    negate (AddInt x) = AddInt (negate x)
    negate (MultInt x) = MultInt (negate x)

instance Group NewInt where 
    (<+>) x y = x + y
    (<^>) x 0 = AddInt 0


instance Ring (GrpElem NewInt) where 
    (<**>) (GrpElem f e x) (GrpElem _ _ y) = GrpElem f e (x*y)
    (<++>) (GrpElem f e x) (GrpElem _ _ y) = GrpElem f e (x+y)

instance Eq (Fin (GrpElem NewInt)) where 
    (==) a b = (getVal a) == (getVal b)

--type FieldSet c = (Field c) => FieldElem [c] c
type FiniteField = FieldElem [Tuple] Tuple

minv :: FiniteField -> FiniteField
minv  = (=<<) (fieldOp 2 inverse) 

instance Ring (FiniteField) where 
    (<++>) ma mb = ma <+> mb 
    (<**>) ma mb = FieldElem $ \s0 ->
        let ((a1,m1),as) = runF ma s0
            ((a2,m2),_) = runF mb as
        in 
            if ((a1 == m1) || (a2==m2)) 
            then (as !! 0,as)
            else (extract (finVal(m1 <+> m2)) as,as)

instance Field (FiniteField) where 
    (</>) ma mb = ma <**> (minv mb)

getTNum :: [Tuple] -> FiniteField -> Tuple
getTNum base num = fst (runF num base)

find_gen :: Int -> GrpElem NewInt 
find_gen prime = 
    let og = [1..(prime-1)]
        q_residues = rm_dups $ map ((`mod` prime).(^2)) og 
        prim = filter (\x -> not (x`elem` q_residues)) og 
        in pure_new (MultInt (prim !! 0))

f_p :: Int -> [Tuple]
f_p order = 
    let mults = makeMultFinite order
        adds  = makeAddFinite (order + 1)
        in organize adds mults

makeMultFinite :: Int -> [Fin (GrpElem NewInt)]
makeMultFinite order = 
    let g = find_gen order 
    in [Fin order g i | i <-[0..(order-1)]]

makeAddFinite :: Int -> [Fin (GrpElem NewInt)]
makeAddFinite order = 
    let g = pure_new (AddInt 1)
    in [Fin order g i | i <-[0..(order - 2)]]

instance Group Tuple where 
    (<+>) (a1,m1) (a2,m2) = 
        let sum = a1 <+> a2
            val = getVal sum
        in (sum, Val val)
    (<^>) (a1,m1) b = 
        let power = m1 <^> b 
            val = getVal power 
        in (Val val,power)

toInt :: Fin (GrpElem NewInt) -> Int 
toInt x = 
    case (getVal x) of
        GrpElem _ _ (MultInt a) -> a `mod` (ord x)
        GrpElem _ _ (AddInt a) -> a `mod` (ord x)


organize :: [Fin (GrpElem NewInt)] -> [Fin (GrpElem NewInt)] -> [Tuple]
organize ns ms = 
    let a1s = map (\x -> (toInt x,x)) ns 
        m1s = map (\x -> (toInt x,x)) ms 
    in map (\a -> f a m1s) ns where 
        f x y = case lookup (toInt x) y of 
                Just nice -> (x,nice)
                Nothing   -> (ns !! 0, ns !! 0)


raise :: [FieldElem [c] c] -> Int -> [FieldElem [c] c]
--raise p 0   = [zero|i<-[1..(length p)-1]] ++ [one]
raise p num = p ++ [zero|i<-[1..num]]

normalize :: [FieldElem [c] c] -> Int -> [FieldElem [c] c]
normalize p num 
    | length p >= num = p 
    | otherwise = [zero|i<-[1..(num - (length p))]] ++ p

rm_dups :: (Eq a) => [a] -> [a]
rm_dups [] = []
rm_dups (x:xs) 
    | x `elem` xs = rm_dups xs 
    | otherwise   = x : (rm_dups xs)

zero :: FieldElem [c] c
zero = FieldElem $ \s -> (s !! 0,s)

one :: FieldElem [c] c 
one = FieldElem $ \s -> (s !! 1,s)

number :: Int -> FieldElem [c] c 
number x = FieldElem $ \s -> (s !! x,s)