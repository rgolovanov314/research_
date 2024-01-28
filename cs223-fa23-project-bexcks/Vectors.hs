module Vectors where 

import Fields 
import Control.Applicative hiding ((<**>))
import Data.List

data Var = Var Int
    deriving (Show)

instance Eq Var where 
    (==) (Var x) (Var y) = x ==y
instance Eq (Fin Var) where 
    (==) x y = (ord x == ord y) && (gen x == gen y) && (pow x == pow y)

makeFin :: Var -> Fin Var 
makeFin (Var int) = Fin int (Var int) 1


instance Group Var where 
    (<^>) (Var a) 0 = Var 1 
    (<^>) (Var a) 1 = Var a
    (<^>) (Var a) b 
        |(a - b)<0 = (Var a) <^> (b `mod` a)
        |(a - b)==0 = Var 1
        |otherwise = Var (a-b+1)
        
--note that general fin a was defined regardless of a    
instance Group ([Fin Var]) where 
    xs <+> ys = [x <+> y | x <- xs, y <- ys]


--data Polynomial c = (Field c) => Polynomial {vars::[Var],coeffs::[FieldElem [c] c]}
--data Polynomial c = (Group c,Field c) => Polynomial [FieldElem [c] c]
data FPolynomial = FPolynomial [FiniteField]
data FVectors = FVectors [(Fin Var,FiniteField)]

instance Group (FPolynomial) where 
    p <+> (FPolynomial []) = p 
    (FPolynomial []) <+> p = p
    (FPolynomial p) <+> (FPolynomial q) = FPolynomial $ (*$) (<+>) p q
    (FPolynomial p) <-> (FPolynomial q) = FPolynomial $ (*$) (<->) p q
    p <^> b = raise_poly p b

raise_poly :: FPolynomial -> Int -> FPolynomial
raise_poly (FPolynomial coeffs) pow = FPolynomial (raise coeffs pow) 

get :: [a] -> FieldElem [a] c  -> c 
get state val = fst (runF val state)

productPoly1 :: FPolynomial -> FPolynomial -> [FPolynomial]
productPoly1 (FPolynomial []) q = []
productPoly1 (FPolynomial p)(FPolynomial q) =
    let q1 = raise q (length p-1)
        scalar = head p
        scaled = FPolynomial $ map (<**> scalar) q1
    in scaled : productPoly1 (FPolynomial (tail p)) (FPolynomial q)

max_length :: [[a]] -> Int 
max_length xs = head ((reverse.sort) (map length xs))

sumPoly :: [FPolynomial] -> FPolynomial
sumPoly minis = 
    let unwrapped = map unwrap minis
        len = max_length unwrapped
        normalized = map (\x -> normalize x len) unwrapped
        wrapped = [FPolynomial m| m<-normalized]
    in foldr (<+>) (FPolynomial []) wrapped

unwrap :: FPolynomial -> [FiniteField]
unwrap (FPolynomial x) = x

instance Ring FPolynomial where
    (<**>) p q = sumPoly (productPoly1 p q)


scale :: FiniteField -> FVectors -> FVectors
scale scalar (FVectors tups) = FVectors $ map (fmap (<**> scalar)) tups

--double fmap
($*) :: (x->b) -> [(a,x)] -> [(a,b)]
($*) f [] = []
($*) f ((a,x):xs) = (a, f x) : (($*) f xs)

--double wrap
(<$*>) :: [(a,(x->b))] ->[(a,x)] -> [(a,b)]
(<$*>) ((a,f):fs) ((ax,x):xs) = (a, f x) : (<$*>) fs xs
(<$*>) _           _          = []

--wrap func
($+) f as bs = f $* as <$*> bs

--i dont want to deal with ziplists
(*$) :: (a->b->c) -> [a] -> [b] -> [c]
(*$) f (x:xs) (y:ys) = (f x y) : ((*$) f xs ys)
(*$) _ _       _     = []

instance Group (FVectors) where 
    (<+>) (FVectors t1) (FVectors t2) = FVectors $ ($+) (<+>) t1 t2
    (<->) (FVectors t1) (FVectors t2) = FVectors $ ($+) (<->) t1 t2

instance Num (FVectors) where 
    (+) x y = x <+> y 
    (-) x y = x <-> y 
    negate x = (zeroVector x) <-> x
    (*) x y = x <**> y

instance Ring (FVectors) where 
    (<**>) t1 t2 = 
        let (v1,p1) = toPoly t1
            (v2,p2) = toPoly t2
            (FPolynomial p) = p1 <**> p2 
            v3 = rm_dups (v1 <+> v2) 
        in simplify (length v1) (FVectors (zip v3 p))

--rn only working on quadratic case
simplify1 :: Int -> (Fin Var,FiniteField) -> (Fin Var,FiniteField) 
simplify1 degree fv@(Fin o g pw,p) = 
    if pw>= degree then 
        --else if pw >= degree 
        -- max = order so all noncooperative are between deg and order
        let t@(q,r) = (pw `div` degree, pw `mod` degree)
            scalar = getGen p
            scaled = p <**> (scalar ^ q)
        in (Fin o g r, scaled) 
    else fv

getGen :: FiniteField -> FiniteField
getGen el = FieldElem $ \s0 -> 
    let ((a,m),as) = runF el s0
        g = gen m 
        tup = extract g s0
    in (tup,as)

instance Num (FieldElem [Tuple] Tuple) where 
    (+) ma mb = ma <+> mb 
    (-) ma mb = ma <-> mb 
    (*) ma mb = ma <**> mb

simplify :: Int -> FVectors -> FVectors
simplify deg (FVectors tups) = 
    let simplified = map (simplify1 deg) tups  
        new = prelim (group_ simplified)      
    in FVectors new

group_ :: Eq a => [(a,b)] -> [[(a,b)]]
group_ [] = []
group_ all@(t:xs) = 
    let curr = fst t
        n = [f | f <- all, (fst f) == curr]
        m = [f | f <- all, (fst f) /= curr]
    in n : (group_ m)
    
prelim :: [[(Fin Var,FiniteField)]] -> [(Fin Var,FiniteField)]
prelim [] = []
prelim (g:grouped) = 
    let (vs,fs) = unzip g
        v = head vs
    in (v,(foldr (<+>) zero fs)) : prelim grouped

vinv :: FVectors -> FVectors
vinv v@(FVectors tups) = 
    let (Fin o g p,f) = tups !! 0
    in v ^ o

instance Field FVectors where 
    (</>) v1 v2 = v1 <**> (vinv v2)

zeroVector :: FVectors -> FVectors
zeroVector (FVectors tups) = 
    let (vs,cs) = unzip tups 
        zipped = zip vs [zero|i<-[1..length vs]]
    in FVectors zipped

toPoly :: FVectors -> ([Fin Var],FPolynomial)
toPoly (FVectors tups) = 
    let start = unzip tups
    in (fst start,FPolynomial (snd start))

bases :: [Tuple] -> Int -> [FVectors]
--bases field 1 = 
    --let g = makeFin (Var $ (length field +1))
bases field degree =
    let g = makeFin (Var $ (length field -1)*(degree))
        vs = [g <^> i | i <- [0..(degree -1)]]
        ones = map (flip normalize degree) [raise [one] i | i <- [0..degree-1]]
        zeroV = normalize [zero] (degree)
        nums = [(*$) (<+>) zeroV i|i <-ones]
    in map (\x -> FVectors (zip vs x)) nums


computeFromList :: [FiniteField] -> [FVectors] -> FVectors
computeFromList nums basis = 
    let scaled = (*$) scale nums basis
        zzero  = (basis !! 0) <-> (basis !! 0)
    in foldr (<+>) zzero scaled

raiseField :: [Tuple] -> Int -> [FVectors]
--raiseField field 1 = 
    --let combinations = [map put c|c <- field]
    --in [computeFromList num ]
raiseField field degree = 
    let basis = bases field degree 
        combs = sequenceA (replicate degree field)
        combinations = [map put c | c <- combs]
    in [computeFromList num basis | num <- combinations]