module Showing where

import Vectors
import Fields

pretty :: Fin (GrpElem NewInt) -> Int
pretty x = 
    case (getVal x) of
        GrpElem _ _ (MultInt a) -> a `mod` (ord x)
        GrpElem _ _ (AddInt a) -> a `mod` (ord x)

fromGroup :: GrpElem a -> a
fromGroup (GrpElem f e x) = x

makeInt :: NewInt  -> Int
makeInt (AddInt x) = x 
makeInt (MultInt x) = x

pretty_tup :: Tuple -> (Int,Int)
pretty_tup (Val x,Fin o g p) = ((makeInt (fromGroup x)) `mod` o,pretty (Fin o g p))
pretty_tup (Fin o g p,Val x) = (pretty (Fin o g p), (makeInt (fromGroup x)) `mod` o)
pretty_tup (Fin o g p,Fin q r s) = (pretty (Fin o g p), pretty (Fin q r s))

pretty_one :: Tuple -> Int
pretty_one tup = fst (pretty_tup tup)

pretty_vector :: [Tuple] -> FVectors  -> [(Fin Var,Int)]
pretty_vector state vs =
    let tups = getTups vs 
        pretty_ish = map (fmap (getTNum state)) tups
    in map (fmap pretty_one) pretty_ish

prettier :: [(Fin Var,Int)] -> [Int]
prettier tups = map snd tups

getTups :: FVectors -> [(Fin Var,FiniteField)]
getTups (FVectors tups) = tups

showlist :: [c] -> [FieldElem [c] c] -> [c] 
showlist state vals= map (get state) vals

showpoly :: [Tuple] -> FPolynomial -> [Tuple]
showpoly state (FPolynomial p) = map (get state) p

instance Show (GrpElem NewInt) where 
    show (GrpElem f e x) = show x