import Fields
import Vectors
import Showing

-- base field generation --
f_3 = f_p 3
f_5 = f_p 5
f_7 = f_p 7

primes :: [Int]
primes = [3,5,7,11,13,17,19]

instance {-# OVERLAPS #-} Show Tuple where 
    show x = show (pretty_one x)

raise_3 = raiseField f_3

-- work with f_11 to show arithmetic --
f_11 = f_p 11

raise1 = \x -> raiseField x 1
raise2 = \x -> raiseField x 2

raise_11 = raiseField f_11

pv11 = pretty_vector f_11
pv11s = map pv11

detailed :: Int -> [Tuple] -> FVectors -> [Fin (GrpElem NewInt)]
detailed 1 field (FVectors fv) =
    let xs = map snd fv
        y = map (getTNum field) xs
    in map snd y
detailed 0 field (FVectors fv) =
    let xs = map snd fv
        y = map (getTNum field) xs
    in map fst y
    

-- galois/automorphisms
quad3 = raise2 f_3
quad5 = raise2 f_5
quad7 = raise2 f_7

instance {-# OVERLAPS #-} Show ([Tuple],[FVectors]) where 
    show (f,x) = show (map prettier (map (pretty_vector f) x))

instance {-# OVERLAPS #-} Eq ([Tuple],FVectors) where 
    (==) (f1,x) (f2,y) = 
        let xs = (prettier.(pretty_vector f1)) x
            ys = (prettier.(pretty_vector f2)) y
            xy = zip xs ys
            bools = map (\(x,y)->x==y) xy
        in foldr (&&) (True) (bools)


f3 = map (^3) quad3
check :: Int -> [Tuple] -> [FVectors] -> [FVectors] -> [FVectors]
check 0 f v1 v2 = 
    let p = filter (\(x,y) -> (f,x)==(f,y)) (zip v1 v2)
    in fst (unzip p)
check 1 f v1 v2 = 
    let p = filter (\(x,y) -> (f,x)/=(f,y)) (zip v1 v2)
    in fst (unzip p)

cube :: [FVectors] -> [FVectors]
cube = map (^3)
square :: [FVectors] -> [FVectors]
square = map (^2)