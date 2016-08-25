module Data.Vect.Structural

-- For structural lemmas about (Vect) modules
import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module
import Classes.Verified -- definition of verified algebras other than modules
import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20
import Data.Matrix.AlgebraicVerified



{-
Theorem (vecHeadtailsEq) for proving equality of (Vect)s by proving equality of their heads and tails. Often used after (headtails).
-}



vecHeadtailsEq : {xs,ys : Vect _ _} -> ( headeq : x = y ) -> ( taileq : xs = ys ) -> x::xs = y::ys
vecHeadtailsEq {x} {xs} {ys} headeq taileq = trans (vectConsCong x xs ys taileq) $ cong {f=(::ys)} headeq
-- Also a solid proof:
-- vecHeadtailsEq {x} {xs} {ys} headeq taileq = trans (cong {f=(::xs)} headeq) $ replace {P=\l => l::xs = l::ys} headeq $ vectConsCong x xs ys taileq



{-
* Theorems characterizing (Vect)s of degenerate qualities.
* Theorems characterizing the index or head of a list created with a certain operation.
* The theorem (weakenedInd) about comparing an index of a list to an index of its (init).
-}



total
zeroVecEq : {a : Vect 0 r} -> {b : Vect 0 r} -> a = b
zeroVecEq {a=[]} {b=[]} = Refl



total
vecSingletonReplicateEq : ((u : a) -> v=u) -> (xs : Vect n a) -> (xs = replicate n v)
vecSingletonReplicateEq f [] = Refl
vecSingletonReplicateEq f (x::xs) {v} = rewrite sym (f x) in cong {f=(v::)} (vecSingletonReplicateEq f xs)



total
zeroVecVecId : (xs : Vect n (Vect 0 a)) -> (xs = replicate n [])
zeroVecVecId = vecSingletonReplicateEq (\b => zeroVecEq {a=[]} {b=b})



total
headMapChariz : {xs : Vect (S n) _} -> head $ map f xs = f $ head xs
headMapChariz {xs=x::xs} = Refl

mapheadrec : with Data.Vect ( map head (v::vs) = (head v) :: (map head vs) )
mapheadrec = Refl

headtails : (v : Vect (S predk) _) -> v = (head v) :: (tail v)
headtails (vv::vvs) = Refl



-- The theorem below this one should not be a necessary weakening, since the functions have equivalent definitions.
-- indexFZIshead : index FZ = Data.Vect.head

total
indexFZIsheadValued : index FZ xs = head xs
indexFZIsheadValued {xs=x :: xs} = Refl



indexMapChariz : Data.Vect.index k $ map f xs = f $ index k xs
indexMapChariz {xs=[]} {k} = FinZElim k
-- indexMapChariz {xs} {f} {k=FZ} = trans indexFZIsheadValued $ trans headMapChariz $ sym $ cong indexFZIsheadValued
indexMapChariz {xs=x::xs} {f} {k=FZ} = Refl
indexMapChariz {xs=x::xs} {f} {k=FS k} = indexMapChariz {xs=xs} {f=f} {k=k}

indexUpdateAtChariz : index i $ updateAt i f xs = f $ index i xs
indexUpdateAtChariz {xs=[]} {i} = FinZElim i
indexUpdateAtChariz {xs=(x::xs)} {f} {i=FZ} = Refl
indexUpdateAtChariz {xs=x::xs} {f} {i=FS i} = indexUpdateAtChariz {xs=xs} {f=f} {i=i}

updateAtIndIsMapAtInd : index i $ updateAt i f xs = index i $ map f xs
updateAtIndIsMapAtInd = trans indexUpdateAtChariz $ sym indexMapChariz

deleteSuccRowVanishesUnderHead : head $ deleteRow (FS k) xs = head xs
deleteSuccRowVanishesUnderHead {xs=x::xs} = Refl

updateAtSuccRowVanishesUnderHead : head $ updateAt (FS k) f xs = head xs
updateAtSuccRowVanishesUnderHead {xs=x::xs} = Refl

zipWithEntryChariz : index i $ Vect.zipWith m x y = m (index i x) (index i y)



plusOneVectIsSuccVect : Vect (n+1) a = Vect (S n) a
plusOneVectIsSuccVect {a} {n} = sym $ cong {f=\k => Vect k a} $ trans (cong {f=S} $ sym $ plusZeroRightNeutral n) $ plusSuccRightSucc n Z

appendedSingletonAsSuccVect : (xs : Vect n a) -> (v : a) -> Vect (S n) a
appendedSingletonAsSuccVect {a} {n} xs v = rewrite sym $ plusOneVectIsSuccVect {a=a} {n=n} in (xs++[v])

consAppendedSingleton : {xs : Vect n a} -> appendedSingletonAsSuccVect (x::xs) v = x::appendedSingletonAsSuccVect xs v
consAppendedSingleton {x} {xs} {v} {a} {n} = the ( appendedSingletonAsSuccVect (x::xs) v = x::appendedSingletonAsSuccVect xs v ) ?consAppendedSingleton_rhs

{-
-- Too many problems with this, rewriting the types to handle Nat addition.
lastInd : {xs : Vect n a} -> Data.Vect.index Data.Fin.last (rewrite sym $ plusOneVectIsSuccVect {a=a} {n=n} in (xs++[v])) = v
-}

-- Could this be done with the reversal isomorphism of each Fin?
lastInd : {xs : Vect n a} -> index Data.Fin.last $ appendedSingletonAsSuccVect xs v = v
lastInd {xs=[]} = Refl
lastInd {xs=x::xs} {v} = rewrite consAppendedSingleton {x=x} {xs=xs} {v=v} in (lastInd {xs=xs} {v=v})
{-

"ERROR ON INTROS" BUG, CASE, SOLUTION

--------

> lastInd {xs=x::xs} = ?lastInd_rhs_2

> :prove lastInd_rhs_2
lastInd_rhs_2> intro

Type mismatch between
        Vect k a = Vect k a
and
        Vect (S (S k)) a = Vect (S (plus k 1)) a

which I think means the type signature for (lastInd) is being reanalyzed in the presence of (x::xs), as if inlined, in such a way that the sucessor to rewrite is the one inside rather than outside, or something.

This works fine:

> lastInd {xs=x::xs} {v} = the ( (index Data.Fin.last $ appendedSingletonAsSuccVect (x::xs) v) = v ) ?lastInd_rhs_2

and spells out

> lastInd {xs=x::xs} {v} = the ( (index Data.Fin.last $ appendedSingletonAsSuccVect (x::xs) v) = v ) ( rewrite consAppendedSingleton {x=x} {xs=xs} {v=v} in lastInd {xs=xs} {v=v} )

-}

{-
Could this be done with the reversal isomorphism of each Fin and a proof that weaken becomes FS under it?
-}
total
weakenedInd : {xs : Vect n a} -> index (weaken k) $ appendedSingletonAsSuccVect xs v = index k xs
weakenedInd {xs=[]} {k} = absurd k
weakenedInd {xs=x::xs} {k=FZ} {v} = rewrite consAppendedSingleton {x=x} {xs=xs} {v=v} in Refl
weakenedInd {xs=x::xs} {k=FS j} {v} = rewrite consAppendedSingleton {x=x} {xs=xs} {v=v} in weakenedInd {xs=xs} {k=j} {v}



{-
Theorems about the module (Vect n a) over a ring (a):
* Compatibility between the operations of the ring (a) and of (Vect n a) as a module under (index).
-}



-- For completeness's sake, these should have (index FZ) as (head) forms proved.

indexCompatInverse : VerifiedRingWithUnity a => (xs : Vect n a) -> (i : Fin n) -> index i $ inverse xs = inverse $ index i xs

indexCompatAdd : VerifiedRingWithUnity a => (xs, ys : Vect n a) -> (i : Fin n) -> index i $ xs <+> ys = index i xs <+> index i ys
indexCompatAdd xs ys i = zipWithEntryChariz {x=xs} {y=ys} {i=i} {m=(<+>)}

{-
Proof obstruction seems to be that the meaning of "inverse" depends on whether the class hierarchy is treated as

	VerifiedGroup < Group < Monoid < Semigroup

or as

	VerifiedGroup < VerifiedMonoid < VerifiedSemigroup < Semigroup
-}
indexCompatSub : VerifiedRingWithUnity a => (xs, ys : Vect n a) -> (i : Fin n) -> index i $ xs <-> ys = index i xs <-> index i ys
indexCompatSub xs ys i ?= trans (indexCompatAdd xs (inverse ys) i) $ cong {f=((index i xs)<+>)} $ indexCompatInverse ys i

indexCompatScaling : VerifiedRingWithUnity a => (r : a) -> (xs : Vect n a) -> (i : Fin n) -> index i $ r <#> xs = r <.> index i xs