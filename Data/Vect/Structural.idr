module Data.Vect.Structural

-- For structural lemmas about (Vect) modules
import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module
import Classes.Verified -- definition of verified algebras other than modules
import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20
import Data.Matrix.AlgebraicVerified

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
