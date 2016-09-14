module Data.Matrix.AlgebraicVerified

import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module
import Classes.Verified -- definition of verified algebras other than modules
import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20

import Data.Vect.Structural



{-
Definitions:
* Verified module
* Verified vector space

Ripped from comments of Classes.Verified, commenting out there coincides with definition of module being in the separate module Control.Algebra.VectorSpace from Control.Algebra.
-}



class (VerifiedRingWithUnity a, VerifiedAbelianGroup b, Module a b) => VerifiedModule a b where
  total moduleScalarMultiplyComposition : (x,y : a) -> (v : b) -> x <#> (y <#> v) = (x <.> y) <#> v
  total moduleScalarUnityIsUnity : (v : b) -> unity {a} <#> v = v
  total moduleScalarMultDistributiveWRTVectorAddition : (s : a) -> (v, w : b) -> s <#> (v <+> w) = (s <#> v) <+> (s <#> w)
  total moduleScalarMultDistributiveWRTModuleAddition : (s, t : a) -> (v : b) -> (s <+> t) <#> v = (s <#> v) <+> (t <#> v)

--class (VerifiedField a, VerifiedModule a b) => VerifiedVectorSpace a b where {}

-- As desired in Data.Matrix.Algebraic
instance [vectModule] Module a b => Module a (Vect n b) where
	(<#>) r = map (r <#>)



{-
Definitions:
* Verified module instance for Matrix n m ZZ.
* A verified module instance for Vect n ZZ will prevent you from writing one for Matrix,
	the proof of which depends on (Vect n ZZ) being a (VerifiedModule) in all but name.
-}



semigroupOpIsAssociative_Vect : (VerifiedRingWithUnity a) => (l, c, r : Vect n a) -> l <+> (c <+> r) = l <+> c <+> r
semigroupOpIsAssociative_Vect [] [] [] = Refl
semigroupOpIsAssociative_Vect (l::ls) (c::cs) (r::rs) = vecHeadtailsEq (semigroupOpIsAssociative _ _ _) (semigroupOpIsAssociative_Vect _ _ _)

monoidNeutralIsNeutralL_Vect : (VerifiedRingWithUnity a) => (l : Vect n a) -> l <+> Algebra.neutral = l
monoidNeutralIsNeutralL_Vect [] = Refl
monoidNeutralIsNeutralL_Vect (l::ls) = vecHeadtailsEq (monoidNeutralIsNeutralL _) $ monoidNeutralIsNeutralL_Vect _

monoidNeutralIsNeutralR_Vect : (VerifiedRingWithUnity a) => (r : Vect n a) -> Algebra.neutral <+> r = r
monoidNeutralIsNeutralR_Vect [] = Refl
monoidNeutralIsNeutralR_Vect (r::rs) = vecHeadtailsEq (monoidNeutralIsNeutralR _) $ monoidNeutralIsNeutralR_Vect _

groupInverseIsInverseL_Vect : (VerifiedRingWithUnity a) => (l : Vect n a) -> l <+> inverse l = Algebra.neutral
groupInverseIsInverseL_Vect [] = Refl
groupInverseIsInverseL_Vect (l::ls) = vecHeadtailsEq (groupInverseIsInverseL _) $ groupInverseIsInverseL_Vect _

groupInverseIsInverseR_Vect : (VerifiedRingWithUnity a) => (r : Vect n a) -> inverse r <+> r = Algebra.neutral
groupInverseIsInverseR_Vect [] = Refl
groupInverseIsInverseR_Vect (r::rs) = vecHeadtailsEq (groupInverseIsInverseR _) $ groupInverseIsInverseR_Vect _

abelianGroupOpIsCommutative_Vect : (VerifiedRingWithUnity a) => (l, r : Vect n a) -> l <+> r = r <+> l
abelianGroupOpIsCommutative_Vect [] [] = Refl
abelianGroupOpIsCommutative_Vect (l::ls) (r::rs) = vecHeadtailsEq (abelianGroupOpIsCommutative _ _) $ abelianGroupOpIsCommutative_Vect _ _

moduleScalarMultiplyComposition_Vect : (VerifiedRingWithUnity a) => ( x, y : a ) -> ( v : Vect n a ) -> x <#> (y <#> v) = x <.> y <#> v
moduleScalarMultiplyComposition_Vect x y [] = Refl
moduleScalarMultiplyComposition_Vect x y (v::vs) ?= vecHeadtailsEq (ringOpIsAssociative x y v) $ moduleScalarMultiplyComposition_Vect x y vs

moduleScalarUnityIsUnity_Vect : (VerifiedRingWithUnity a) => ( v : Vect n a ) -> (Algebra.unity {a=a}) <#> v = v
moduleScalarUnityIsUnity_Vect [] = Refl
moduleScalarUnityIsUnity_Vect (v::vs) ?= vecHeadtailsEq (ringWithUnityIsUnityR v) $ moduleScalarUnityIsUnity_Vect vs

moduleScalarMultDistributiveWRTVectorAddition_Vect : (VerifiedRingWithUnity a) => (s : a) -> (v, w : Vect n a) -> s <#> v <+> w = (s <#> v) <+> (s <#> w)
moduleScalarMultDistributiveWRTVectorAddition_Vect s [] [] = Refl
moduleScalarMultDistributiveWRTVectorAddition_Vect s (v::vs) (w::ws) ?= vecHeadtailsEq (ringOpIsDistributiveL s v w) $ moduleScalarMultDistributiveWRTVectorAddition_Vect s vs ws

moduleScalarMultDistributiveWRTModuleAddition_Vect : (VerifiedRingWithUnity a) => (s, t : a) -> (v : Vect n a) -> s <+> t <#> v = (s <#> v) <+> (t <#> v)
moduleScalarMultDistributiveWRTModuleAddition_Vect s t [] = Refl
moduleScalarMultDistributiveWRTModuleAddition_Vect s t (v::vs) ?= vecHeadtailsEq (ringOpIsDistributiveR s t v) $ moduleScalarMultDistributiveWRTModuleAddition_Vect s t vs

{-
instance (VerifiedRingWithUnity a) => VerifiedSemigroup (Vect n a) where
	semigroupOpIsAssociative = ?semigroupOpIsAssociative_Vect

instance (VerifiedRingWithUnity a) => VerifiedMonoid (Vect n a) where {
	monoidNeutralIsNeutralL = ?monoidNeutralIsNeutralL_Vect
	monoidNeutralIsNeutralR = ?monoidNeutralIsNeutralR_Vect
}

instance (VerifiedRingWithUnity a) => VerifiedGroup (Vect n a) where {
	groupInverseIsInverseL = ?groupInverseIsInverseL_Vect
	groupInverseIsInverseR = ?groupInverseIsInverseR_Vect
}

instance (VerifiedRingWithUnity a) => VerifiedAbelianGroup (Vect n a) where {
	abelianGroupOpIsCommutative = ?abelianGroupOpIsCommutative_Vect
}

instance (VerifiedRingWithUnity a) => VerifiedModule a (Vect n a) where {
	moduleScalarMultiplyComposition = ?moduleScalarMultiplyComposition_Vect
	moduleScalarUnityIsUnity = ?moduleScalarUnityIsUnity_Vect
	moduleScalarMultDistributiveWRTVectorAddition = ?moduleScalarMultDistributiveWRTVectorAddition_Vect
	moduleScalarMultDistributiveWRTModuleAddition = ?moduleScalarMultDistributiveWRTModuleAddition_Vect
}
-}



semigroupOpIsAssociative_Mat : (VerifiedRingWithUnity a) => (l, c, r : Matrix n m a) -> l <+> (c <+> r) = l <+> c <+> r
semigroupOpIsAssociative_Mat [] [] [] = Refl
semigroupOpIsAssociative_Mat (l::ls) (c::cs) (r::rs) = vecHeadtailsEq (semigroupOpIsAssociative_Vect _ _ _) (semigroupOpIsAssociative_Mat _ _ _)

monoidNeutralIsNeutralL_Mat : (VerifiedRingWithUnity a) => (l : Matrix n m a) -> l <+> Algebra.neutral = l
monoidNeutralIsNeutralL_Mat [] = Refl
monoidNeutralIsNeutralL_Mat (l::ls) = vecHeadtailsEq (monoidNeutralIsNeutralL_Vect _) $ monoidNeutralIsNeutralL_Mat _

monoidNeutralIsNeutralR_Mat : (VerifiedRingWithUnity a) => (r : Matrix n m a) -> Algebra.neutral <+> r = r
monoidNeutralIsNeutralR_Mat [] = Refl
monoidNeutralIsNeutralR_Mat (r::rs) = vecHeadtailsEq (monoidNeutralIsNeutralR_Vect _) $ monoidNeutralIsNeutralR_Mat _

groupInverseIsInverseL_Mat : (VerifiedRingWithUnity a) => (l : Matrix n m a) -> l <+> inverse l = Algebra.neutral
groupInverseIsInverseL_Mat [] = Refl
groupInverseIsInverseL_Mat (l::ls) = vecHeadtailsEq (groupInverseIsInverseL_Vect _) $ groupInverseIsInverseL_Mat _

groupInverseIsInverseR_Mat : (VerifiedRingWithUnity a) => (r : Matrix n m a) -> inverse r <+> r = Algebra.neutral
groupInverseIsInverseR_Mat [] = Refl
groupInverseIsInverseR_Mat (r::rs) = vecHeadtailsEq (groupInverseIsInverseR_Vect _) $ groupInverseIsInverseR_Mat _

abelianGroupOpIsCommutative_Mat : (VerifiedRingWithUnity a) => (l, r : Matrix n m a) -> l <+> r = r <+> l
abelianGroupOpIsCommutative_Mat [] [] = Refl
abelianGroupOpIsCommutative_Mat (l::ls) (r::rs) = vecHeadtailsEq (abelianGroupOpIsCommutative_Vect _ _) $ abelianGroupOpIsCommutative_Mat _ _

moduleScalarMultiplyComposition_Mat : (VerifiedRingWithUnity a) => ( x, y : a ) -> ( v : Matrix n m a ) -> x <#> (y <#> v) = x <.> y <#> v
moduleScalarMultiplyComposition_Mat x y [] = Refl
moduleScalarMultiplyComposition_Mat x y (v::vs) = vecHeadtailsEq (moduleScalarMultiplyComposition_Vect _ _ _) $ moduleScalarMultiplyComposition_Mat _ _ _

moduleScalarUnityIsUnity_Mat : (VerifiedRingWithUnity a) => ( v : Matrix n m a ) -> (Algebra.unity {a=a}) <#> v = v
moduleScalarUnityIsUnity_Mat [] = Refl
moduleScalarUnityIsUnity_Mat (v::vs) = vecHeadtailsEq (moduleScalarUnityIsUnity_Vect _) $ moduleScalarUnityIsUnity_Mat _

moduleScalarMultDistributiveWRTVectorAddition_Mat : (VerifiedRingWithUnity a) => (s : a) -> (v, w : Matrix n m a) -> s <#> v <+> w = (s <#> v) <+> (s <#> w)
moduleScalarMultDistributiveWRTVectorAddition_Mat s [] [] = Refl
moduleScalarMultDistributiveWRTVectorAddition_Mat s (v::vs) (w::ws) = vecHeadtailsEq (moduleScalarMultDistributiveWRTVectorAddition_Vect _ _ _) $ moduleScalarMultDistributiveWRTVectorAddition_Mat _ _ _

moduleScalarMultDistributiveWRTModuleAddition_Mat : (VerifiedRingWithUnity a) => (s, t : a) -> (v : Matrix n m a) -> s <+> t <#> v = (s <#> v) <+> (t <#> v)
moduleScalarMultDistributiveWRTModuleAddition_Mat s t [] = Refl
moduleScalarMultDistributiveWRTModuleAddition_Mat s t (v::vs) = vecHeadtailsEq (moduleScalarMultDistributiveWRTModuleAddition_Vect _ _ _) $ moduleScalarMultDistributiveWRTModuleAddition_Mat _ _ _


instance (VerifiedRingWithUnity a) => VerifiedSemigroup (Matrix n m a) where
	semigroupOpIsAssociative = semigroupOpIsAssociative_Mat

instance (VerifiedRingWithUnity a) => VerifiedMonoid (Matrix n m a) where {
	monoidNeutralIsNeutralL = monoidNeutralIsNeutralL_Mat
	monoidNeutralIsNeutralR = monoidNeutralIsNeutralR_Mat
}

instance (VerifiedRingWithUnity a) => VerifiedGroup (Matrix n m a) where {
	groupInverseIsInverseL = groupInverseIsInverseL_Mat
	groupInverseIsInverseR = groupInverseIsInverseR_Mat
}

instance (VerifiedRingWithUnity a) => VerifiedAbelianGroup (Matrix n m a) where {
	abelianGroupOpIsCommutative = abelianGroupOpIsCommutative_Mat
}

instance (VerifiedRingWithUnity a) => VerifiedModule a (Matrix n m a) where {
	moduleScalarMultiplyComposition = moduleScalarMultiplyComposition_Mat
	moduleScalarUnityIsUnity = moduleScalarUnityIsUnity_Mat
	moduleScalarMultDistributiveWRTVectorAddition = moduleScalarMultDistributiveWRTVectorAddition_Mat
	moduleScalarMultDistributiveWRTModuleAddition = moduleScalarMultDistributiveWRTModuleAddition_Mat
}



{-
Trivial identities about (unital) rings.
-}



-- Actually theorems about quasigroups
groupOpIsCancellativeL : VerifiedGroup a => (left, right1, right2 : a) -> left<+>right1 = left<+>right2 -> right1=right2
groupOpIsCancellativeL left right1 right2 pr = trans (sym $ trans (cong {f=(<+>right1)} $ groupInverseIsInverseR left) $ monoidNeutralIsNeutralR right1) $ trans (trans (sym $ semigroupOpIsAssociative (inverse left) left right1) $ trans (cong {f=((inverse left)<+>)} pr) $ semigroupOpIsAssociative (inverse left) left right2) $ trans (cong {f=(<+>right2)} $ groupInverseIsInverseR left) $ monoidNeutralIsNeutralR right2
groupOpIsCancellativeR : VerifiedGroup a => (left1, left2, right : a) -> left1<+>right = left2<+>right -> left1=left2
groupOpIsCancellativeR left1 left2 right pr = trans (sym $ trans (cong {f=(left1<+>)} $ groupInverseIsInverseL right) $ monoidNeutralIsNeutralL left1) $ trans (trans (semigroupOpIsAssociative left1 right (inverse right)) $ trans (cong {f=(<+>(inverse right))} pr) $ sym $ semigroupOpIsAssociative left2 right (inverse right)) $ trans (cong {f=(left2<+>)} $ groupInverseIsInverseL right) $ monoidNeutralIsNeutralL left2

groupElemOwnDoubleImpliesNeut : VerifiedGroup a => (x : a) -> x<+>x=x -> x = Algebra.neutral
groupElemOwnDoubleImpliesNeut x pr = groupOpIsCancellativeL x x Algebra.neutral $ trans pr $ sym $ monoidNeutralIsNeutralL x

ringNeutralIsMultZeroL : VerifiedRing a => (x : a) -> Algebra.neutral <.> x = Algebra.neutral
ringNeutralIsMultZeroL x = groupElemOwnDoubleImpliesNeut (Algebra.neutral <.> x) $ trans (sym $ ringOpIsDistributiveR Algebra.neutral Algebra.neutral x) $ cong {f=(<.>x)} $ monoidNeutralIsNeutralL Algebra.neutral
ringNeutralIsMultZeroR : VerifiedRing a => (x : a) -> x <.> Algebra.neutral = Algebra.neutral
ringNeutralIsMultZeroR x = groupElemOwnDoubleImpliesNeut (x <.> Algebra.neutral) $ trans (sym $ ringOpIsDistributiveL x Algebra.neutral Algebra.neutral) $ cong {f=(x<.>)} $ monoidNeutralIsNeutralL Algebra.neutral

ringNegationCommutesWithLeftMult : VerifiedRing a => (left, right : a) -> left<.>(inverse right) = inverse $ left<.>right
ringNegationCommutesWithLeftMult left right = groupOpIsCancellativeR (left<.>(inverse right)) (inverse $ left<.>right) (left<.>right) $ trans (trans (sym $ ringOpIsDistributiveL left (inverse right) right) $ trans (cong {f=(left<.>)} $ groupInverseIsInverseR right) $ ringNeutralIsMultZeroR left) $ sym $ groupInverseIsInverseR $ left<.>right

ringNegationCommutesWithRightMult : VerifiedRing a => (left, right : a) -> (inverse left)<.>right = inverse $ left<.>right
ringNegationCommutesWithRightMult left right = groupOpIsCancellativeR ((inverse left)<.>right) (inverse $ left<.>right) (left<.>right) $ trans (trans (sym $ ringOpIsDistributiveR (inverse left) left right) $ trans (cong {f=(<.>right)} $ groupInverseIsInverseR left) $ ringNeutralIsMultZeroL right) $ sym $ groupInverseIsInverseR $ left<.>right
