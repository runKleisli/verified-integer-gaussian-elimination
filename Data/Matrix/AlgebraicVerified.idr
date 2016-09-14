module Data.Matrix.AlgebraicVerified

import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module
import Classes.Verified -- definition of verified algebras other than modules
import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20



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
* Apparently the verified module instance for Vect n ZZ already exists.
-}



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



instance (VerifiedRingWithUnity a) => VerifiedSemigroup (Matrix n m a) where
	semigroupOpIsAssociative = ?semigroupOpIsAssociative_Mat

instance (VerifiedRingWithUnity a) => VerifiedMonoid (Matrix n m a) where {
	monoidNeutralIsNeutralL = ?monoidNeutralIsNeutralL_Mat
	monoidNeutralIsNeutralR = ?monoidNeutralIsNeutralR_Mat
}

instance (VerifiedRingWithUnity a) => VerifiedGroup (Matrix n m a) where {
	groupInverseIsInverseL = ?groupInverseIsInverseL_Mat
	groupInverseIsInverseR = ?groupInverseIsInverseR_Mat
}

instance (VerifiedRingWithUnity a) => VerifiedAbelianGroup (Matrix n m a) where {
	abelianGroupOpIsCommutative = ?abelianGroupOpIsCommutative_Mat
}

instance (VerifiedRingWithUnity a) => VerifiedModule a (Matrix n m a) where {
	moduleScalarMultiplyComposition = ?moduleScalarMultiplyComposition_Vect
	moduleScalarUnityIsUnity = ?moduleScalarUnityIsUnity_Mat
	moduleScalarMultDistributiveWRTVectorAddition = ?moduleScalarMultDistributiveWRTVectorAddition_Mat
	moduleScalarMultDistributiveWRTModuleAddition = ?moduleScalarMultDistributiveWRTModuleAddition_Mat
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
groupElemOwnDoubleImpliesNeut x pr = groupOpIsCancellativeL x x neutral $ trans pr $ sym $ monoidNeutralIsNeutralL x

{-
This proof avoided to make proving (ringNegationCommutesWithLeftMult) easier, since this proof depends on it when it's easier for it to depend on (ringNeutralIsMultZeroL).

---

ringNeutralIsMultZeroL : VerifiedRing a => (x : a) -> Algebra.neutral <.> x = Algebra.neutral
ringNeutralIsMultZeroL x = neutral<.>x = (x <+> inverse x)<.>x = (x<.>x)<+>((inverse x)<.>x) = (x<.>x)<+>(inverse $ x<.>x) = neutral

---

ringNeutralIsMultZeroL x =
	Algebra.neutral<.>x	={ cong {f=(<.>x)} $ sym $ groupInverseIsInverseL x }=
	(x <+> inverse x)<.>x	={ ringOpIsDistributiveR x (inverse x) x }=
	(x<.>x)<+>((inverse x)<.>x) ={ cong {f=((x<.>x)<+>)} $ ringNegationCommutesWithRightMult x x }=
	(x<.>x)<+>(inverse $ x<.>x) ={ groupInverseIsInverseL (x<.>x) }=
	Algebra.neutral	QED

---

ringNeutralIsMultZeroL : VerifiedRing a => (x : a) -> Algebra.neutral <.> x = Algebra.neutral
ringNeutralIsMultZeroL x =
	trans ( cong {f=(<.>x)} $ sym $ groupInverseIsInverseL x ) $
	trans ( ringOpIsDistributiveR x (inverse x) x ) $
	trans ( cong {f=((x<.>x)<+>)} $ ringNegationCommutesWithRightMult x x ) $
	groupInverseIsInverseL (x<.>x)

ringNeutralIsMultZeroR : VerifiedRing a => (x : a) -> x <.> Algebra.neutral = Algebra.neutral
ringNeutralIsMultZeroR x =
	trans ( cong {f=(x<.>)} $ sym $ groupInverseIsInverseL x ) $
	trans ( ringOpIsDistributiveL x x (inverse x) ) $
	trans ( cong {f=((x<.>x)<+>)} $ ringNegationCommutesWithLeftMult x x ) $
	groupInverseIsInverseL (x<.>x)
-}

ringNeutralIsMultZeroL : VerifiedRing a => (x : a) -> Algebra.neutral <.> x = Algebra.neutral
ringNeutralIsMultZeroL x = groupElemOwnDoubleImpliesNeut (Algebra.neutral <.> x) $ trans (sym $ ringOpIsDistributiveR Algebra.neutral Algebra.neutral x) $ cong {f=(<.>x)} $ monoidNeutralIsNeutralL Algebra.neutral
ringNeutralIsMultZeroR : VerifiedRing a => (x : a) -> x <.> Algebra.neutral = Algebra.neutral
ringNeutralIsMultZeroR x = groupElemOwnDoubleImpliesNeut (x <.> Algebra.neutral) $ trans (sym $ ringOpIsDistributiveL x Algebra.neutral Algebra.neutral) $ cong {f=(x<.>)} $ monoidNeutralIsNeutralL Algebra.neutral

ringNegationCommutesWithLeftMult : VerifiedRing a => (left, right : a) -> left<.>(inverse right) = inverse $ left<.>right
ringNegationCommutesWithLeftMult left right = groupOpIsCancellativeR (left<.>(inverse right)) (inverse $ left<.>right) (left<.>right) $ trans (trans (sym $ ringOpIsDistributiveL left (inverse right) right) $ trans (cong {f=(left<.>)} $ groupInverseIsInverseR right) $ ringNeutralIsMultZeroR left) $ sym $ groupInverseIsInverseR $ left<.>right

ringNegationCommutesWithRightMult : VerifiedRing a => (left, right : a) -> (inverse left)<.>right = inverse $ left<.>right
ringNegationCommutesWithRightMult left right = groupOpIsCancellativeR ((inverse left)<.>right) (inverse $ left<.>right) (left<.>right) $ trans (trans (sym $ ringOpIsDistributiveR (inverse left) left right) $ trans (cong {f=(<.>right)} $ groupInverseIsInverseR left) $ ringNeutralIsMultZeroL right) $ sym $ groupInverseIsInverseR $ left<.>right
