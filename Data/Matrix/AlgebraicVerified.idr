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
