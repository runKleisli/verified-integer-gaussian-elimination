module Control.Algebra.ZZVerifiedInstances
-- We will forego treating this as Control.Algebra.NumericVerifiedInstances

import Data.ZZ
import Control.Algebra
import Classes.Verified
import Control.Algebra.NumericInstances

-- These can be proven through an isomorphism with the free ring on the empty type.

instance VerifiedSemigroup ZZ where
	semigroupOpIsAssociative = ?semigroupOpIsAssociative_ZZ

instance VerifiedMonoid ZZ where {
	monoidNeutralIsNeutralL = ?monoidNeutralIsNeutralL_ZZ
	monoidNeutralIsNeutralR = ?monoidNeutralIsNeutralR_ZZ
}

instance VerifiedGroup ZZ where {
	groupInverseIsInverseL = ?groupInverseIsInverseL_ZZ
	groupInverseIsInverseR = ?groupInverseIsInverseR_ZZ
}

instance VerifiedAbelianGroup ZZ where {
	abelianGroupOpIsCommutative = ?abelianGroupOpIsCommutative_ZZ
}

instance VerifiedRing ZZ where {
	ringOpIsAssociative = ?ringOpIsAssociative_ZZ
	ringOpIsDistributiveL = ?ringOpIsDistributiveL_ZZ
	ringOpIsDistributiveR = ?ringOpIsDistributiveR_ZZ
}

instance VerifiedRingWithUnity ZZ where {
	ringWithUnityIsUnityL = ?ringWithUnityIsUnityL_ZZ
	ringWithUnityIsUnityR = ?ringWithUnityIsUnityR_ZZ
}
