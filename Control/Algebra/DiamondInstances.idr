module Control.Algebra.DiamondInstances

import Control.Algebra
import Classes.Verified -- definition of verified algebras other than modules



{-
Diamond instances
explicitly referenced for using in treating diamond inheritance problems
* VerifiedGroup a -> Semigroup a
* VerifiedRingWithUnity a -> Semigroup a
* VerifiedRingWithUnity a -> Ring a
-}



vgrpVerifiedMonoid : VerifiedGroup a -> VerifiedMonoid a
vgrpVerifiedMonoid a = %instance

vgrpGroup : VerifiedGroup a -> Group a
vgrpGroup a = %instance

vmonSemigrp : VerifiedMonoid a -> Semigroup a
vmonSemigrp a = %instance

grpSemigrp : Group a -> Semigroup a
grpSemigrp a = %instance

vgrpSemigroupByVMon : VerifiedGroup a -> Semigroup a
vgrpSemigroupByVMon = vmonSemigrp . vgrpVerifiedMonoid

vgrpSemigroupByGrp : VerifiedGroup a -> Semigroup a
vgrpSemigroupByGrp = grpSemigrp . vgrpGroup

vrwuSemigroupByVMon : VerifiedRingWithUnity a -> Semigroup a
vrwuSemigroupByVMon a = vgrpSemigroupByVMon %instance

vrwuSemigroupByGrp : VerifiedRingWithUnity a -> Semigroup a
vrwuSemigroupByGrp a = vgrpSemigroupByGrp %instance



vrwuVerifiedRing : VerifiedRingWithUnity a -> VerifiedRing a
vrwuVerifiedRing a = %instance

vrwuRingWithUnity : VerifiedRingWithUnity a -> RingWithUnity a
vrwuRingWithUnity a = %instance

vrRing : VerifiedRing a -> Ring a
vrRing a = %instance

rwuRing : RingWithUnity a -> Ring a
rwuRing a = %instance

vrwuRingByVR : VerifiedRingWithUnity a -> Ring a
vrwuRingByVR = vrRing . vrwuVerifiedRing

vrwuRingByRWU : VerifiedRingWithUnity a -> Ring a
vrwuRingByRWU = rwuRing . vrwuRingWithUnity
