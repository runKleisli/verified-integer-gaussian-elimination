module ZZModuleSpan

import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module
import Classes.Verified -- definition of verified algebras other than modules

import Data.ZZ
import Control.Algebra.NumericInstances



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



{-
ZZ is a VerifiedRing.
-}



--
