module Data.Matrix.ZZVerified

import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module
import Classes.Verified -- definition of verified algebras other than modules
import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20
import Data.Matrix.AlgebraicVerified

import Data.Vect.Structural
import Data.Matrix.Structural

import Data.ZZ
import Control.Algebra.ZZVerifiedInstances

-- import Data.Matrix.LinearCombinations ( timesVectMatAsHeadTail_ByTransposeElimination )
import Data.Matrix.LinearCombinations



{-
Identities whose proof is particular to ZZ.
-}



{-
-- More instance collisions prevent a proof. (<:>) invokes a (neutral) for the ring which differs from (the a Algebra.neutral).

ringVecNeutralIsVecPtwiseProdZeroL : VerifiedRing a => (xs : Vect n a) -> xs <:> (the (Vect n a) Algebra.neutral) = the a Algebra.neutral
ringVecNeutralIsVecPtwiseProdZeroL [] {a} = Refl
ringVecNeutralIsVecPtwiseProdZeroL (x::xs) = vecHeadtailsEq (ringNeutralIsMultZeroL x) $ ringVecNeutralIsVecPtwiseProdZeroL xs

ringVecNeutralIsVecPtwiseProdZeroR : VerifiedRing a => (xs : Vect n a) -> (the (Vect n a) Algebra.neutral) <:> xs = the a Algebra.neutral
ringVecNeutralIsVecPtwiseProdZeroR [] {a} = Refl
ringVecNeutralIsVecPtwiseProdZeroR (x::xs) = vecHeadtailsEq (ringNeutralIsMultZeroR x) $ ringVecNeutralIsVecPtwiseProdZeroR xs

matVecMultIsVecTransposeMult : Ring a => (v : Vect n a) -> (xs : Matrix n m a) -> v <\> xs = (transpose xs) </> v

ringVecNeutralIsMatVecMultZero : VerifiedRing a => (xs : Matrix n m a) -> xs </> Algebra.neutral = Algebra.neutral
ringVecNeutralIsMatVecMultZero [] = Refl
ringVecNeutralIsMatVecMultZero (x::xs) = vecHeadtailsEq (ringVecNeutralIsVecPtwiseProdZeroR x) $ ringVecNeutralIsMatVecMultZero xs

ringVecNeutralIsVecMatMultZero : VerifiedRing a => (xs : Matrix n m a) -> Algebra.neutral <\> xs = Algebra.neutral
ringVecNeutralIsVecMatMultZero xs = trans (vecMatMultTransposeEq Algebra.neutral xs) $ ringVecNeutralIsMatVecMultZero $ transpose xs
-}

zzVecNeutralIsVecPtwiseProdZeroL : (xs : Vect n ZZ) -> xs <:> Algebra.neutral = Algebra.neutral
zzVecNeutralIsVecPtwiseProdZeroL [] = Refl
-- zzVecNeutralIsVecPtwiseProdZeroL (x::xs) = vecHeadtailsEq (ringNeutralIsMultZeroR x) $ zzVecNeutralIsVecPtwiseProdZeroL xs

zzVecNeutralIsVecPtwiseProdZeroR : (xs : Vect n ZZ) -> Algebra.neutral <:> xs = Algebra.neutral
zzVecNeutralIsVecPtwiseProdZeroR [] = Refl
-- zzVecNeutralIsVecPtwiseProdZeroR (x::xs) = vecHeadtailsEq (ringNeutralIsMultZeroL x) $ zzVecNeutralIsVecPtwiseProdZeroR xs

zzVecNeutralIsVecMatMultZero : (xs : Matrix n m ZZ) -> Algebra.neutral <\> xs = Algebra.neutral
zzVecNeutralIsVecMatMultZero xs {m=Z} = zeroVecEq
zzVecNeutralIsVecMatMultZero xs {m=S predm} = trans timesVectMatAsHeadTail_ByTransposeElimination $ vecHeadtailsEq (zzVecNeutralIsVecPtwiseProdZeroR $ map Vect.head xs) $ zzVecNeutralIsVecMatMultZero $ map Vect.tail xs

zzVecNeutralIsMatVecMultZero : (xs : Matrix n m ZZ) -> xs </> Algebra.neutral = Algebra.neutral
zzVecNeutralIsMatVecMultZero xs = trans (matVecMultIsVecTransposeMult Algebra.neutral xs) $ zzVecNeutralIsVecMatMultZero (transpose xs)

zzVecNeutralIsNeutralL : (l : Vect n ZZ) -> l<+>Algebra.neutral=l
-- zzVecNeutralIsNeutralL = monoidNeutralIsNeutralL

zzVecNeutralIsNeutralR : (r : Vect n ZZ) -> Algebra.neutral<+>r=r
-- zzVecNeutralIsNeutralR = monoidNeutralIsNeutralR

zzVecScalarUnityIsUnity : (v : Vect n ZZ) -> (Algebra.unity {a=ZZ}) <#> v = v
-- zzVecScalarUnityIsUnity = moduleScalarUnityIsUnity
