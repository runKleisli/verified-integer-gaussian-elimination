module Data.Matrix.ZZVerified

import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module
import Classes.Verified -- definition of verified algebras other than modules
import Control.Algebra.DiamondInstances
import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20
import Data.Matrix.AlgebraicVerified

import Data.Vect.Structural
import Data.Matrix.Structural

import Data.ZZ
import Control.Algebra.ZZVerifiedInstances

-- import Data.Matrix.LinearCombinations ( timesVectMatAsHeadTail_ByTransposeElimination )
import Data.Matrix.LinearCombinations

%default total



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

zzVecNeutralIsVecPtwiseProdZeroL :
	(xs : Vect n ZZ)
	-> xs <:> Algebra.neutral = Algebra.neutral
zzVecNeutralIsVecPtwiseProdZeroL [] = Refl
zzVecNeutralIsVecPtwiseProdZeroL (x::xs) =
	trans ( foldrImplRec (<+>) (Pos 0) id
		(x <.> Algebra.neutral)
		(zipWith (<.>) xs Algebra.neutral) )
	$ trans ( rewrite ringNeutralIsMultZeroR x in monoidNeutralIsNeutralR _ )
	$ zzVecNeutralIsVecPtwiseProdZeroL xs
{-
Couldn't do this:

> zzVecNeutralIsVecPtwiseProdZeroL (x::xs) = vecHeadtailsEq (ringNeutralIsMultZeroR x) $ zzVecNeutralIsVecPtwiseProdZeroL xs

Discovered this proof by ordered inspection following this proof script:

ZZVerified.zzVecNeutralIsVecPtwiseProdZeroL' = proof
  intros
  let pr' = zzVecNeutralIsVecPtwiseProdZeroL xs
  exact _ pr'
  compute
  intro computedPr
  exact trans _ computedPr
  -- The script thusfar makes it possible to identify the missing theorem.
  exact trans ( foldrImplRec (<+>) (Pos 0) id (x <.> Algebra.neutral) (zipWith (<.>) xs Algebra.neutral) ) $ _
  compute
  rewrite sym $ ringNeutralIsMultZeroR x
  exact monoidNeutralIsNeutralR _
-}

zzVecNeutralIsVecPtwiseProdZeroR : (xs : Vect n ZZ) -> Algebra.neutral <:> xs = Algebra.neutral
zzVecNeutralIsVecPtwiseProdZeroR [] = Refl
zzVecNeutralIsVecPtwiseProdZeroR (x::xs) =
	trans ( foldrImplRec (<+>) (Pos 0) id
		(Algebra.neutral <.> x)
		(zipWith (<.>) Algebra.neutral xs) )
	$ trans ( rewrite ringNeutralIsMultZeroL x in monoidNeutralIsNeutralR _ )
	$ zzVecNeutralIsVecPtwiseProdZeroR xs

zzVecNeutralIsVecMatMultZero : (xs : Matrix n m ZZ) -> Algebra.neutral <\> xs = Algebra.neutral
zzVecNeutralIsVecMatMultZero xs {m=Z} = zeroVecEq
zzVecNeutralIsVecMatMultZero xs {m=S predm} = trans timesVectMatAsHeadTail_ByTransposeElimination $ vecHeadtailsEq (zzVecNeutralIsVecPtwiseProdZeroR $ map Vect.head xs) $ zzVecNeutralIsVecMatMultZero $ map Vect.tail xs

zzVecNeutralIsMatVecMultZero : (xs : Matrix n m ZZ) -> xs </> Algebra.neutral = Algebra.neutral
zzVecNeutralIsMatVecMultZero xs = trans (matVecMultIsVecTransposeMult Algebra.neutral xs) $ zzVecNeutralIsVecMatMultZero (transpose xs)

zzVecNeutralIsNeutralL : (l : Vect n ZZ) -> l<+>Algebra.neutral=l
zzVecNeutralIsNeutralL = monoidNeutralIsNeutralL_Vect

zzVecNeutralIsNeutralR : (r : Vect n ZZ) -> Algebra.neutral<+>r=r
zzVecNeutralIsNeutralR = monoidNeutralIsNeutralR_Vect

zzVecScalarUnityIsUnity : (v : Vect n ZZ) -> (Algebra.unity {a=ZZ}) <#> v = v
zzVecScalarUnityIsUnity = moduleScalarUnityIsUnity_Vect
