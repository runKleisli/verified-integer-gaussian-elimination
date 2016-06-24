module ZZModuleSpan

import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module
import Classes.Verified -- definition of verified algebras other than modules
import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20
import Data.Matrix.LinearCombinations

import Data.ZZ
import Control.Algebra.NumericInstances



{-
Trivial lemmas
-}

vecHeadtailsEq : {xs,ys : Vect _ _} -> ( headeq : x = y ) -> ( taileq : xs = ys ) -> x::xs = y::ys
vecHeadtailsEq {x} {xs} {ys} headeq taileq = trans (vectConsCong x xs ys taileq) $ cong {f=(::ys)} headeq
-- Also a solid proof:
-- vecHeadtailsEq {x} {xs} {ys} headeq taileq = trans (cong {f=(::xs)} headeq) $ replace {P=\l => l::xs = l::ys} headeq $ vectConsCong x xs ys taileq

multIdLeftNeutral : VerifiedRingWithUnity r => (a : Matrix _ _ r) -> Id <> a = a

multIdRightNeutral : VerifiedRingWithUnity r => (a : Matrix _ _ r) -> a <> Id = a



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
Definition:
* Monoid/VerifiedMonoid instance matTimesMonoid/matTimesVerMonoid for matrix multiplication
As desired in Data.Matrix.Algebraic

-----

When checking right hand side of matTimesVerSemigroup' with expected type
        VerifiedSemigroup (Vect n (Vect n r))

Can't resolve type class Semigroup (Vect n (Vect n r))

-----

instance [matTimesSemigroup] Ring r => Semigroup (Matrix n n r) where {}

matTimesMonoid : Ring r => with matTimesSemigroup (Monoid (Matrix n n r))
matTimesMonoid {r} {n} = ?matTimesMonoid'

matTimesVerSemigroup : VerifiedRing r => with matTimesSemigroup (VerifiedSemigroup (Matrix n n r))
matTimesVerSemigroup {r} {n} = matTimesVerSemigroup'
	where
		instance [matTimesVerSemigroup'] VerifiedSemigroup (Matrix n n r) where {
				semigroupOpIsAssociative = ?semigroupOpIsAssociative_matTimesVerSemigroup
			}

matTimesVerMonoid : VerifiedRing r => with matTimesVerSemigroup (VerifiedMonoid (Matrix n n r))
matTimesVerMonoid {r} {n} = matTimesVerMonoid'
	where
		instance [matTimesVerMonoid'] VerifiedMonoid (Matrix n n r) where {
			monoidNeutralIsNeutralL = ?monoidNeutralIsNeutralL_matTimesVerMonoid
			monoidNeutralIsNeutralR = ?monoidNeutralIsNeutralR_matTimesVerMonoid
		}
-}



{-
Associative property for matrix multiplication
-}

timesMatMatIsAssociative : Ring a => {l : Matrix _ _ a} -> {c : Matrix _ _ a} -> {r : Matrix _ _ a} -> l <> (c <> r) = (l <> c) <> r



{-
ZZ is a VerifiedRing.
-}

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



{-
"Spans" relation
-}



{-
When checking right hand side of ZZModuleSpan.spans, scaleBy:
Can't resolve type class Module ZZ a

> spans : VerifiedModule ZZ a => (a : Type) -> (P : a -> Type) -> (Q : a -> Type) -> Type
> spans a pprop qprop = (x : a) -> qprop x -> ( scal : List (Subset a pprop,ZZ) ** (Control.Algebra.sum (map scaleBy scal) = x) )
> 	where
> 		scaleBy : (Subset a pprop,ZZ) -> a
> 		scaleBy (Element v _, r) = r <#> v

----------              Other goals:              ----------
{hole4},{hole3},{hole2},{hole1},{hole0}
----------              Assumptions:              ----------
 a : Type
 constrarg : VerifiedModule ZZ a
 a2 : Type
 P : a2 -> Type
 Q : a2 -> Type
----------                 Goal:                  ----------
{hole5} : Type

> spans : VerifiedModule ZZ a => (a : Type) -> (P : a -> Type) -> (Q : a -> Type) -> Type
> spans = ?pr_spans

So it's the term splitting problem encountered in ClassDataExpers. Solution should be to make class constraint argument a normal argument.
-}

spans : {auto a : Type} -> {auto p : VerifiedModule ZZ a} -> (P : a -> Type) -> (Q : a -> Type) -> Type
spans {a} pprop qprop = (x : a) -> qprop x -> ( scal : List (Subset a pprop,ZZ) ** (monoidsum (map scaleBy scal) = x) )
	where
		scaleBy : (Subset a pprop,ZZ) -> a
		scaleBy (Element v _, r) = r <#> v



{-
Same as above, but for lists of vectors
-}



spansl : VerifiedModule ZZ a => Vect n a -> Vect n' a -> Type
spansl = ?spanslpr
{-
spansl xs ys = (vs : [[ZZ]] ** zipWithShort (<:> xs) vs = ys)
	where zipWithShort f as bs = let len = minimum (length as length bs) in Data.VectType.Vect.zipWith f (take len as) (take len bs)
-}



{-
Same as above, but for lists of ZZ vectors specifically.
-}



rewriteAssociativityUnderEquality : {f, g : a -> a -> a} -> ( (x : a) -> (y : a) -> f x y = g x y) -> (l `f` (c `f` r) = (l `f` c) `f` r) -> (l `g` (c `g` r) = (l `g` c) `g` r)

zippyScale : Matrix n' n ZZ -> Matrix n w ZZ -> Matrix n' w ZZ
zippyScale vs xs = map (\zs => monoidsum $ zipWith (<#>) zs xs) vs

-- Inherited properties from (<>) equality proven in Data.Matrix.LinearCombinations
zippyScaleIsAssociative : l `zippyScale` (c `zippyScale` r) = (l `zippyScale` c) `zippyScale` r
{-
zippyScaleIsAssociative = ?zippyScaleIsAssociative'
-- zippyScaleIsAssociative = rewriteAssociativityUnderEquality timesMatMatAsMultipleLinearCombos
-}
zippyScaleIsAssociative_squaremats : {l, c, r : Matrix n n ZZ} -> l `zippyScale` (c `zippyScale` r) = (l `zippyScale` c) `zippyScale` r
-- zippyScaleIsAssociative_squaremats = ?zippyScaleIsAssociative_squaremats'
zippyScaleIsAssociative_squaremats {l} {c} {r} {n} = ( rewriteAssociativityUnderEquality {l=l} {c=c} {r=r} {f=(<>)} {g=\varg => \xarg => map (\zs => monoidsum (zipWith (<#>) zs xarg)) varg} (timesMatMatAsMultipleLinearCombos {n'=n} {n=n} {w=n}) ) $ timesMatMatIsAssociative {l=l} {c=c} {r=r}

zippyScaleIdLeftNeutral : (a : Matrix n m ZZ) -> Id `zippyScale` a = a
zippyScaleIdLeftNeutral _ = trans (sym $ timesMatMatAsMultipleLinearCombos _ _) $ multIdLeftNeutral _

zippyScaleIdRightNeutral : (a : Matrix _ _ ZZ) -> a `zippyScale` Id = a
zippyScaleIdRightNeutral _ = trans (sym $ timesMatMatAsMultipleLinearCombos _ _) $ multIdRightNeutral _

{-

Implementations explored:

------------------

zippyScaleIsAssociative {l} {c} {r} = trans (cong {f=zippyScale l} $ sym $ timesMatMatAsMultipleLinearCombos c r) $ trans (sym $ timesMatMatAsMultipleLinearCombos l (c<>r)) $ trans (timesMatMatIsAssociative {l=l} {c=c} {r=r}) $ trans (cong {f=(<> r)} $ timesMatMatAsMultipleLinearCombos l c) $ timesMatMatAsMultipleLinearCombos (l `zippyScale` c) r

------

zippyScaleIsAssociative {l} {c} {r} = trans (cong {f=zippyScale l} $ sym $ timesMatMatAsMultipleLinearCombos c r) $ trans (sym $ timesMatMatAsMultipleLinearCombos l (c<>r)) $ trans (timesMatMatIsAssociative {l=l} {c=c} {r=r}) $ trans (timesMatMatAsMultipleLinearCombos (l <> c) r) $ cong {f=(flip zippyScale) r} $ timesMatMatAsMultipleLinearCombos l c

------

zippyScaleIsAssociative {l} {c} {r} = trans
		( rewrite sym (timesMatMatAsMultipleLinearCombos l (c `zippyScale` r)) in rewrite sym (timesMatMatAsMultipleLinearCombos c r) in timesMatMatIsAssociative {l=l} {c=c} {r=r}
		)
		( rewrite sym (timesMatMatAsMultipleLinearCombos l c) in rewrite sym (timesMatMatAsMultipleLinearCombos (l <> c) r) in timesMatMatIsAssociative {l=l} {c=c} {r=r}
		)

zippyScaleIsAssociative2 : {l : Matrix _ _ ZZ} -> {c : Matrix _ _ ZZ} -> {r : Matrix _ _ ZZ} -> map (\rs => monoidsum $ zipWith (<#>) rs (map (\rs => monoidsum $ zipWith (<#>) rs r) c)) l = map (\rs => monoidsum $ zipWith (<#>) rs r) (map (\rs => monoidsum $ zipWith (<#>) rs c) l)
zippyScaleIsAssociative2 {l} {c} {r} = trans
		( rewrite sym (timesMatMatAsMultipleLinearCombos l (c `zippyScale` r)) in rewrite sym (timesMatMatAsMultipleLinearCombos c r) in timesMatMatIsAssociative {l=l} {c=c} {r=r}
		)
		( rewrite sym (timesMatMatAsMultipleLinearCombos l c) in rewrite sym (timesMatMatAsMultipleLinearCombos (l <> c) r) in timesMatMatIsAssociative {l=l} {c=c} {r=r}
		)
-}



{-
This error seems no more. Cause of switching from 0.9.18 to 0.9.20? Cause of changing the definition of zippyScale to use linear combinations instead of (<>)?

---

Type must be given by a proof, because

	spanslz : {n : Nat} -> {n' : Nat} -> (xs : Matrix n w ZZ) -> (ys : Matrix n' w ZZ) -> Type
	spanslz {n} {n'} xs ys = (vs : Matrix n' n ZZ ** vs `zippyScale` xs = ys)

alone will just split the (n, n') in the declaration / theorem stmt from some n'1 in the definition / proof.

-----

As implemented
Originally problematic
---
spanslz {n} {n'} xs ys = (vs : Matrix n' n ZZ ** vs `zippyScale` xs = ys)

-----

Proof fix
---
spanslz = ?spanslz'
spanslz' = proof
	intros
	exact (vs : Matrix n' n ZZ ** vs `zippyScale` xs = ys)

-----

Alternative fix, untested
---
spanslz {n} {n'} xs ys = (vs : Matrix n' n ZZ ** zippyScale {n'=n'} {n=n} vs xs = ys)

-}
spanslz : (xs : Matrix n w ZZ) -> (ys : Matrix n' w ZZ) -> Type
spanslz {n} {n'} xs ys = (vs : Matrix n' n ZZ ** vs `zippyScale` xs = ys)



{-
Proof of relational properties of span

i.e.,
Relational:
* equivalence relation axioms
* spanned by implies tail spanned by
Algebraic: gcd and lcm divisibility relationships via Bezout's identity
-}



{-
When checking type of ZZModuleSpan.spansTrans:
INTERNAL ERROR: Not an attackable hole
This is probably a bug, or a missing error message.
Please consider reporting at https://github.com/idris-lang/Idris-dev/issues

> spansTrans : spans p q -> spans q r -> spans p r

or

> spansTrans : spans p q -> spans q r -> spans p r
-- with rule / dependent pattern matching
> spansTrans par_orAllxsNrs_prsum par_orAllysNss_prsum = ?prSpansTrans

same applies when the type argument to (spans) is made explicit, not an auto implicit. Should try making the class instance explicit too. On the other hand, it may be because of the missing proof of VerifiedRing for ZZ.
-}

-- spansTrans : spans p q -> spans q r -> spans p r
-- with rule / dependent pattern matching
-- spansTrans par_orAllxsNrs_prsum par_orAllysNss_prsum = ?prSpansTrans



{-
spansltrans : spansl xs ys -> spansl ys zs -> spansl xs zs
spansltrans xs ys
-}



spanslzTail : {xs : Matrix n w ZZ} -> {ys : Matrix (S predn') w ZZ} -> spanslz xs ys -> spanslz xs (Data.Vect.tail ys)
spanslzTail {xs} {ys} (vs ** prvs) = (tail vs ** tailnote)
	where
		tailnote : map (\zs => monoidsum (zipWith (<#>) zs xs)) (tail vs) = tail ys
		tailnote = sym ?tailnote'

tailnote' = proof
  intros
  exact trans (cong {f=Data.Vect.tail} $ sym prvs) _
  rewrite sym $ headtails vs
  exact Refl

spannedlzByZeroId : {xs : Matrix n m ZZ} -> spanslz [] xs -> xs=neutral @{the (Monoid $ Matrix _ _ ZZ) %instance}
spannedlzByZeroId {xs=[]} (vs ** prvs) = Refl
spannedlzByZeroId {xs=x::xs} ((v::vs) ** prvs) = ?spannedlzByZeroId'

spannedlzByZeroId' = proof
  intros
  exact vecHeadtailsEq (trans (sym $ cong {f=head} prvs) _) (spannedlzByZeroId $ spanslzTail ((v::vs)**prvs))
  rewrite sym $ zeroVecEq {a=v} {b=[]}
  exact Refl

{-
-- Works in REPL,
-- if this is a little clearer.
-- Difference is probably in inferring different implicit arguments to vecHeadtailsEq.
spannedlzByZeroId' = proof
  intros
  exact vecHeadtailsEq _ (spannedlzByZeroId $ spanslzTail ((v::vs)**prvs))
  exact trans (sym $ cong {f=head} prvs) _
  -- compute
  rewrite sym $ zeroVecEq {a=v} {b=[]}
  -- compute
  exact Refl
-}



{-
Implicit naturals must be passed to the (spanslz)s in this type signature for the types of (vsx) in (the (spanslz xs ys) (vsx ** prvsx)) and (vsy) in (the (spanslz ys zs) (vsy ** prvsy)) to be inferred, even when these parameters are summoned in the definition.
-}
spanslztrans : {xs : Matrix na m ZZ} -> {ys : Matrix ni m ZZ} -> {zs : Matrix nu m ZZ} -> spanslz {n=na} {n'=ni} xs ys -> spanslz {n=ni} {n'=nu} ys zs -> spanslz xs zs

spanslztrans {na} {ni} {nu} {m} {xs} {ys} {zs} (vsx ** prvsx) (vsy ** prvsy) = ( spanslztrans_matrix ** spanslztrans_linearcombprop )
	where
		spanslztrans_matrix : Matrix nu na ZZ
		spanslztrans_matrix = vsy <> vsx
		spanslztrans_linearcombprop : spanslztrans_matrix `zippyScale` xs = zs
		spanslztrans_linearcombprop = trans (cong {f=(flip zippyScale) xs} $ timesMatMatAsMultipleLinearCombos vsy vsx) $ trans (sym $ zippyScaleIsAssociative {l=vsy} {c=vsx} {r=xs}) $ trans (cong {f=zippyScale vsy} prvsx) prvsy



spanslzrefl : spanslz xs xs
spanslzrefl = ( Id ** zippyScaleIdLeftNeutral _ )
