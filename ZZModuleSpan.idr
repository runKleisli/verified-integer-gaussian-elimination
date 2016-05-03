module ZZModuleSpan

import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module
import Classes.Verified -- definition of verified algebras other than modules
import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20

import Data.ZZ
import Control.Algebra.NumericInstances



monoidsum : (Foldable t, Monoid a) => t a -> a
{-
-- Idris version 0.9.18
monoidsum = Control.Algebra.sum
-}
-- Idris version 0.9.20
monoidsum = sum'
--



{-
Trivial theorems
-}



total
zeroVecEq : {a : Vect 0 r} -> {b : Vect 0 r} -> a = b
zeroVecEq {a=[]} {b=[]} = Refl



total
vecSingletonReplicateEq : ((u : a) -> v=u) -> (xs : Vect n a) -> (xs = replicate n v)
vecSingletonReplicateEq f [] = Refl
vecSingletonReplicateEq f (x::xs) {v} = rewrite sym (f x) in cong {f=(v::)} (vecSingletonReplicateEq f xs)



total
zeroVecVecId : (xs : Vect n (Vect 0 a)) -> (xs = replicate n [])
zeroVecVecId = vecSingletonReplicateEq (\b => zeroVecEq {a=[]} {b=b})



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
ZZ is a VerifiedRing.
-}



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

zippyScale : Matrix n' n ZZ -> Matrix n w ZZ -> Matrix n' w ZZ
zippyScale = (<>)

-- Goal here : show that (<>) satisfies the property that the first argument scales the vectors of the second argument in n' various ways.
-- This proof is only a hint at our reason for using (<>) to implement linear combination.
-- Thus, it is a proof for the humans that the definition of linear combination as matrix multiplication is satisfactory, not for the computers.
-- We could have some sort of `because`:=`const` to annotate, though it adds overhead.
zippyIntermed : Vect n ZZ -> Matrix n w ZZ -> Vect w ZZ
zippyIntermed = (<\>)

zippyThm1 : (vs : Matrix (S n') n ZZ) -> (xs : Matrix n w ZZ) -> Data.Vect.head (vs <> xs) = (Data.Vect.head vs) <\> xs

zippyLemA : (the (Vect 0 ZZ) []) <\> (the (Matrix 0 w ZZ) []) = replicate w (Pos 0)
zippyLemA {w = Z} = Refl
zippyLemA {w = S n} = ?zippyLemA_induct
zippyLemA_induct = proof
	intro
	exact (cong zippyLemA)
zippyLemB : replicate w (Pos 0) = monoidsum (zipWith (<#>) (the (Vect 0 ZZ) []) (the (Matrix 0 w ZZ) []))
zippyLemB {w = Z} = Refl
zippyLemB {w = S n} = ?zippyLemB_induct
zippyLemB_induct = proof
	intro
	exact (cong zippyLemB)

{-
-- The following proofs are a matter of making a readable train of thought behind the proof details. That is, they explain why one expects the illegible final goal to be solved in the efficient way that it is.

zippyLemC : {predw : Nat} -> (z::[]) <\> ((x0::x0s) :: []) = map (\ARG => ((z::[]) <:> ARG)) $ zipWith (::) ( the (Vect (S predw) ZZ) (x0::x0s) ) (replicate (S predw) [])
zippyLemC = Refl

zippyLemD : map (\ARG => ((z::[]) <:> ARG)) $ zipWith (::) ( the (Vect (S predw) ZZ) (x0::x0s) ) (replicate (S predw) []) = ?zippyLemD_recurse
zippyLemD = Refl

zippyLemD_recurse = proof
  intros
  let headterm = head $ zipWith (Data.Vect.(::)) ( the (Vect (S predw) ZZ) (x0::x0s) ) (replicate (S predw) [])
  let tailterm = tail $ zipWith (Data.Vect.(::)) ( the (Vect (S predw) ZZ) (x0::x0s) ) (replicate (S predw) [])
  exact ( ((z::[])<:>headterm) :: map (\ARG => ( (z::[]) <:> ARG )) tailterm )

zippyLemE : map (\ARG => ((z::[]) <:> ARG)) $ zipWith (::) ( the (Vect (S predw) ZZ) (x0::x0s) ) (replicate (S predw) []) = ?zippyLemE_recurse
zippyLemE = Refl

-- Same as zippyLemD_recurse, but expanding the head and tail of the list made with (zipWith (::))
zippyLemE_recurse = proof
  intros
  let headterm = Data.Vect.(::) x0 []
  let tailterm = zipWith (Data.Vect.(::)) ( the (Vect predw ZZ) x0s ) (replicate predw [])
  exact ( ((z::[])<:>headterm) :: map (\ARG => ( (z::[]) <:> ARG )) tailterm )

zippyLemFnHalf : (z::[]) <:> (Data.Vect.(::) (the ZZ x0) []) = z*x0
zippyLemFnHalf {z} {x0} = plusZeroRightNeutralZ (multZ z x0)

zippyLemF : map (\ARG => ((z::[]) <:> ARG)) $ zipWith (::) ( the (Vect (S predw) ZZ) (x0::x0s) ) (replicate (S predw) []) = z*x0 :: ( map (\ARG => ( (z::[]) <:> ARG )) $ zipWith (::) ( the (Vect predw ZZ) x0s ) (replicate predw []) )
zippyLemF = ?zippyLemF'

zippyLemF' = proof
  intros
  rewrite sym zippyLemE
  exact cong {f=(:: ( map (\ARG => ( (z::[]) <:> ARG )) $ zipWith (::) ( the (Vect predw ZZ) x0s ) (replicate predw []) ))} zippyLemFnHalf
  -- Junk holes that were generated by the interactive prover
  -- Errors are like "Can't infer argument predw to S, Can't infer argument z to zippyLemE". w.r.t. "Can't infer argument predw to zipWith", this may explain why the (Data.Vect) namespace must be explicitly stated for zipWith.
  exact Z
  exact []
  exact (Pos 0)
  exact (Pos 0)

zippyLemG : {z : ZZ} -> (z::[]) <\> ((x0::x0s) :: []) = z*x0 :: ( (z::[]) <\> (x0s::[]) )
zippyLemG = zippyLemF

zippyLemG_nullcaseforH : {z : ZZ} -> (z::[]) <\> ([] :: []) = []
zippyLemG_nullcaseforH = Refl
-}

{-
	zippyLemG {z=z} {x0=x0} {x0s=x0s}

and

	the (map (z*) (x0::x0s) = z*x0::(x0::x0s)) Refl

were not needed at all for zippyLemH.
-}

-- See comment atop zippyLemA through zippyLemG
zippyLemH : {z : ZZ} -> (xs : Vect w ZZ) -> (z::[]) <\> (the (Matrix 1 w ZZ) (xs :: [])) = map (z*) xs
zippyLemH [] = Refl
zippyLemH {z} (x0::x0s) = ?zippyLemH'
zippyLemH' = proof
  intros
  rewrite sym (plusZeroRightNeutralZ (multZ z x0))
  exact (cong (zippyLemH x0s))

-- See comment atop zippyLemA through zippyLemG
-- Proof is of the same form as zippyLemH, and suggested by its success.
zippyLemI : {z : ZZ} -> (xs : Vect w ZZ) -> map (z*) xs = monoidsum (Data.Vect.zipWith (<#>) (z::[]) (xs::[]))
zippyLemI [] = Refl
zippyLemI {z} (x0::x0s) = ?zippyLemI'
zippyLemI' = proof
  intros
  rewrite sym (plusZeroRightNeutralZ (multZ z x0))
  exact (cong (zippyLemI x0s))

zippyLemJ : {z : ZZ} -> (xs : Vect w ZZ) -> (z::[]) <\> (the (Matrix 1 w ZZ) (xs :: [])) =  monoidsum (Data.Vect.zipWith (<#>) (z::[]) (xs::[]))
zippyLemJ xs = trans (zippyLemH xs) (zippyLemI xs)

-- Modeled after zippyLemH
{-
zippyLemK : {z : ZZ} -> {predn : Nat} -> (xs : Vect w ZZ) -> (z::zs) <\> (the (Matrix (S predn) w ZZ) (xs :: xss)) = ?lemKTy -- ?lemKfunc (map (z*) xs) ((z::zs) <\> xss)
-}

{-
!!!!!!!!!!!
~~~~~~~~~~~
Type checker fails to identify from the general case that it is impossible to satisfy zippyLemL in general, since it is impossible to satisfy it in the case w=1.
~~~~~~~~~~~
!!!!!!!!!!!
-}

-- Used to figure out how to prove zippyLemL, of which this is a special case.
zippyLemL_Mini : {z : ZZ} -> (xs : Vect 1 ZZ) -> (map (z*) xs)::( monoidsum (Data.Vect.zipWith (<#>) zs xss) ) = monoidsum (Data.Vect.zipWith (<#>) (z::zs) (xs::xss))
zippyLemL_Mini (x::[]) = ?zippyLemMini_rhs

-- Modeled after zippyLemI
-- Raises a type error if you set w to 1.
zippyLemL : {z : ZZ} -> (xs : Vect w ZZ) -> (map (z*) xs)++( monoidsum (Data.Vect.zipWith (<#>) zs xss) ) = monoidsum (Data.Vect.zipWith (<#>) (z::zs) (xs::xss))
zippyLemL [] = ?zippyLemL_rhs_1
{-
-- This claimed proof doesn't have to be valid. In particular, it's probably not, but it shows you what the theorem should degenerate to in the case (xs=[]).

zippyLemL_rhs_1 = proof
  intros
  rewrite (zeroVecVecId xss)
  claim lem_unfunction ( (\x => Data.Vect.zipWith (\meth1 => \meth2 => plusZ meth1 meth2) [] x) = id )
  unfocus
  rewrite sym lem_unfunction
  exact Refl
  exact ?lem_unfunction_tbContd
-}
zippyLemL (x0::x0s) = ?zippyLemL_rhs_2

zippyThm2 : (v : Vect n ZZ) -> (xs : Matrix n w ZZ) -> ( v <\> xs = monoidsum (zipWith (<#>) v xs) )
zippyThm2 [] [] = trans zippyLemA zippyLemB
zippyThm2 (z::zs) ([] :: xs) = zeroVecEq
{-
Have to reduce this to an intermediate theorem inductive in x@(x0::x0s), reducing to describing the effect of multiplying by z.

Actually, showing each side reduces to what's basically (z*) would be proof enough.

Breaking z up into different cases of ZZ value may be sufficient to force a full automation of the proof. However, this loses generality across the ring of coefficients.
-}
zippyThm2 (z::[]) (xs :: []) = zippyLemJ xs
zippyThm2 (z :: (zt::zts)) ((x0::x0s) :: (xt::xts)) = ?zippyThm2_rhs_2
-- zippyThm2 = ?zippyThm2Pr
{-
Beginnings of a substitution proof... abandoned cause nontrivial to look at.
Should probably just use induction, splitting the cases automatically.

zippyThm2 = ?zippyThm2Pr
	where
		eq1 : v <\> xs = map (\ARG => (v <:> ARG)) (transpose xs)
		eq2 : ( \v => \xs => map (\ARG => (v <:> ARG)) (transpose xs) ) = ( \v => \xs => map (\ARG => (v (foldr (<+>) neutral (zipWith (<.>) w v)) ARG)) (transpose xs) )
		eq2 = cong {f=\k => \v => \xs => map (\ARG => (v `k` ARG)) (transpose xs)} Refl
		eq3 : map (\ARG => (v (foldr (<+>) neutral (zipWith (<.>) w v)) ARG)) (transpose xs) = map (\ARG => (v (monoidsum (zipWith (<.>) w v)) ARG)) (transpose xs)
-}
{-
Evidence for zippyThm2:

sum' = foldr (<+>) neutral
(w <:> v) = foldr (<+>) neutral (zipWith (<.>) w v)
(r <\> m) = map (\ARG => (r <:> ARG)) (transpose m)
-}

{-
Labels (xs, ys) aren't depended on for values, they're just hints, used cause

	%name Matrix xs, ys

doesn't work.

Type must be given by a proof, because

	spanslz : {n : Nat} -> {n' : Nat} -> (xs : Matrix n w ZZ) -> (ys : Matrix n' w ZZ) -> Type
	spanslz {n} {n'} xs ys = (vs : Matrix n' n ZZ ** vs `zippyScale` xs = ys)

alone will just split the (n, n') in the declaration / theorem stmt from some n'1 in the definition / proof.
-}
spanslz : (xs : Matrix n w ZZ) -> (ys : Matrix n' w ZZ) -> Type
spanslz = ?spanslz'
spanslz' = proof
	intros
	exact (vs : Matrix n' n ZZ ** vs `zippyScale` xs = ys)
{- spanslz {n} {n'} xs ys = (vs : Matrix n' n ZZ ** vs `zippyScale` xs = ys) -}



{-
Proof of relational properties of span

i.e.,
Relational: equivalence relation axioms
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

{-
spanslztrans : {n : Nat} -> {n' : Nat} -> {xs : Matrix n m ZZ} -> {ys : Matrix n' m ZZ} -> spanslz xs ys -> spanslz ys zs -> spanslz xs zs
-- spanslztrans (vsx ** prvsx) (vsy ** prvsy) = ?spanslztransPr
spanslztrans {n} {n'} {xs} {ys} (vsx ** prvsx) (vsy ** prvsy) = ( the (Vect n' (Vect n ZZ)) _ ** rewrite sym prvsx in prvsy )
-}
