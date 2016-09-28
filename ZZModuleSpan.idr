module ZZModuleSpan

import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module
import Classes.Verified -- definition of verified algebras other than modules
import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20
import Data.Matrix.AlgebraicVerified
import Data.Matrix.LinearCombinations

import Data.ZZ
import Control.Algebra.NumericInstances
import Control.Algebra.ZZVerifiedInstances

import Data.Vect.Structural
-- import Data.Matrix.Structural

import Control.Isomorphism



{-
Trivial lemmas and plumbing
-}

runIso : Iso a b -> a -> b
runIso (MkIso to _ _ _) = to

finReduce : (snel : Fin (S n)) -> Either (Fin n) (FZ = snel)
finReduce FZ = Right Refl
finReduce (FS nel) = Left nel

permDoesntFixAValueNotFixed : (sigma : Iso (Fin n) (Fin n)) -> (nel1, nel2 : Fin n) -> (runIso sigma nel1 = nel2) -> Either (Not (runIso sigma nel2 = nel2)) (nel1 = nel2)
{-
-- Positive form. Not strong enough for our purposes.
permpermFixedImpliesPermFixed : (sigma : Iso (Fin n) (Fin n)) -> (nel : Fin n) -> (runIso sigma nel = runIso sigma $ runIso sigma nel) -> (nel = runIso sigma nel2)
-}

permDoesntFix_corrolary : (sigma : Iso (Fin (S n)) (Fin (S n))) -> (snel : Fin (S n)) -> Not (snel = FZ) -> (runIso sigma snel = FZ) -> Not (runIso sigma FZ = FZ)
permDoesntFix_corrolary sigma snel ab pr = runIso eitherBotRight $ map ab (permDoesntFixAValueNotFixed sigma snel FZ pr)

weakenIsoByValFZ : Iso (Fin (S n)) (Fin (S n)) -> Iso (Fin n) (Fin n)
weakenIsoByValFZ {n} (MkIso to from toFrom fromTo) = MkIso to' from' toFrom' fromTo'
	where
		to' : Fin n -> Fin n
		to' nel = runIso eitherBotRight $ (map ((permDoesntFix_corrolary (MkIso to from toFrom fromTo) (FS nel) (FZNotFS . sym)) . sym) (finReduce $ to $ FS nel)) <*> (map sym $ finReduce $ to FZ)
		from' : Fin n -> Fin n
		from' = ?weakenIsoByValFZ_from_pr
		toFrom' : (y : Fin n) -> to' (from' y) = y
		-- Suggestion: with (to $ FS nel) or perhaps by injectivity of FS.
		toFrom' = ?weakenIsoByValFZ_toFrom_pr
		fromTo' : (x : Fin n) -> from' (to' x) = x
		fromTo' = ?weakenIsoByValFZ_fromTo_pr

-- fromEither {a=Fin n} : Either (Fin n) (Fin n) -> Fin n
-- goal : (finReduce $ to $ FS nel : Either (Fin n) (FZ = to $ FS nel)) -> Either (Fin n) (Fin n)
-- suffices: (FZ = to $ FS nel) -> Fin n
-- permDoesntFix_corrolary (MkIso to ...) (FS nel) : Not (FS nel = FZ) -> (to $ FS nel = FZ) -> Not (to FZ = FZ)
-- permDoesntFix_corrolary (MkIso to ...) (FS nel) (sym FZNotFS) : (to $ FS nel = FZ) -> Not (to FZ = FZ)
-- map (?above . sym) (finReduce $ to $ FS nel) : Either (Fin n) $ Not (to FZ = FZ)
-- finReduce $ to FZ: Either (Fin n) (FZ = to FZ)
-- ?aboveAbove <*> ?above : Either (Fin n) Void
-- -- aboveAbove with a left value will overwrite any value of above. aboveAbove with a Left value is the predecessor of (to $ FS nel) when (to $ FS nel) is nonzero, so this is appropriate.
-- runIso eitherBotRight ?above : Fin n
-- Hence, without using fromEither at all, we arrive at:
-- runIso eitherBotRight $ (map ((permDoesntFix_corrolary (MkIso to from toFrom fromTo) (FS nel) (sym FZNotFS)) . sym) (finReduce $ to $ FS nel)) <*> (finReduce $ to FZ) : Fin n

{-
-- Something like this, maybe...

		to' : Fin n -> Fin n
		to' nel with (finReduce $ to $ FS nel)
			| Right Refl = (runIso eitherBotRight) $ map (the (FZ = to $ to $ FS nel -> Void) ?weakval_absurdity) $ finReduce $ to $ to $ FS nel
			| Left (FS nel') = nel'
-}


{-
-- Can't use this because it won't accept the proof in to', analogous to from_fzfixedAndNotFixed, that FZ can't be fixed by the permutation if it is the value of a (Fin (S n)) other than FZ.

weakenIsoByValFZ : Iso (Fin (S n)) (Fin (S n)) -> Iso (Fin n) (Fin n)
weakenIsoByValFZ {n} (MkIso to from toFrom fromTo) = MkIso to' from' toFrom' fromTo'
	where
		to' : Fin n -> Fin n
		to' nel
			with (to (FS nel))
				| FZ with (to FZ)
					| FZ = void . FZNotFS $ trans (trans (sym $ fromTo FZ) $ sym $ cong {f=from} $ the (FZ = to FZ) Refl) (trans (cong {f=from} $ the (FZ = to $ FS nel) Refl) $ fromTo $ FS nel)
					| FS skipFZ = skipFZ
				| FS nel' = nel'
		from' : Fin n -> Fin n
		from' nel
			with (from (FS nel))
				| FZ with (from FZ)
					| FZ = void ?from_fzfixedAndNotFixed
					| FS skipFZ = skipFZ
				| FS nel' = nel'
		toFrom' : (y : Fin n) -> to' (from' y) = y
		fromTo' : (x : Fin n) -> from' (to' x) = x
-}

vectPermTo : Iso (Fin n) (Fin n) -> Vect n a -> Vect n a
vectPermTo (MkIso to from toFrom fromTo) {n} {a} xs = map (((flip index) xs) . to) range

moveUpdateAt : (sigma : Iso (Fin n) (Fin n)) -> vectPermTo sigma $ updateAt nel f xs = updateAt (runIso sigma nel) f (vectPermTo sigma xs)

vecDeleteatpermEq : (sigma : Iso (Fin (S n)) (Fin (S n))) -> ( deleteAt (runIso sigma FZ) $ vectPermTo sigma xs = vectPermTo (weakenIsoByValFZ sigma) $ deleteAt FZ xs )
vecDeleteatpermEq sigma@(MkIso to from toFrom fromTo) {xs} = ?vecDeleteatpermEq'

deleteAtAsPermTail : (sigma : Iso (Fin (S n)) (Fin (S n))) -> ( xs = vectPermTo sigma (y::ys) ) -> ( deleteAt (runIso sigma FZ) xs = vectPermTo (weakenIsoByValFZ sigma) ys )
deleteAtAsPermTail sigma@(MkIso to from toFrom fromTo) pr_xsRys {xs=xx::[]} {y} {ys=[]} = ?deleteAtAsPermTail_rhs_1
	where
		fin1elIsFZ : (el : Fin 1) -> el=FZ
		fin1elIsFZ FZ = Refl
		fin1elIsFZ (FS el) = FinZElim el
deleteAtAsPermTail sigma@(MkIso to from toFrom fromTo) pr_xsRys {xs=xx::xxs} {y} {ys=yy::yys} = ?deleteAtAsPermTail_rhs_2

multIdLeftNeutral : VerifiedRingWithUnity r => (a : Matrix _ _ r) -> Id <> a = a

multIdRightNeutral : VerifiedRingWithUnity r => (a : Matrix _ _ r) -> a <> Id = a

{-
When checking type of ZZModuleSpan.rewriteMultInv:
When checking an application of function Control.Algebra.VectorSpace.<#>:
        Can't resolve type class Group r

---

rewriteMultInv : (VerifiedRingWithUnity r, VerifiedModule r a) -> (s : r) -> (x : a) -> (inverse s) <#> x = s <#> (inverse x)
-}

rewriteMultInvVect : VerifiedRingWithUnity r => (s : r) -> (x : Vect _ r) -> (inverse s) <#> x = s <#> (inverse x)

rewriteMultInvMat : VerifiedRingWithUnity r => (s : r) -> (x : Matrix _ _ r) -> (inverse s) <#> x = s <#> (inverse x)

rewriteAssociativityUnderEquality : {f, g : a -> a -> a} -> ( (x : a) -> (y : a) -> f x y = g x y) -> (l `f` (c `f` r) = (l `f` c) `f` r) -> (l `g` (c `g` r) = (l `g` c) `g` r)
rewriteAssociativityUnderEquality {f} {g} {l} {c} {r} fneq prf = trans (sym stepleft) $ trans prf stepright
	where
		stepleft : f l (f c r) = g l (g c r)
		stepleft = rewrite sym (fneq c r) in fneq l _
		stepright : f (f l c) r = g (g l c) r
		stepright = rewrite sym (fneq l c) in fneq _ r

{-
-- Works both compiled and in the REPL

rewriteAssociativityUnderEquality {f} {g} {l} {c} {r} fneq prf = ?rewriteAssociativityUnderEquality'

rewriteAssociativityUnderEquality' = proof
  intros
  claim stepleft f l (f c r) = g l (g c r)
  claim stepright f (f l c) r = g (g l c) r
  unfocus
  unfocus
  exact trans (sym stepleft) $ trans prf stepright
  exact rewrite sym (fneq l c) in fneq _ r
  exact rewrite sym (fneq c r) in fneq l _

-- Works in REPL but not compiled

rewriteAssociativityUnderEquality {f} {g} {l} {c} {r} fneq prf = ?rewriteAssociativityUnderEquality'

rewriteAssociativityUnderEquality' = proof
  intros
  exact trans _ $ trans prf _
  exact trans _ (sym $ fneq l _)
  exact trans (cong {f=(flip f) r} (fneq l c)) _
  exact cong (sym $ fneq _ _)
  exact fneq _ r
-}



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

bispanslz : (xs : Matrix n w ZZ) -> (ys : Matrix n' w ZZ) -> Type
bispanslz xs ys = (xs `spanslz` ys, ys `spanslz` xs)



{-
Proof of relational properties of span

i.e.,
Relational:
* equivalence relation axioms
* spanned by implies tail spanned by
Algebraic:
* gcd and lcm divisibility relationships via Bezout's identity
* additive updates to the spanning set that preserve span
Reordering lemmas:
* Master: permPreservesSpanslz : (sigma : Iso (Fin n) (Fin n)) -> spanslz (vectPermTo sigma xs) xs
* Minimal for above: spanslz (x::y::zs) (y::x::zs)
** Requires knowledge that every permutation of (Fin n) is built up from pair swaps and that this corresponds to the special case of Master for such a permutation.
** Note that extension of special cases to those for the permutations' composites follows from spanslztrans together with (runBijection (sigma . tau) = (runBijection sigma) . (runBijection tau)).
* spanslz (xs++ys) (ys++xs)
Mixed:
* compatibility with combining sets spanned or spanning (list concatenation is algebraic)
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

bispanslztrans : {xs : Matrix na m ZZ} -> {ys : Matrix ni m ZZ} -> {zs : Matrix nu m ZZ} -> bispanslz {n=na} {n'=ni} xs ys -> bispanslz {n=ni} {n'=nu} ys zs -> bispanslz xs zs
bispanslztrans (sxy,syx) (syz,szy) = (spanslztrans sxy syz, spanslztrans szy syx)



bispanslzsym : xs `bispanslz` ys -> ys `bispanslz` xs
bispanslzsym = swap



spanslzrefl : spanslz xs xs
spanslzrefl = ( Id ** zippyScaleIdLeftNeutral _ )

bispanslzrefl : bispanslz xs xs
bispanslzrefl = (spanslzrefl, spanslzrefl)

spanslzreflFromEq : (xs=ys) -> xs `spanslz` ys
spanslzreflFromEq pr = ( Id ** trans (zippyScaleIdLeftNeutral _) pr )

bispanslzreflFromEq : (xs=ys) -> xs `bispanslz` ys



spanslzNeutral : {xs : Matrix n w ZZ} -> spanslz xs $ the (Matrix m w ZZ) Algebra.neutral
spanslzNeutral = (Algebra.neutral ** trans (sym $ timesMatMatAsMultipleLinearCombos _ _) $ neutralMatIsMultZeroL _)

updateAtEquality : {ls : Matrix n k ZZ} -> {rs : Matrix k m ZZ} -> (updi : Fin n) -> (f : (i : Nat) -> Vect i ZZ -> Vect i ZZ) -> ( (la : Vect k ZZ) -> (f k la) <\> rs = f m $ la <\> rs ) -> (updateAt updi (f k) ls) `zippyScale` rs = updateAt updi (f m) (ls `zippyScale` rs)
updateAtEquality {ls=[]} updi f fnpreq = FinZElim updi
updateAtEquality {ls=l::ls} {rs} FZ f fnpreq = vecHeadtailsEq {xs=tail $ (l::ls) `zippyScale` rs} ( trans (sym $ timesVectMatAsLinearCombo (f _ l) rs) $ trans (fnpreq l) $ cong {f=f _} $ timesVectMatAsLinearCombo l rs ) Refl
updateAtEquality {ls=l::ls} (FS penupdi) f fnpreq = vecHeadtailsEq Refl $ updateAtEquality penupdi f fnpreq

-- Note the relationship to bilinearity of matrix multiplication
vectMatLScalingCompatibility : {z : ZZ} -> {rs : Matrix k m ZZ} -> (z <#> la) <\> rs = z <#> (la <\> rs)
vectMatLScalingCompatibility {z} {la} {rs} = ?vectMatLScalingCompatibility_rhs

{-
-- Works in REPL, untested otherwise
vectMatLScalingCompatibility_rhs = proof
  intros
  claim vectmatLiftId1 (z <#> la) <\> rs = head $ (row $ z <#> la) <> rs
  unfocus
  claim moveScaleOutsideRow row (z <#> la) = z <#> (row la)
  unfocus
  claim chScaleOutsideTimes (row (z <#> la)) <> rs = z <#> ((row la) <> rs)
  unfocus
  exact trans vectmatLiftId1 $ cong {f=head} chScaleOutsideTimes
  trivial
  unfocus
  exact trans (cong {f=(<> rs)} moveScaleOutsideRow) _
  trivial
  compute
  claim scalMatMatCompat (scal : ZZ) -> {nu, ka, mu : Nat} -> (xs : Matrix nu ka ZZ) -> (ys : Matrix ka mu ZZ) -> (scal <#> xs) <> ys = scal <#> (xs <> ys)
  unfocus
  exact scalMatMatCompat z (row la) rs
  exact ?timesScalarLeftCommutesWithTimesMatRight
-}

spanRowScalelz : (z : ZZ) -> (updi : Fin n') -> spanslz xs ys -> spanslz xs (updateAt updi (z<#>) ys)
spanRowScalelz z updi (vs ** prvs) {xs} = (updateAt updi (z<#>) vs ** trans scaleMain $ rewrite sym prvs in Refl)
	where
		scaleMain : (updateAt updi (z<#>) vs) `zippyScale` xs = updateAt updi (z<#>) (vs `zippyScale` xs)
		scaleMain = updateAtEquality updi ( \i => (z<#>) ) ( \la => vectMatLScalingCompatibility {la=la} )



spanScalelz : (z : ZZ) -> spanslz xs ys -> spanslz xs (z<#>ys)

spanAdd : spanslz xs ys -> spanslz xs zs -> spanslz xs (ys <+> zs)
spanAdd {xs} {ys} {zs} spXY spXZ = ((getWitness spXY)<+>(getWitness spXZ) **
	trans (sym $ timesMatMatAsMultipleLinearCombos ((getWitness spXY)<+>(getWitness spXZ)) xs)
	$ trans (matrixMultRightDistributesOverMatrixPlus (getWitness spXY) (getWitness spXZ) xs)
	$ trans (cong {f=(((getWitness spXY)<>xs)<+>)} $ trans (timesMatMatAsMultipleLinearCombos (getWitness spXZ) xs) $ getProof spXZ)
	$ cong {f=(<+>zs)} $ trans (timesMatMatAsMultipleLinearCombos (getWitness spXY) xs) $ getProof spXY
	)

spanSub : spanslz xs ys -> spanslz xs zs -> spanslz xs (ys <-> zs)
spanSub {xs} {ys} {zs} prxy prxz = ?spanSub'

spanSub' = proof
  intros
  let spanAdd' = spanAdd {xs=xs} {ys=ys} {zs = inverse zs}
  refine spanAdd'
  exact prxy
  exact spanslztrans (spanScalelz (inverse unity) prxz) $ replace {P=\t => spanslz ((<#>) (inverse $ unity {a=ZZ}) zs) t} (trans ( rewriteMultInvMat (unity {a=ZZ}) zs ) ( moduleScalarUnityIsUnity {a=ZZ} (inverse zs) )) spanslzrefl

{-
-- Works in REPL only
spanSub' = proof
  intros
  refine spanAdd
  exact prxy
  exact spanslztrans (spanScalelz (inverse unity) prxz) _
  exact replace {P=\t => spanslz ((<#>) (inverse $ unity {a=ZZ}) zs) t} (trans ( rewriteMultInvMat (unity {a=ZZ}) zs ) ( the ((<#>) (unity {a=ZZ}) (inverse zs) = (inverse zs)) ?moduleIdScalZZ )) spanslzrefl
-}

{-
-- I feel like typechecking this shouldn't be a problem for Idris.
-- Perhaps (unity) needed to be (Algebra.unity).


spanSub : spanslz xs ys -> spanslz xs zs -> spanslz xs (ys <-> zs)
spanSub {xs} {ys} {zs} prxy prxz
	with ( spanAdd {xs=xs} {ys=ys} {zs = (inverse unity)<#>zs} prxy (spanScalelz (inverse unity) prxz) )
		| (vs ** pr) = (vs ** cong {f=spanslz xs} $ rewriteMultInvMat unity zs)


-- Replacement test code for analyzing the problem:


spanSub : {xs : Matrix n w ZZ} -> {ys, zs : Matrix n' w ZZ} -> spanslz {n=n} {n'=n'} {w=w} xs ys -> spanslz {n=n} {n'=n'} {w=w} xs zs -> spanslz {n=n} {n'=n'} {w=w} xs ((the (Matrix n' w ZZ -> Matrix n' w ZZ -> Matrix n' w ZZ) (<->)) ys zs)
spanSub {xs} {ys} {zs} {n} {n'} {w} prxy prxz
	with (?akdjna)
	-- with ( spanAdd {xs=xs} {ys=ys} {zs = (inverse (the ZZ unity))<#>zs} prxy (spanScalelz (inverse (the ZZ unity)) prxz) )
		| (vs ** pr) = ?ajdnjfka
		-- | (vs ** pr) = (vs ** cong {f=spanslz xs} $ rewriteMultInvMat (the ZZ unity) pr)
-}



mergeSpannedLZs : spanslz xs ys -> spanslz xs zs -> spanslz xs (ys++zs)

spanslzRowTimesSelf : spanslz xs [v<\>xs]
spanslzRowTimesSelf {xs} {v} = ([v] ** cong {f=(::[])} $ sym $ timesVectMatAsLinearCombo v xs)

preserveSpanningLZByCons : spanslz xs ys -> spanslz (z::xs) ys

extendSpanningLZsByPreconcatTrivially : spanslz xs ys -> spanslz (zs++xs) ys
extendSpanningLZsByPreconcatTrivially {zs=[]} prsp = prsp
extendSpanningLZsByPreconcatTrivially {zs=z::zs} prsp = preserveSpanningLZByCons {z=z} $ extendSpanningLZsByPreconcatTrivially {zs=zs} prsp

-- Could be done by (spanslztrans) of above with a reversal permutation `spanslz`.
-- Equality of the (Fin) types and induced eq of the (Iso) types w/ (Auto)s suffices.
extendSpanningLZsByPostconcatTrivially : spanslz xs ys -> spanslz (xs++zs) ys

concatSpansRellz : spanslz xs zs -> spanslz ys ws -> spanslz (xs++ys) (zs++ws)



spanslzAdditiveExchange : spanslz ((y<+>(z<\>xs))::xs) (y::xs)
spanslzAdditiveExchange {xs} {y} {z} =
	-- Subtract two matrices
	(spanSub
		(spanslzrefl {xs=(y<+>(z<\>xs))::xs})
		-- Treat head subtraction as matrix subtraction by appending neutral mat:
		-- (y<+>(z<\>xs))::xs `spanslz` (z<\>xs)::Algebra.neutral
		$ mergeSpannedLZs
			-- (y<+>(z<\>xs))::xs `spanslz` [z<\>xs]
			(spanslztrans
				(preserveSpanningLZByCons spanslzrefl)
				spanslzRowTimesSelf)
			spanslzNeutral)
	-- Then simplify the subtraction
	`spanslztrans` (spanslzreflFromEq
		$ vecHeadtailsEq
			-- Regroup element next to its inverse, then cancel
			(trans
				(sym $ semigroupOpIsAssociative_Vect y (z<\>xs) $ inverse $ z<\>xs)
				$ trans (cong $ groupInverseIsInverseL_Vect $ z<\>xs)
				$ monoidNeutralIsNeutralL_Vect y)
			-- (<->Algebra.neutral) is a no-op.
			$ trans
				(cong {f=(xs<+>)} $ neutralSelfInverse)
				$ monoidNeutralIsNeutralL xs)

spanslzSubtractiveExchange : spanslz ((y<->(z<\>xs))::xs) (y::xs)

{-
Should actually be as follows, as it will make the proof easier:

spanslzAdditiveExchange : spanslz ((y<+>(monoidsum $ zipWith (<#>) z xs))::xs) (y::xs)

spanslzSubtractiveExchange : spanslz ((y<->(monoidsum $ zipWith (<#>) z xs))::xs) (y::xs)
-}

{-
Implication: Above can be rewritten in terms of (updateAt FZ).

This characterization is combined with a natural theorem on bijection reorderings to show that for all indices (nel : Fin n), (updateAt nel (<->(monoidsum $ zipWith (<#>) z xs)) xs) `spanslz` xs.
-}

{-
-- Not needed for our purposes.

spanslzAdditiveExchange2 : spanslz xs ys -> spanslz ((zs<+>ys)++xs) (zs++xs)

spanslzSubtractiveExchange2 : spanslz xs ys -> spanslz ((zs<->ys)++xs) (zs++xs)
-}

spanslzAdditivePreservation : spanslz (y::xs) ((y<+>(z<\>xs))::xs)
spanslzAdditivePreservation {xs} {y} {z} = ?spanslzAdditivePreservation'

spanslzSubtractivePreservation : spanslz (y::xs) ((y<->(z<\>xs))::xs)

{-
Implication of bispannability: Transformations of this form preserve the span of the vectors, the span of both sides of the transformation is the same ZZ-submodule of ZZ^n.
-}



permPreservesSpanslz : (sigma : Iso (Fin n) (Fin n)) -> spanslz (vectPermTo sigma xs) xs

permPreservesSpannedbylz : (sigma : Iso (Fin n) (Fin n)) -> spanslz xs (vectPermTo sigma xs)

swapFZPerm : (nel : Fin (S predn)) -> (sigma : Iso (Fin (S predn)) (Fin (S predn)) ** (runIso sigma FZ = nel, runIso sigma nel = FZ, (Not (mel=FZ),Not (mel=nel)) -> runIso sigma mel = mel) )

{-
Recall:

moveUpdateAt : (sigma : Iso (Fin n) (Fin n)) -> vectPermTo sigma $ updateAt nel f xs = updateAt (runIso sigma nel) f (vectPermTo sigma xs)

---

deleteAtAsPermTail : (sigma : Iso (Fin (S n)) (Fin (S n))) -> ( xs = vectPermTo sigma (y::ys) ) -> ( deleteAt (runIso sigma FZ) xs = vectPermTo (weakenIsoByValFZ sigma) ys )
-}

headOpPreservesSpanslzImpliesUpdateAtDoes : {f : Vect m ZZ -> Matrix predn m ZZ -> Vect m ZZ} -> ((xx : Vect m ZZ) -> (xxs: Matrix predn m ZZ) -> spanslz (f xx xxs :: xxs) (xx::xxs)) -> (nel : Fin (S predn)) -> (xs: Matrix (S predn) m ZZ) -> spanslz (updateAt nel (\xx => f xx (deleteRow nel xs)) xs) xs
{-
-- For starters:
headOpPreservesSpanslzImpliesUpdateAtDoes {f} transfpr nel xs
	with (swapFZPerm nel)
		| ( sigma ** ( fzToNelpr, nelToFZpr, elseToSelfpr ) ) =
			...
-- Main idea: sigma can then be used to take (xs) to a ((x'::xs') : Vect _ _) such that (index nel xs = index FZ (x'::xs') = x') and, by analyzing weakenIsoByValFZ, ((vectToPerm $ isoSym $ weakenIsoByValFZ sigma) $ deleteRow nel xs=tail xs').
-- With weakenIsoByValFZ, we basically want to use a permutation used on a Vect to act on its row-deleted form as if the deleted row at (nel : Fin (S predn)) were sent to a row that were never added and reindex around the deleted row. However, there would also be an element being sent TO that deleted row, and we haven't accounted for that by giving it a new value. Since there are currently no properties that weakenIsoByValFZ must satisfy to make the algorithm correct, we can set that value arbitrarily, except that we'd have to make sure it's a permutation. This is not a regular process to perform!
-- Why wouldn't it work to just tighten the cycle the deleted row lies in so that it's skipped in order? What properties must weakenIsoByValFZ satisfy for it to allow headOpPreservesSpanslzImpliesUpdateAtDoes to be produced?
-- We may need ( vectToPerm $ weakenIsoByValFZ $ isoSym sigma ) instead of ( vectToPerm $ isoSym $ weakenIsoByValFZ sigma )
-}

spanslzAdditiveExchangeAt : (nel : Fin (S predn)) -> spanslz (updateAt nel (<+>(z<\>(deleteRow nel xs))) xs) xs
spanslzAdditiveExchangeAt nel {predn} {xs} {z} = headOpPreservesSpanslzImpliesUpdateAtDoes {f=\argxx => \argxxs => argxx<+>(z<\>argxxs) } (\argxx => \argxxs => spanslzAdditiveExchange {y=argxx} {xs=argxxs} {z=z}) nel xs

spanslzSubtractiveExchangeAt : (nel : Fin (S predn)) -> spanslz (updateAt nel (<->(z<\>(deleteRow nel xs))) xs) xs

spanslzAdditivePreservationAt : (nel : Fin (S predn)) -> spanslz xs (updateAt nel (<+>(z<\>(deleteRow nel xs))) xs)

spanslzSubtractivePreservationAt : (nel : Fin (S predn)) -> spanslz xs (updateAt nel (<->(z<\>(deleteRow nel xs))) xs)

bispanslzAdditiveExchangeAt : (nel : Fin (S predn)) -> bispanslz (updateAt nel (<+>(z<\>(deleteRow nel xs))) xs) xs
bispanslzAdditiveExchangeAt nel = (spanslzAdditiveExchangeAt nel, spanslzAdditivePreservationAt nel)

bispanslzSubtractiveExchangeAt : (nel : Fin (S predn)) -> bispanslz (updateAt nel (<->(z<\>(deleteRow nel xs))) xs) xs
bispanslzSubtractiveExchangeAt nel = (spanslzSubtractiveExchangeAt nel, spanslzSubtractivePreservationAt nel)

bispansSamevecExtension : xs `bispanslz` ys -> (v : Vect _ ZZ) -> (v::xs) `bispanslz` (v::ys)

bispansNullcolExtension : (getCol FZ xs=Algebra.neutral)
	-> ys `bispanslz` map tail xs
	-> map ((Pos Z)::) ys `bispanslz` xs



spansImpliesSameFirstColNeutrality : xs `spanslz` ys -> getCol FZ xs = Algebra.neutral -> getCol FZ ys = Algebra.neutral
