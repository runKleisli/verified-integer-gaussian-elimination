module ZZGaussianElimination

import Control.Algebra
import Classes.Verified
import Control.Algebra.VectorSpace -- definition of module

import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20
import Data.Matrix.AlgebraicVerified

import Data.Vect.Structural
import Data.Matrix.Structural

import Data.ZZ
import Control.Algebra.NumericInstances
import Control.Algebra.ZZVerifiedInstances
import Data.Matrix.ZZVerified

import ZZModuleSpan
import Data.Matrix.LinearCombinations

import FinOrdering

-- For style. ((Reader r a) equivalent to (r -> a))
import Control.Monad.Identity
import Control.Monad.Reader



{-
Trivial lemmas and plumbing
-}



total
FinSZAreFZ : (x : Fin 1) -> x=FZ
FinSZAreFZ FZ = Refl
FinSZAreFZ (FS voda) = FinZElim voda

last_rw : Fin (n+(S predk))
last_rw {n} {predk} = rewrite sym (plusSuccRightSucc n predk) in last {n=n+predk}

{-
-- Impossible to have this type
last_rw2 : ( the (Fin (S $ n+predk)) last = the (Fin (n + (S predk))) last )
last_rw2 {n} {predk} = rewrite sym (plusSuccRightSucc n predk) in Refl
-}

{-
-- Seems impossible to prove this, actually. Maybe with careful study.
last_rw2 : ( last_rw {n=n} {predk=predk} ~=~ Data.Fin.last {n=n+predk} )
last_rw2 = ?last_rw2_pr
-- last_rw2 {n} {predk} = rewrite sym (plusSuccRightSucc n predk) in Refl
-}

commuteFSWeaken : (i : Fin n) -> (FS $ weaken i = weaken $ FS i)
commuteFSWeaken i = Refl



{-
"
LTE (S (finToNat last)) (finToNat i)  cannot be a parameter of Prelude.Uninhabited.Uninhabited
(Type class arguments must be injective)
"

> instance Uninhabited (LTE (S $ finToNat $ last {n=n}) (finToNat $ the (Fin (S n)) i)) where {
> 	uninhabited = ?notSNatLastLTEAnything
> }
-}

-- notSNatLastLTEAnything : LTE (S $ finToNat $ last {n=n}) (finToNat $ the (Fin (S n)) i) -> Void

notSNatLastLTEAnything : {n : Nat} -> {i : Fin (S n)} -> LTE (S $ finToNat $ last {n=n}) (finToNat i) -> Void



total
splitFinS : (i : Fin (S predn)) -> Either ( k : Fin predn ** i = weaken k ) ( i = Data.Fin.last )
splitFinS {predn=Z} FZ = Right Refl
splitFinS {predn=Z} (FS j) = absurd j
splitFinS {predn=S prededn} FZ = Left ( FZ ** Refl )
splitFinS {predn=S prededn} (FS prednel) with ( splitFinS prednel )
	| Left ( k ** pr ) = Left ( FS k ** cong pr )
	| Right pr = Right $ cong pr



{-
BUG: Wrong type displayed given implicit argument in argument

Incorrect type displayed:

\a : Type => \p : ({m : Nat} -> Fin (S m) -> a -> Type) => p (weaken $ FZ {k=Z})
	: (a : Type) ->
	  Fin (S m) -> a -> Type ->
	  a -> Type

Correct type displayed:

\a : Type => \p : ((m : Nat) -> Fin (S m) -> a -> Type) => p 5 (weaken FZ)
	: (a : Type) ->
	  ((m : Nat) -> Fin (S m) -> a -> Type) ->
	  a -> Type

Note that these examples both actually have the correct type, they're just not displayed correctly.
-}



{-
Error discovered while implementing (foldAutoind).

---

It was found that if you replace the argument

> p : (m : Nat) -> Fin (S m) -> a -> Type

with one where (m) is implicit, and rewrite (foldAutoind) & dependencies accordingly, then one can't implement them, because composing (p) with weaken leads to a Universe Inconsistency error, which doesn't appear when the weakening is done in the REPL, only when the resulting proof is loaded in the module.

See (elimFirstCol-oldmaterial.idr) where (fai_regrwkn_chty) and (fai_regrwkn_chty2) are being implemented (for that file's (foldAutoind), (foldAutoind2) resp.) for details.

This differs from the error described in (ImplicitArgsError), in that the values of (p) are irrelevant in creating this Universe Inconsistency error, whereas the one in (ImplicitArgsError) would arise from the values of (p) having implicit arguments of their own.
-}



fai_regrwkn : ( p : (m : Nat) -> Fin (S m) -> a -> Type )
	-> ( (i : Fin (S predn))
		-> ( w : a ** p _ (FS i) w )
		-> ( w' : a ** p _ (weaken i) w' ) )
	-> (i : Fin predn)
	-> ( w : a ** ((p _) . weaken) (FS i) w )
	-> ( w' : a ** ((p _) . weaken) (weaken i) w' )
-- can't be written as `(fn . weaken) i`, nor can `i` be dropped as an argument.
fai_regrwkn p fn i = fn (weaken i)

||| A vector fold over suppressed indices
||| Best used with those `p` which are trivial for (last) and some (a).
foldAutoind : ( p : (m : Nat) -> Fin (S m) -> a -> Type )
	-> ( (i : Fin predn)
		-> ( w : a ** p _ (FS i) w )
		-> ( w' : a ** p _ (weaken i) w' ) )
	-> ( v : a ** p _ (last {n=predn}) v )
	-> ( xs : Vect (S predn) a ** (i : Fin (S predn)) -> p _ i (index i xs) )
foldAutoind {predn=Z} p regr (v ** pv) = ( [v] ** \i => rewrite sym (the (FZ = i) $ sym $ FinSZAreFZ i) in pv )
foldAutoind {predn=S prededn} p regr (v ** pv) with (regr (last {n=prededn}) (v ** pv))
	| (v' ** pv') with ( foldAutoind {predn=prededn} (\mu => (p $ S mu) . weaken) (fai_regrwkn p regr) (v' ** pv') )
		| (xs ** fn) = ?faiNew
		-- | ( xs ** fn ) = ( xs++[v] ** _ )

faiNew = proof
  intros
  exact (appendedSingletonAsSuccVect xs v ** _)
  intro i
  claim ifLastThenProved (i=last) -> p (S prededn) i (index i $ appendedSingletonAsSuccVect xs v)
  unfocus
  claim ifWeakenedThenProved (j : Fin (S prededn) ** i = weaken j) -> p (S prededn) i (index i $ appendedSingletonAsSuccVect xs v)
  unfocus
  let iAsEither = splitFinS i
  exact either ifWeakenedThenProved ifLastThenProved iAsEither
  intro prIsLast
  rewrite sym prIsLast
  exact rewrite (lastInd {xs=xs} {v=v}) in pv
  intro parIsWeakened
  let prIsWeakened = getProof parIsWeakened
  rewrite sym prIsWeakened
  exact rewrite (weakenedInd {xs=xs} {v=v} {k=getWitness parIsWeakened}) in fn (getWitness parIsWeakened)



fai2_regrwkn : (a : Nat -> Type)
	-> ( p : (m : Nat) -> Fin (S m) -> (a m) -> Type )
	-> ( (i : Fin (S predn))
		-> ( w : a (S predn) ** p _ (FS i) w )
		-> ( w' : a (S predn) ** p _ (weaken i) w' ) )
	-> (i : Fin predn)
	-> ( w  : (a . S) predn ** ((p _) . weaken) (FS i) w )
	-> ( w' : (a . S) predn ** ((p _) . weaken) (weaken i) w' )
-- can't be written as `(fn . weaken) i`, nor can `i` be dropped as an argument.
fai2_regrwkn a p fn i = fn (weaken i)

||| A vector fold over suppressed indices
||| The sequel to foldAutoind
{-
(a : Nat -> Type) is not made implicit because Idris isn't likely to deduce it and will likely spend a long time trying anyway.
-}
foldAutoind2 : ( a : Nat -> Type )
	-> ( p : (m : Nat) -> Fin (S m) -> (a m) -> Type )
	-> ( (i : Fin predn)
		-> ( w : a predn ** p _ (FS i) w )
		-> ( w' : a predn ** p _ (weaken i) w' ) )
	-> ( v : a predn ** p _ (last {n=predn}) v )
	-> ( xs : Vect (S predn) (a predn) ** (i : Fin (S predn)) -> p _ i (index i xs) )
foldAutoind2 {predn=Z} _ p regr (v ** pv) = ( [v] ** \i => rewrite sym (the (FZ = i) $ sym $ FinSZAreFZ i) in pv )
foldAutoind2 {predn=S prededn} natToA p regr (v ** pv) with (regr (last {n=prededn}) (v ** pv))
	| (v' ** pv') with ( foldAutoind2 {predn=prededn} (natToA . S) (\mu => (p $ S mu) . weaken) (fai2_regrwkn natToA p regr) (v' ** pv') )
		| (xs ** fn) = ?faiNew2
		-- | ( xs ** fn ) = ( xs++[v] ** _ )

-- Identical to the proof of faiNew
faiNew2 = proof
  intros
  exact (appendedSingletonAsSuccVect xs v ** _)
  intro i
  claim ifLastThenProved (i=last) -> p (S prededn) i (index i $ appendedSingletonAsSuccVect xs v)
  unfocus
  claim ifWeakenedThenProved (j : Fin (S prededn) ** i = weaken j) -> p (S prededn) i (index i $ appendedSingletonAsSuccVect xs v)
  unfocus
  let iAsEither = splitFinS i
  exact either ifWeakenedThenProved ifLastThenProved iAsEither
  intro prIsLast
  rewrite sym prIsLast
  exact rewrite (lastInd {xs=xs} {v=v}) in pv
  intro parIsWeakened
  let prIsWeakened = getProof parIsWeakened
  rewrite sym prIsWeakened
  exact rewrite (weakenedInd {xs=xs} {v=v} {k=getWitness parIsWeakened}) in fn (getWitness parIsWeakened)



{-
Properties of vectors and matrices.
-}



downAndNotRightOfEntryImpliesZ : (xs : Matrix n m ZZ) -> (row : Fin n) -> (col : Fin m) -> Type
downAndNotRightOfEntryImpliesZ xs nel mel {n} {m} = (i : Fin n) -> (j : Fin m) -> (finToNat nel `LTRel` finToNat i) -> (finToNat j `LTERel` finToNat mel) -> indices i j xs = Pos Z
{-
Equivalent properties:
1) map (take mel) (drop nel xs) = neutral
2) (nel `LT` i) -> (j `LTE` mel) -> indices i j xs = Pos Z
	# In pseudocode, because we decided not to use direct LT and LTE of Fins.

---

We cannot write

> downAndNotRightOfEntryImpliesZ : (xs : Matrix n m ZZ) -> (row : Fin n) -> (col : Fin m) -> Type
> downAndNotRightOfEntryImpliesZ xs nel mel {n} {m} = {i : Fin n} -> {j : Fin m} -> (finToNat nel `LTRel` finToNat i) -> (finToNat j `LTERel` finToNat mel) -> indices i j xs = Pos Z

because the error described in ImplicitArgsError applied to (i) and (j) in ({i : Fin n} -> {j : Fin m} -> ...).
-}



weakenDownAndNotRight : (downAndNotRightOfEntryImpliesZ mat (FS prednel) mel) -> (indices (FS prednel) mel mat = Pos Z) -> downAndNotRightOfEntryImpliesZ mat (weaken prednel) mel

afterUpdateAtCurStillDownAndNotRight : (downAndNotRightOfEntryImpliesZ mat (FS prednel) mel) -> (downAndNotRightOfEntryImpliesZ (updateAt (FS prednel) f mat) (FS prednel) mel)



leadingNonzero : (v : Vect n ZZ) -> Type
leadingNonzero {n} v = Either
		(v = neutral)
		(nel : Fin n **
			( {i : Fin n}
			-> finToNat i `LTRel` finToNat nel
			-> index i v = Pos Z,
			Not (index nel v = Pos Z) )
		)

leadingNonzeroCalc : (v : Vect n ZZ) -> leadingNonzero v
leadingNonzeroCalc [] = Left Refl
leadingNonzeroCalc {n=S predn} (Pos Z::xs) with (leadingNonzeroCalc xs)
	| Left pr = Left $ cong {f=(::) $ Pos Z} pr
	| Right ( predel ** (l_fn, r_pr) ) = Right ( FS predel ** (l_fn', r_pr) )
		where
			l_fn_pr_skipup : index (FS i) (v::vs) = index i vs
			l_fn_pr_skipup = Refl
			l_fn' : {ii : Fin (S predn)}
				-> finToNat ii `LTRel` finToNat (FS predel)
				-> index ii (Pos Z::xs) = Pos Z
			l_fn' {ii=FZ} precondit = Refl
			l_fn' {ii=FS j} precondit = trans (l_fn_pr_skipup {v=Pos 0}) $ l_fn (fromLteSucc precondit)
leadingNonzeroCalc {n=S predn} (Pos (S k)::xs) = Right ( FZ ** ( void . succNotLTEzero, flip (replace {P=distinguish_Z_SZ}) () ) )
	where
		distinguish_Z_SZ : ZZ -> Type
		distinguish_Z_SZ (Pos Z) = Void
		distinguish_Z_SZ z = ()
leadingNonzeroCalc {n=S predn} (NegS k::xs) = Right ( FZ ** ( void . succNotLTEzero, flip (replace {P=distinguish_Z_SZ}) () ) )
	where
		distinguish_Z_SZ : ZZ -> Type
		distinguish_Z_SZ (Pos Z) = Void
		distinguish_Z_SZ z = ()



{-
There is a tricky part to matching on Left.

We might have this

> | Left _ = downAndNotRightOfEntryImpliesZ xs nel (last {n=predm})

but that only works if we guarantee `m` has a predecessor `predm`. Else we should use

> | Left _ = ()

So, we just simplify things and write

> | Left _ = {nelow : Fin n} -> (finToNat nel `LTRel` finToNat nelow) -> index nel xs = neutral
-}
rowEchelon : (xs : Matrix n m ZZ) -> Type
rowEchelon {n} {m} xs = (narg : Fin n) -> (ty narg)
	where
		ty : Fin n -> Type
		ty nel with (leadingNonzeroCalc $ index nel xs)
			| Right someNonZness with someNonZness
				| (leadeln ** _) = downAndNotRightOfEntryImpliesZ xs nel leadeln
			| Left _ = {nelow : Fin n} -> (finToNat nel `LTRel` finToNat nelow) -> index nel xs = neutral



{-
Intermediate or secondary algorithms
-}



-- Should be modified to account for (gcd x 0 = 0).
quotientOverZZ : ZZ -> ZZ -> Type
quotientOverZZ x y = ( d : ZZ ** d<.>y=x )

quotientOverZZrefl : x `quotientOverZZ` x
quotientOverZZrefl {x} = ( unity ** ringWithUnityIsUnityR x )

quotientOverZZtrans : x `quotientOverZZ` y -> y `quotientOverZZ` z -> x `quotientOverZZ` z
quotientOverZZtrans (dx ** prx) (dy ** pry) {x} {y} {z} = ( dx<.>dy ** trans (sym $ ringOpIsAssociative dx dy z) $ trans (cong pry) prx )

quotientOverZZreflFromEq : (a=b) -> a `quotientOverZZ` b
quotientOverZZreflFromEq {a} {b} eq with (quotientOverZZrefl {x=b})
	| (d ** pr) = (d ** trans pr $ sym eq)



||| Examples:
||| 
||| > divisorByDistrib (Pos 4) ((Pos 8)::(Pos 0)::[]) (\x => case x of { FZ => (Pos 2 ** Refl); (FS FZ) => (Pos 0 ** Refl) })
||| 
||| (Pos 2 ** ?divisorByDistrib_pr) : (d : ZZ ** multZ d (Pos 4) = Pos 8)
||| 
||| > divisorByDistrib (Pos 4) ((Pos 8)::(Pos 4)::[]) (\x => case x of { FZ => (Pos 2 ** Refl); (FS FZ) => (Pos 1 ** Refl) })
||| 
||| (Pos 3 ** ?divisorByDistrib_pr) : (d : ZZ ** multZ d (Pos 4) = Pos 12)
||| 
||| > divisorByDistrib (Pos 4) ((Pos 8)::(Pos 1)::[]) (\x => case x of { FZ => (Pos 2 ** Refl); (FS FZ) => (Pos 0 ** Refl) })
||| 
||| ... Type mismatch between 0 and 1
divisorByDistrib : (z : ZZ)
	-> (x : Vect n ZZ)
	-> ( (k : _) -> index k x `quotientOverZZ` z )
	-> (LinearCombinations.monoidsum x) `quotientOverZZ` z
divisorByDistrib z [] fn = (0 ** ringNeutralIsMultZeroL z)
{-
-- Doesn't like the (fn . FS) passed to divisorByDistrib in the recursive step.
divisorByDistrib z (xx::xxs) fn with ( divisorByDistrib z xxs (fn . FS) )
	| (dxxs ** prxxs) with (fn FZ)
		| (dxx ** prxx) = (dxx<+>dxxs ** ?divisorByDistrib_pr)
	-- divisorByDistrib_pr {z} {xx} {xxs} {fn} {dxx} {dxxs} =
	-- 	(dxx<+>dxxs)<.>z	={ ringOpIsDistributiveR dxx dxxs z }=
	-- 	(dxx<.>z)<+>(dxxs<.>z)	={ cong {f=((dxx<.>z)<+>)} prxxs }=
	-- 	(dxx<.>z)<+>sum xxs	={ cong {f=(<+>_)} prxx }=
	-- 	xx<+>sum xxs	={ rewrite sym $ monoidrec1D {v=xx} {vs=xxs} }=
	-- 	sum (x::xxs)	QED
-}
divisorByDistrib z (xx::xxs) {n=S predn} fn = ( dxx<+>dxxs ** divisorByDistrib' )
	where
		dxx : ZZ
		dxx = getWitness $ fn FZ
		prxx : dxx<.>z = xx
		prxx = getProof $ fn FZ
		dxxs : ZZ
		-- Passing (fn . FS) as an arg during proof reqs implicit arg (n).
		{-
		In REPL: "No such variable __pi_arg7"
		Otherwise:
		"Type mismatch between
			(k1 : Fin (S k)) ->
			quotientOverZZ (index k1 (xx :: xxs)) z (Type of fn)
		and
			Fin (S k) ->
			(\k1 =>
				quotientOverZZ (index k1 xxs) z) (__pi_arg7) (Expected type)

		Specifically:
			Type mismatch between
				index v1 (xx :: xxs)
			and
				index (__pi_arg7) xxs
		"

		> dxxs = getWitness $ divisorByDistrib z xxs (fn . FS)
		-}
		dxxs = getWitness $ divisorByDistrib z xxs (\i => fn (FS i))
		prxxs : dxxs<.>z = LinearCombinations.monoidsum xxs
		-- prxxs = getProof $ divisorByDistrib z xxs (fn . FS)
		prxxs = getProof $ divisorByDistrib z xxs (\i => fn (FS i))
		{-
		If you only write the following (note the missing (<.>_) from (_<.>_ = _))

		> divisorByDistrib' : (dxx<+>dxxs) = LinearCombinations.monoidsum (xx::xxs)

		then you get a type mismatch error that looks like

		"type mismatch between _ and _, specifically between

			foldrImpl (flip plusZ) (Pos 0) (plusZ xx) xxs

		and

			foldrImpl (flip plusZ) (Pos 0) (plusZ xx) xxs
		"

		which is not at all what's wrong, and is an unhelpful error message.
		-}
		divisorByDistrib' : (dxx<+>dxxs)<.>z = LinearCombinations.monoidsum (xx::xxs)
		divisorByDistrib' = ?divisorByDistrib_pr



{-
We need to modify this formula to make the right-hand-argument of (quotientOverZZ) constant. It should perhaps be saying the (quotientOverZZ)'s right-hand-arg lies in the transpose of xs in a constant position.
-}
zipWithHeadsQuotientRelation : {zs : Vect (S predn) ZZ} -> {xs : Matrix (S predn) (S predm) ZZ} -> (k : _ ) -> ( index k $ map head $ zipWith (<#>) zs xs ) `quotientOverZZ` (head $ index k xs)
zipWithHeadsQuotientRelation {zs=z::zs} {xs=(xx::xxs)::xs} FZ = (z ** Refl)
zipWithHeadsQuotientRelation {zs=z::zs} {xs=(xx::xxs)::xs} {predn=Z} (FS prelk) = FinZElim prelk
zipWithHeadsQuotientRelation {zs=z::zs} {xs=x::xs} {predn=S prededn} (FS prelk) = zipWithHeadsQuotientRelation {zs=zs} {xs=xs} {predn=prededn} prelk

-- Should be applied to (fn) as given by the gcd equality.
zipWithHeadsQuotientRelation2 : {zs : Vect (S predn) ZZ} -> {xs : Matrix (S predn) (S predm) ZZ} -> ( fn : ( i : Fin _ ) -> (head $ Vect.index i xs) `quotientOverZZ` (head $ Vect.head xs) ) -> (k : _ ) -> ( Vect.index k $ map head $ Vect.zipWith (<#>) zs xs ) `quotientOverZZ` (head $ Vect.head xs)
zipWithHeadsQuotientRelation2 {zs} {xs} fn k = quotientOverZZtrans (zipWithHeadsQuotientRelation {zs=zs} {xs=xs} k) (fn k)

linearComboQuotientRelation : (x : Vect (S predm) ZZ) -> (xs : Matrix predn (S predm) ZZ) -> (z : Vect (S predn) ZZ)
	-> ( fn : ( i : Fin _ ) -> (head $ Vect.index i (x::xs)) `quotientOverZZ` (head x) )
	-> ( LinearCombinations.monoidsum $
			map head $
			zipWith (<#>) z (x::xs) )
		`quotientOverZZ` (head x)
linearComboQuotientRelation x xs z fn = divisorByDistrib _ _ (zipWithHeadsQuotientRelation2 {zs=z} {xs=x::xs} fn)

-- Motivation: succImplWknStep_Qfunclemma
linearComboQuotientRelation_corrollary : (x : Vect (S predm) ZZ) -> (xs : Matrix predn (S predm) ZZ) -> (z : Vect (S predn) ZZ)
	-> ( fn : ( i : Fin _ ) -> (head $ Vect.index i (x::xs)) `quotientOverZZ` (head x) )
	-> ( head $
			LinearCombinations.monoidsum $
			zipWith (<#>) z (x::xs) )
		`quotientOverZZ` (head x)
linearComboQuotientRelation_corrollary x xs z fn = quotientOverZZtrans (quotientOverZZreflFromEq $ headOfSumIsSumOfHeads _) $ linearComboQuotientRelation x xs z fn



-- Making argument "k" implicit will not work.
gcdOfVectAlg : Type
gcdOfVectAlg = (k : Nat) -> (x : Vect k ZZ) -> ( v : Vect k ZZ ** ( i : Fin k ) -> (index i x) `quotientOverZZ` (v <:> x) )

-- Necessary because Idris won't unpack the definition of (gcdOfVectAlg) at occurrences.
runGCDOfVectAlg : ZZGaussianElimination.gcdOfVectAlg -> (k : Nat) -> (x : Vect k ZZ) -> ( v : Vect k ZZ ** ( i : Fin k ) -> (index i x) `quotientOverZZ` (v <:> x) )
runGCDOfVectAlg gcdalg = gcdalg

firstColZero : (xs : Matrix n m ZZ) -> Type
firstColZero [] {m} = ()	-- implicit {m} needed to match (invariantly in)/(for all) m
firstColZero ([]::xs) = ()
firstColZero ((xx::xxs)::xs) = (xx=neutral, firstColZero xs)

firstColZeroCalc : (xs : Matrix n m ZZ) -> Dec $ firstColZero xs
firstColZeroCalc [] = Yes ()
firstColZeroCalc ([]::xs) = Yes ()
firstColZeroCalc ((xx::xxs)::xs) with (firstColZeroCalc xs)
	| No pr = No ( pr . snd )
	| Yes pr with (decEq xx neutral)
		| Yes isneut = Yes (isneut, pr)
		| No nope = No ( nope . fst )



succImplWknProp : (omat : Matrix predonnom (S predm) ZZ) -> (senior : Vect (S predm) ZZ) -> (nu : Nat) -> (fi : Fin (S nu)) -> Matrix (S nu) (S predm) ZZ -> Type
succImplWknProp omat senior nu fi tmat = ( senior = head tmat, downAndNotRightOfEntryImpliesZ tmat fi FZ, tmat `bispanslz` (senior::omat) )
succImplWknPropSec2 : (nu : Nat) -> (fi : Fin (S nu)) -> Matrix (S nu) (S predm) ZZ -> Type
succImplWknPropSec2 nu fi tmat = downAndNotRightOfEntryImpliesZ tmat fi FZ

danrzLast : (omat : Matrix (S predn) (S predm) ZZ) -> succImplWknPropSec2 predn (last {n=predn}) omat
danrzLast omat = (\i => \j => void . notSNatLastLTEAnything)

{-
Better to refine this to a type that depends on (m=S predm) so that the case (m=Z) may also be covered.

Shall start from the bottom of the matrix (last) and work up to row (FS FZ) using a traversal based on (weaken) and a binary map from index (Fin n) and oldvals to newvals.
-}

elimFirstCol : (xs : Matrix n (S predm) ZZ) -> Reader ZZGaussianElimination.gcdOfVectAlg (gexs : Matrix (S n) (S predm) ZZ ** (downAndNotRightOfEntryImpliesZ gexs FZ FZ, gexs `spanslz` xs, xs `spanslz` gexs))
elimFirstCol [] {predm} = return ( row {n=S predm} $ neutral ** ( nosuch, ([] ** Refl), ([neutral] ** Refl) ) )
	where
		nosuch : (i : Fin _) -> (j : Fin _)
			-> LTRel Z (finToNat i)
			-> LTERel (finToNat j) Z
			-> indices i j (row {n=S predm} Prelude.Algebra.neutral) = Pos 0
		nosuch FZ FZ _ = either (const Refl) (const Refl)
		nosuch (FS k) FZ _ = absurd k
		nosuch _ (FS k) _ = void . ( either succNotLTEzero SIsNotZ )
elimFirstCol mat {n=S predn} {predm} = do {
		gcdalg <- ask @{the (MonadReader ZZGaussianElimination.gcdOfVectAlg _) %instance}

		-- (v ** fn) : ( v : Vect _ ZZ ** ( i : Fin _ ) -> (index i matcolZ) `quotientOverZZ` (v <:> matcolZ) )
		{-
		This should still be viable it just hasn't been restored from alteration while diagnosing a compiler error.
		> let (v ** fn) = runGCDOfVectAlg gcdalg _ (getCol FZ mat)
		-}
		let (v ** fn) = runGCDOfVectAlg gcdalg (S predn) (getCol FZ mat)

		let bisWithGCD = the ((v<\>mat)::mat `spanslz` mat, mat `spanslz` (v<\>mat)::mat)
			(extendSpanningLZsByPreconcatTrivially {zs=[_]} spanslzrefl, mergeSpannedLZs spanslzRowTimesSelf spanslzrefl)


		{-
		This works fine
		> let ( endmat ** endmatPropFn ) = foldedFully v ?vQfunc

		This should too but doesn't
		> let ( endmat ** endmatPropFn ) = foldedFully v (mkQFunc fn)

		says

		"
		When checking ... w/ expected type
			ReaderT ...

		Type mismatch between
		        Matrix (S predn) (S predm) ZZ (Type of mat)
		and
		        Matrix (S predm) (S predn) ZZ (Expected type)
		"

		This is the same error as we described getting for (foldedFully) before, when (succImplWknStep) has (imat') occuring before it was declared as the witness of the dependent pair output.

		This doesn't work either, even though the inputs' type signatures are correct by definition. Hence it's probably an issue with pattern matching to expose the witness and proof of either (v ** fn) or this dependent pair (the output of foldedFully).

		> placeholder_witness : Vect (S predn) ZZ
		> placeholder_fn : ( i : Fin (S predn) )
			-> (index i $ getCol FZ mat) `quotientOverZZ` (placeholder_witness <:> (getCol FZ mat))
		> let ( endmat ** endmatPropFn ) = foldedFully placeholder_witness (mkQFunc placeholder_fn)

		However, if we write

		> placeholder_witness : Vect (S predn) ZZ
		> placeholder_fn : ( i : Fin (S predn) )
		> 	-> (index i $ getCol FZ mat) `quotientOverZZ` (placeholder_witness <:> (getCol FZ mat))
		> mkQFunc : ( ( i : Fin (S predn) )
		> 		-> (index i $ getCol FZ mat) `quotientOverZZ` (v <:> (getCol FZ mat)) )
		> 	-> ( ( i : Fin (S $ S predn) )
		> 		-> (indices i FZ $ (v<\>mat)::mat) `quotientOverZZ` (head $ v<\>mat) )
		> mkQFunc = ?mkQFunc_pr
		> placeholder_2ndfn : ( i : Fin (S $ S predn) )
		> 		-> (indices i FZ $ (v<\>mat)::mat) `quotientOverZZ` (head $ v<\>mat)
		> placeholder_2ndfn = mkQFunc placeholder_fn

		we get the opposite error:

		"
		Type mismatch between
		        Matrix (S predm) (S predn) ZZ (Type of mat)
		and
		        Matrix (S predn) (S predm) ZZ (Expected type)
		"

		without needing to apply (mkQFunc) inside the monad.

		After some revision we see we have to make (v) and (mat) explicit arguments of the (mkQFunc) deal. So we write

		> mkQFunc : (v : Vect (S predn) ZZ)
			-> (m : Matrix (S predn) (S predm) ZZ)
			-> ( ( i : Fin (S predn) )
				-> (index i $ getCol FZ m) `quotientOverZZ` (v <:> (getCol FZ m)) )
			-> ( ( i : Fin (S $ S predn) )
				-> (indices i FZ $ (v<\>m)::m) `quotientOverZZ` (head $ v<\>m) )

		> let ( endmat ** endmatPropFn ) = foldedFully v $ mkQFunc v mat fn

		and that works.
		-}
		let ( endmat ** endmatPropFn ) = foldedFully v $ mkQFunc v mat fn

		let ( headvecWasFixed, leftColZBelow, endmatBispansMatandgcd ) = endmatPropFn FZ

		return ( index FZ endmat ** (leftColZBelow, bispanslztrans endmatBispansMatandgcd bisWithGCD) )
	}
	where
		{-
		Structure of proof:

		succImplWknStep_Qfunclemma => succImplWknStep_stepQfunc => succImplWknStep_unplumbed => succImplWknStep => foldedFully
		(mkQfunc, foldedFully) => elimFirstCol (after some work)
		-}
		mkQFunc : (v : Vect (S predn) ZZ)
			-> (xs : Matrix (S predn) (S predm) ZZ)
			-> ( ( i : Fin (S predn) )
				-> (index i $ getCol FZ xs) `quotientOverZZ` (v <:> (getCol FZ xs)) )
			-> ( ( i : Fin (S $ S predn) )
				-> (indices i FZ $ (v<\>xs)::xs) `quotientOverZZ` (head $ v<\>xs) )
		mkQFunc v xs fn FZ = quotientOverZZreflFromEq $ indexFZIsheadValued {xs=v<\>xs}
		mkQFunc v xs fn (FS k) = ( (quotientOverZZreflFromEq $ sym $ indexMapChariz {k=k} {f=index FZ} {xs=xs}) `quotientOverZZtrans` fn k ) `quotientOverZZtrans` ( quotientOverZZreflFromEq $ sym $ headVecMatMultChariz {v=v} {xs=xs} )
		{-
		Section notes for succImplWknStep

		---

		We have learned of two obstructions to expressing (succImplWknStep) and its lemmas which must be taken into account in this design.

		1) If a dependent pair's proof's type is a function of the witness and has implicit arguments, that dependent pair will not be inferred correctly when used as an argument to a function, and this might only be revealed through type errors in (the left-hand side of) other definitions that are attempted within the function, such as in its where block, where such definitions have the arguments to the function in their assumptions/context (environment, scope).

			See (ImplicitArgsError) for simple examples of the problem.

			Implementing (foldAutoind) created a similar problem when using type-valued functions that took certain implicit arguments (see elimFirstCol-oldmaterial.idr, where we had to rewrite its (foldAutoind) into its (foldAutoind2)). However, the values of those type-valued functions did not clearly have implicit arguments.

		2) A triple of types in the righthand value of a dependent pair is not treated as a type when pattern matching on it, giving type errors when anything is done with the proof (getProof _) except using it as an argument to a function. Hence to get a function from dependent pairs to dependent pairs that applies the theorem proved, we must call a dependently typed but curried version of the function on the witness and proof of the dependent pair input. Whence (succImplWknStep_unplumbed) and the definition of (succImplWknStep) in terms of it.

			Note, we may write (the Type (Nat,Nat,Nat)), but using a predefined (Type) whose value is a triple does not get around the mismatch error.
		-}
		succImplWknStep_Qfunclemma : ( senior : Vect (S predm) ZZ ) -> ( srQfunc : ( i : Fin _ ) -> (indices i FZ (senior::mat)) `quotientOverZZ` (head senior) )
			-> ( imat : Matrix (S (S predn)) (S predm) ZZ )
			-> ( z : Matrix _ _ ZZ )
			-> ( quotchariz : ( k : Fin _ ) -> ( LinearCombinations.monoidsum $ zipWith (<#>) (index k z) (senior::mat) = index k imat ) )
			-> ( ( j : Fin _ ) -> (indices j FZ imat) `quotientOverZZ` (head senior) )
		{-
		-- This version is perhaps more readable.

		succImplWknStep_Qfunclemma senior srQfunc imat z quotchariz j ?= linearComboQuotientRelation_corrollary senior mat (index j z) (\i => quotientOverZZtrans (quotientOverZZreflFromEq $ sym indexFZIsheadValued) $ srQfunc i)
		succImplWknStep_Qfunclemma_lemma_1 = proof
			intros
			exact (getWitness value ** _)
			rewrite sym $ indexFZIsheadValued {xs=index j imat}
			rewrite cong {f=head} $ quotchariz j
			exact getProof value
		-}
		succImplWknStep_Qfunclemma senior srQfunc imat z quotchariz j = (getWitness lemma ** trans (getProof lemma) $ trans (cong {f=head} $ quotchariz j) $ sym $ indexFZIsheadValued {xs=index j imat})
			where
				lemma : (head $ monoidsum $ zipWith (<#>) (index j z) (senior::mat)) `quotientOverZZ` (head senior)
				lemma = linearComboQuotientRelation_corrollary senior mat (index j z) (\i => quotientOverZZtrans (quotientOverZZreflFromEq $ sym indexFZIsheadValued) $ srQfunc i)
		succImplWknStep_stepQfunc : ( senior : Vect (S predm) ZZ ) -> ( srQfunc : ( i : Fin _ ) -> (indices i FZ (senior::mat)) `quotientOverZZ` (head senior) )
			-> ( imat : Matrix (S (S predn)) (S predm) ZZ )
			-> ( reprolem : senior::mat `spanslz` imat )
			-> ( ( j : Fin _ ) -> (indices j FZ imat) `quotientOverZZ` (head senior) )
		succImplWknStep_stepQfunc senior srQfunc imat reprolem = succImplWknStep_Qfunclemma senior srQfunc imat (getWitness reprolem) (\k => trans (sym indexMapChariz) $ cong {f=index k} $ getProof reprolem)
		{-
		For the proof of (downAndNotRightOfEntryImpliesZ) for the output of the below function in human, consider the modification

		> updateAt (weaken fi) (<-> (Sigma.getWitness $ fn (weaken fi)) <#> senior) imat

		to imat. According to (fn $ weaken fi), we will get a value (imat') such that

		> indices (weaken fi) FZ imat'
			= head $ index (weaken fi) imat <-> (Sigma.getWitness $ fn (weaken fi)) <#> senior
			= head (index (weaken fi) imat) <-> head ( (Sigma.getWitness $ fn (weaken fi)) <#> senior )
			= head (index (weaken fi) imat) <-> (Sigma.getWitness $ fn (weaken fi)) <.> (head senior)
			=	(by getProof $ fn (weaken fi))
				head (index (weaken fi) imat) <-> head (index (weaken fi) imat)
			=	(by groupInverseIsInverseL $ head (index (weaken fi) imat))
			Pos Z
		-}
		-- Including proof the head is equal to senior just makes this step easier.
		succImplWknStep_unplumbed : ( senior : Vect (S predm) ZZ ) -> ( srQfunc : ( i : Fin _ ) -> (indices i FZ (senior::mat)) `quotientOverZZ` (head senior) )
			-> (fi : Fin (S predn))
			-> ( imat : Matrix (S (S predn)) (S predm) ZZ )
			-> ( senior = head imat, downAndNotRightOfEntryImpliesZ {n=S $ S predn} {m=S predm} imat (FS fi) FZ, imat `spanslz` (senior::mat), (senior::mat) `spanslz` imat )
			-> ( imat' : Matrix (S (S predn)) (S predm) ZZ ** ( senior = head imat', downAndNotRightOfEntryImpliesZ {n=S $ S predn} {m=S predm} imat' (weaken fi) FZ, imat' `spanslz` (senior::mat), (senior::mat) `spanslz` imat' ) )
		succImplWknStep_unplumbed senior srQfunc fi imat ( seniorIsImatHead, imatDANRZ, imatSpansOrig, origSpansImat ) = (jmat ** ( seniorIsJmatHead, jmatDANRZ, jmatBispansOrig ) )
			where
				fn : ( j : Fin _ ) -> (indices j FZ imat) `quotientOverZZ` (head senior)
				fn = succImplWknStep_stepQfunc senior srQfunc imat origSpansImat
				jmat : Matrix (S (S predn)) (S predm) ZZ
				jmat = updateAt (FS fi) (<-> (Sigma.getWitness $ fn (FS fi)) <#> senior) imat
				seniorIsJmatHead : senior = head jmat
				seniorIsJmatHead = trans seniorIsImatHead $ sym updateAtSuccRowVanishesUnderHead
				primatzAtWknFi : indices (FS fi) FZ jmat = Pos Z
				primatzAtWknFi = trans (cong {f=index FZ} $ indexUpdateAtChariz {xs=imat} {i=FS fi} {f=(<-> (Sigma.getWitness $ fn (FS fi)) <#> senior)}) $ trans (zipWithEntryChariz {i=FZ {k=predm}} {m=(<+>)} {x=index (FS fi) imat} {y=inverse $ (Sigma.getWitness $ fn (FS fi)) <#> senior}) $ trans (cong {f=plusZ $ indices (FS fi) FZ imat} $ trans (indexCompatInverse ((<#>) (Sigma.getWitness $ fn $ FS fi) senior) FZ) (cong {f=inverse} $ indexCompatScaling (Sigma.getWitness $ fn $ FS fi) senior FZ)) $ trans (cong {f=(<->) $ indices (FS fi) FZ imat} $ trans (cong {f=((Sigma.getWitness $ fn $ FS fi)<.>)} $ indexFZIsheadValued {xs=senior}) $ getProof $ fn $ FS fi) $ groupInverseIsInverseL $ indices (FS fi) FZ imat
				jmatDANRZ : downAndNotRightOfEntryImpliesZ jmat (weaken fi) FZ
				jmatDANRZ = weakenDownAndNotRight {prednel=fi} {mel=FZ} {mat=jmat} (afterUpdateAtCurStillDownAndNotRight {mat=imat} {prednel=fi} {mel=FZ} {f=(<-> (Sigma.getWitness $ fn (FS fi)) <#> senior)} imatDANRZ) primatzAtWknFi
				missingstep : head imat = (Algebra.unity::Algebra.neutral) <\> deleteRow (FS fi) imat
				missingstep = sym $ trans
					( timesVectMatAsLinearCombo (Algebra.unity::Algebra.neutral) $ deleteRow (FS fi) imat )
					$ trans ( cong {f=\m => monoidsum {t=Vect _} $ zipWith ((<#>) {a=ZZ}) (Algebra.unity::Algebra.neutral) m} $ headtails $ deleteRow (FS fi) imat )
					$ trans ( cong {f=monoidsum {a=Vect _ ZZ}} $ vecHeadtailsEq (zzVecScalarUnityIsUnity $ head $ deleteRow (FS fi) imat) Refl )
					$ trans monoidrec2D
					$ trans ( cong {f=((head $ deleteRow (FS fi) imat)<+>)} $ trans (sym $ timesVectMatAsLinearCombo Algebra.neutral $ tail $ deleteRow (FS fi) imat) $ zzVecNeutralIsVecMatMultZero (tail $ deleteRow (FS fi) imat) )
					$ trans ( zzVecNeutralIsNeutralL $ head $ deleteRow (FS fi) imat )
					$ deleteSuccRowVanishesUnderHead {k=fi} {xs=imat}
				jmatBispansOrig : jmat `bispanslz` (senior::mat)
				jmatBispansOrig = bispanslztrans (bispanslzreflFromEq {xs=jmat} $ cong {f=\z => updateAt (FS fi) (<-> z) imat} $ trans ( cong {f=((<#>) {a=ZZ} _)} $ trans seniorIsImatHead $ missingstep ) $ sym $ vectMatLScalingCompatibility {z=Sigma.getWitness $ fn $ FS fi} {la=Algebra.unity::Algebra.neutral} {rs=deleteRow (FS fi) imat}) $ bispanslztrans ( bispanslzSubtractiveExchangeAt (FS fi) {xs=imat} {z=(Sigma.getWitness $ fn (FS fi))<#>(Algebra.unity::Algebra.neutral)} ) $ (imatSpansOrig, origSpansImat)
		succImplWknStep : ( senior : Vect (S predm) ZZ ) -> ( srQfunc : ( i : Fin _ ) -> (indices i FZ (senior::mat)) `quotientOverZZ` (head senior) )
			-> (fi : Fin (S predn))
			-> ( imat : Matrix (S (S predn)) (S predm) ZZ ** ( senior = head imat, downAndNotRightOfEntryImpliesZ {n=S $ S predn} {m=S predm} imat (FS fi) FZ, imat `spanslz` (senior::mat), (senior::mat) `spanslz` imat ) )
			-> ( imat' : Matrix (S (S predn)) (S predm) ZZ ** ( senior = head imat', downAndNotRightOfEntryImpliesZ {n=S $ S predn} {m=S predm} imat' (weaken fi) FZ, imat' `spanslz` (senior::mat), (senior::mat) `spanslz` imat' ) )
		succImplWknStep senior srQfunc fi imatAndPrs = succImplWknStep_unplumbed senior srQfunc fi (getWitness imatAndPrs) (getProof imatAndPrs)
		{-
		Misleading error message from using name in type signature before it enters scope.

		---

		If you write

		> succImplWknStep : ( senior : Vect (S predm) ZZ ) -> ( srQfunc : ( i : Fin _ ) -> (indices i FZ (senior::mat)) `quotientOverZZ` (head senior) )
		> 	-> (fi : Fin (S predn))
		> 	-> ( imat : Matrix (S (S predn)) (S predm) ZZ ** ( senior = head imat, downAndNotRightOfEntryImpliesZ {n=S $ S predn} {m=S predm} imat (FS fi) FZ, imat' `spanslz` (senior::mat), (senior::mat) `spanslz` imat ) )
		> 	-> ( imat' : Matrix (S (S predn)) (S predm) ZZ ** ( senior = head imat', downAndNotRightOfEntryImpliesZ {n=S $ S predn} {m=S predm} imat' (weaken fi) FZ, imat' `spanslz` (senior::mat), (senior::mat) `spanslz` imat' ) )

		then on the 3rd line near the end, you see "imat'" when (imat') has not been defined yet, and it should read "imat".

		1) This creates a host of error messages saying they're from (foldedFully) when they're actually from (succImplWknStep).
		2) The error messages are misleading. In particular, it seems to say that one of the matrices must, whatever its height and width, have that width for its height and that height for its width.
		3) Using a (with (succImplWknStep ...)) or (let (x = succImplWknStep ...)) block in the definition of (foldedFully) is enough to trigger the error.

		One such error message:

		"
		Type mismatch between
		        Vect (S predn) ZZ (Type of v)
		and
		        Vect (S predm) ZZ (Expected type)

		Specifically:
		        Type mismatch between
		                predn
		        and
		                predm
		"

		A similar one was found indicating a type mismatch between (Matrix (S predn) (S predm) ZZ) and (Matrix (S predm) (S predn) ZZ), where both the argument chosen and the function's assigned type for that argument were equal to (Matrix (S predn) (S predm) ZZ).
		-}
		foldedFully : (v : Vect (S predn) ZZ)
			-> ( vmatQfunc : ( i : Fin _ ) -> (indices i FZ ((v <\> mat)::mat)) `quotientOverZZ` (head $ v <\> mat) )
			-> ( mats : Vect (S (S predn)) $ Matrix (S (S predn)) (S predm) ZZ ** (i : Fin (S (S predn))) -> succImplWknProp mat (v<\>mat) (S predn) i (index i mats) )
		foldedFully v vmatQfunc = foldAutoind2 {predn=S predn} (\ne => Matrix (S ne) (S predm) ZZ) (succImplWknProp mat (v <\> mat)) (succImplWknStep (v <\> mat) vmatQfunc) ( (v<\>mat)::mat ** (Refl, danrzLast ((v <\> mat)::mat), bispanslzrefl) )

{-
Reference
-----
gcdOfVectAlg = (k : Nat) -> (x : Vect k ZZ) -> ( v : Vect k ZZ ** ( i : Fin k ) -> (index i x) `quotientOverZZ` (v <:> x) )
-}

gaussElimlzIfGCD : Reader gcdOfVectAlg ( (xs : Matrix n m ZZ) -> (gexs : Matrix n' m ZZ ** (gexs `spanslz` xs, xs `spanslz` gexs, rowEchelon gexs)) )
-- gaussElimlzIfGCD2 : (xs : Matrix n m ZZ) -> Reader gcdOfVectAlg (gexs : Matrix n' m ZZ ** (gexs `spanslz` xs, xs `spanslz` gexs, rowEchelon gexs))



{-
Background info
-}



gcdOfVectZZ : (x : Vect n ZZ) -> ( v : Vect n ZZ ** ( i : Fin n ) -> (index i x) `quotientOverZZ` (v <:> x) )



{-
Main algorithm
-}



gaussElimlz : (xs : Matrix n m ZZ) -> (gexs : Matrix n' m ZZ ** (gexs `spanslz` xs, xs `spanslz` gexs, rowEchelon gexs))
gaussElimlz = runIdentity $ runReaderT gaussElimlzIfGCD (\k => gcdOfVectZZ {n=k})
-- Why is this wrong, for if we put the argument inside the ReaderT gaussElimlzIfGCD?
-- gaussElimlz = runIdentity . ((flip runReaderT) $ (\k => gcdOfVectZZ {n=k})) . gaussElimlzIfGCD2
