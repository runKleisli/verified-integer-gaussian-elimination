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

import Control.Isomorphism



{-
Trivial lemmas and plumbing
-}



bileibniz : (f : a -> b -> c) -> (x1=x2) -> (y1=y2) -> f x1 y1 = f x2 y2
bileibniz f {x1} {x2} {y1} {y2} xeq yeq = rewrite (cong {f=f} xeq) in cong {f=f x2} yeq



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

total
notSNatLastLTEAnything : {n : Nat} -> {i : Fin (S n)} -> LTE (S $ finToNat $ last {n=n}) (finToNat i) -> Void
notSNatLastLTEAnything {n} {i=FZ} = uninhabited
notSNatLastLTEAnything {n=Z} {i=FS pri} = FinZElim pri
notSNatLastLTEAnything {n=S predn} {i=FS pri} = notSNatLastLTEAnything . fromLteSucc



finToNatWeaken : {k : Fin n} -> finToNat k = finToNat (weaken k)
finToNatWeaken {k=FZ} = Refl
finToNatWeaken {k=FS k} = cong {f=S} $ finToNatWeaken {k}

partitionNatWknLT : (pnel : Fin n) -> (el : Fin (S n)) -> (elDown : LTRel (finToNat $ weaken pnel) (finToNat el)) -> Either ( LTRel (finToNat $ FS pnel) (finToNat el) ) ( el=FS pnel )
partitionNatWknLT pnel el elDown = map (sym . (finToNatInjective (FS pnel) el)) $ lteToLTERel $ lteFromEqLeft (cong {f=S} $ sym finToNatWeaken) elDown
	where
		lteFromEqLeft : (a=b) -> LTE a c -> LTE b c
		lteFromEqLeft pr lel = rewrite (sym pr) in lel



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
|||
||| Extends one witness for some predicate
|||
||| p : (m : Nat) -> Fin (S m) -> a -> Type
|||
||| to a (Vect) of them.
|||
||| Best used with those (p) which are trivial for (last) and some (a).
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
|||
||| Same strength of result as foldAutoind, but where the predicate is of the form
|||
||| p : (m : Nat) -> Fin (S m) -> (a m) -> Type
|||
||| for when it isn't naturally expressed or proved without affecting
||| the type (a _) of the witnesses dealt with by this process.
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



{-
danrzTail : downAndNotRightOfEntryImpliesZ (x::xs) (weaken nel) mel -> downAndNotRightOfEntryImpliesZ xs nel mel
-}



weakenDownAndNotRight : (downAndNotRightOfEntryImpliesZ mat (FS prednel) mel) -> ((j : _) -> LTERel (finToNat j) (finToNat mel) -> indices (FS prednel) j mat = Pos Z) -> downAndNotRightOfEntryImpliesZ mat (weaken prednel) mel
weakenDownAndNotRight {prednel} {mat} danrz newzfn i j iDown jNotRight = either (\b => danrz i j b jNotRight) (\pr => trans (cong {f=\e => indices e j mat} pr) $ newzfn j jNotRight) $ partitionNatWknLT prednel i iDown

||| A special case of (weakenDownAndNotRight).
weakenDownAndNotRightFZ : (downAndNotRightOfEntryImpliesZ mat (FS prednel) FZ) -> (indices (FS prednel) FZ mat = Pos Z) -> downAndNotRightOfEntryImpliesZ mat (weaken prednel) FZ
weakenDownAndNotRightFZ {prednel} {mat} danrz newz i FZ iDown fzNotRight = either (\b => danrz i FZ b fzNotRight) (\pr => trans (cong {f=\e => indices e FZ mat} pr) newz) $ partitionNatWknLT prednel i iDown

{-
Obviously you want

> weakenDownAndNotRightFZ : (downAndNotRightOfEntryImpliesZ mat (FS prednel) FZ) -> (indices (FS prednel) FZ mat = Pos Z) -> downAndNotRightOfEntryImpliesZ mat (weaken prednel) FZ
> weakenDownAndNotRightFZ {prednel} {mat} danrz newz = weakenDownAndNotRight {mel=FZ} danrz ?newzfn

but the implementation of (newzfn) is not readily available, so nope.

> :search {k : Nat} -> (j : Fin (S k)) -> LTERel (finToNat j) (finToNat $ FZ {k=k}) -> (j=FZ)
No results found
> :search {k : Nat} -> (j : Fin (S k)) -> LTE (finToNat j) (finToNat $ FZ {k=k}) -> (j=FZ)
No results found
-}



total
afterUpdateAtCurStillDownAndNotRight : (downAndNotRightOfEntryImpliesZ mat (FS prednel) mel) -> (downAndNotRightOfEntryImpliesZ (updateAt (FS prednel) f mat) (FS prednel) mel)
afterUpdateAtCurStillDownAndNotRight {prednel=FZ} {mat=x::y::xs} {mel} danrz FZ j iDown jNotRight = void $ succNotLTEzero $ iDown
afterUpdateAtCurStillDownAndNotRight {prednel=FZ} {mat=x::y::xs} {mel} danrz (FS FZ) j iDown jNotRight = void $ succNotLTEzero $ fromLteSucc iDown
afterUpdateAtCurStillDownAndNotRight {prednel=FZ} {mat=x::y::xs} {mel} danrz (FS $ FS i) j iDown jNotRight = danrz (FS $ FS i) j iDown jNotRight
afterUpdateAtCurStillDownAndNotRight {prednel=FS predednel} {mat=x::xs} {f} danrz FZ j iDown jNotRight = danrz FZ j iDown jNotRight
afterUpdateAtCurStillDownAndNotRight {prednel=FS predednel} {mat=x::xs} {mel} {f} danrz (FS i) j iDown jNotRight = afterUpdateAtCurStillDownAndNotRight {prednel=predednel} {mat=xs} {mel=mel} {f=f} (\i_xs => \j_xs => \iDown_xs => \jNotRight_xs => danrz (FS i_xs) j_xs (LTESucc iDown_xs) jNotRight_xs) i j (fromLteSucc iDown) jNotRight



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
			| Left _ = (nelow : Fin n) -> (ltpr : finToNat nel `LTRel` finToNat nelow) -> index nelow xs = Algebra.neutral



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
		divisorByDistrib' = trans (ringOpIsDistributiveR dxx dxxs z) $ trans (bileibniz (<+>) prxx prxxs) $ sym $ monoidrec1D {v=xx} {vs=xxs}



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
				jmatDANRZ = weakenDownAndNotRightFZ {prednel=fi} {mat=jmat} (afterUpdateAtCurStillDownAndNotRight {mat=imat} {prednel=fi} {mel=FZ} {f=(<-> (Sigma.getWitness $ fn (FS fi)) <#> senior)} imatDANRZ) primatzAtWknFi
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



bispansNulltailcolExtension : downAndNotRightOfEntryImpliesZ (x::xs) FZ FZ
	-> ys `bispanslz` map tail xs
	-> map ((Pos Z)::) ys `bispanslz` xs

-- Corrollary : decEq w/ eitherBotRight lets you extract rowEchelon proofs.
danrzLeadingZeroAlt : downAndNotRightOfEntryImpliesZ (x::xs) FZ FZ -> Either (getCol FZ (x::xs)=Algebra.neutral) (pr : _ ** leadingNonzeroCalc x = Right ( FZ ** pr ))

echelonNullcolExtension : rowEchelon xs -> rowEchelon $ map ((Pos 0)::) xs

{-
When we use this type signature we get the error "No such variable k" when using it,
as in the ImplicitArgsError error message.
Presumably (k) would be the Nat whose successor is the length of (x).

> echelonHeadnonzerovecExtension : ( leadingNonzeroCalc x = Right ( FZ ** pr ) )
> 	-> rowEchelon xs
> 	-> rowEchelon (x::xs)

specifically, we got the error from using the line

> let endmatEch = echelonHeadnonzerovecExtension {x=xFCE} (getProof headxFCELeadingNonzero) xsNullcolextElimEch

(in (gaussElimlzIfGCD2)'s (No) case) instead of what would now be written

> let endmatEch = echelonHeadnonzerovecExtension {x=xFCE} headxFCELeadingNonzero xsNullcolextElimEch
-}
echelonHeadnonzerovecExtension : ( pr : _ ** leadingNonzeroCalc x = Right ( FZ ** pr ) )
	-> rowEchelon xs
	-> rowEchelon (x::xs)

danrzLastcolImpliesAllcol : {mat : Matrix (S _) (S mu) ZZ}
	-> downAndNotRightOfEntryImpliesZ mat FZ (last {n=mu})
	-> downAndNotRightOfEntryImpliesZ mat FZ mel

danrzLastcolImpliesTailNeutral : {x : Vect (S mu) ZZ} -> downAndNotRightOfEntryImpliesZ (x::xs) FZ (last {n=mu}) -> xs=Algebra.neutral

-- echelonTrivial : rowEchelon [x]



echelonFromDanrzLast : {mat : Matrix (S n) (S mu) ZZ}
	-> downAndNotRightOfEntryImpliesZ mat FZ (last {n=mu})
	-> rowEchelon mat
echelonFromDanrzLast {mat=x::xs} {n} {mu} danrz FZ with (leadingNonzeroCalc x)
	| Right someNonZness with someNonZness
		| (leadeln ** _) = danrzLastcolImpliesAllcol {mel=leadeln} danrz
	| Left _ = ?echelonFromDanrzLast_rhs_1
	{-
	Doing this made the module take 20 seconds longer to compile, 2:40 total.

	> | Left _ = \nelow => \ltpr => trans (cong {f=\ts => Vect.index nelow (x::ts)} $ danrzLastcolImpliesTailNeutral {x=x} {xs=xs} danrz) $ trans (cong {f=(\i => Vect.index i (x::Algebra.neutral))} $ getProof $ gtnatFZImpliesIsFinSucc nelow ltpr) $ indexNeutralIsNeutral2D _

	The above was debugged by making a hole like this

	> | Left _ = ?echelonFromDanrzLast_rhs_1_1

	making sure a correct REPL proof existed, then finding some missing implicit args
	required by the compiler by putting that proof in the module, and whenever a type
	mismatch occurred looking at the type expected and assuming it was a value from
	the context that was needed as an implicit argument somewhere.
	-}
echelonFromDanrzLast {mat=x::xs} danrz (FS k) with (leadingNonzeroCalc $ index k xs)
	-- indexNeutralIsNeutral1D
	| Right someNonZness with (someNonZness)
		| (leadeln ** (_, prNonZ)) = void $ prNonZ $ flip trans (indexNeutralIsNeutral1D leadeln) $ cong {f=index leadeln} $ trans (cong {f=index k} $ danrzLastcolImpliesTailNeutral {x=x} {xs=xs} danrz) $ indexNeutralIsNeutral2D k
	| Left _ = ?echelonFromDanrzLast_rhs_2

echelonFromDanrzLast_rhs_1 = proof
  intros
  exact trans (cong {f=\ts => Vect.index nelow (x::ts)} $ danrzLastcolImpliesTailNeutral {x=x} {xs=xs} danrz) $ trans (cong {f=(\i => Vect.index i (x::Algebra.neutral))} $ getProof $ gtnatFZImpliesIsFinSucc nelow ltpr) $ indexNeutralIsNeutral2D _

echelonFromDanrzLast_rhs_2 = proof
  intros
  exact trans (cong {f=\ts => Vect.index nelow (x::ts)} $ danrzLastcolImpliesTailNeutral {x=x} {xs=xs} danrz) $ trans (cong {f=(\i => Vect.index i (x::Algebra.neutral))} $ getProof $ gtnatFZImpliesIsFinSucc nelow $ natGtAnyImpliesGtZ (S $ finToNat k) (finToNat nelow) ltpr) $ indexNeutralIsNeutral2D _



{-
Reference
-----
rowEchelon : (xs : Matrix n m ZZ) -> Type
rowEchelon {n} {m} xs = (narg : Fin n) -> (ty narg)
	where
		ty : Fin n -> Type
		ty nel with (leadingNonzeroCalc $ index nel xs)
			| Right someNonZness with someNonZness
				| (leadeln ** _) = downAndNotRightOfEntryImpliesZ xs nel leadeln
			| Left _ = (nelow : Fin n) -> (ltpr : finToNat nel `LTRel` finToNat nelow) -> index nelow xs = Algebra.neutral
-}



gaussElimlzIfGCD : Reader ZZGaussianElimination.gcdOfVectAlg ( (xs : Matrix n m ZZ) -> (n' : Nat ** (gexs : Matrix n' m ZZ ** (rowEchelon gexs, gexs `bispanslz` xs))) )

gaussElimlzIfGCD2 : (xs : Matrix n (S predm) ZZ) -> Reader ZZGaussianElimination.gcdOfVectAlg ( n' : Nat ** (gexs : Matrix n' (S predm) ZZ ** (rowEchelon gexs, gexs `bispanslz` xs)) )
{-
-- Template
gaussElimlzIfGCD2 xs = do {
		gcdalg <- ask @{the (MonadReader gcdOfVectAlg _) %instance}
		return $ believe_me "shshs"
		-- return (the Nat _ ** (?foo ** (?bar1,?bar2,?bar3)))
	}
-}
{-
( echFromDanrz $ fst $ getProof k, snd $ getProof k)
-->
(\f => \(a,b) => (f a, b)) echFromDanrz $ getProof k

"
When checking deferred type of ZZGaussianElimination.case block in gaussElimlzIfGCD2 at ZZGaussianElimination.idr:821:71:
No such variable mu
"
-}
gaussElimlzIfGCD2 xs {predm=Z} = map (\k => (_ ** (getWitness k ** ( echelonFromDanrzLast $ fst $ getProof k, snd $ getProof k)))) $ elimFirstCol xs
{-
We handle recursion in different ways depending on whether the first column is neutral.
Since (with) blocks can't access local functions (unless local to the case?), and (case)
blocks have totality problems, we write it as a wrapping of a local function which
pattern matches on the equality decision.
-}
gaussElimlzIfGCD2 xs {predm = S prededm} = gaussElimlzIfGCD2_gen $ decEq (getCol FZ xs) Algebra.neutral
	where
		gaussElimlzIfGCD2_gen : Dec (getCol FZ xs = Algebra.neutral) -> Reader ZZGaussianElimination.gcdOfVectAlg ( n' : Nat ** (gexs : Matrix n' (S $ S prededm) ZZ ** (rowEchelon gexs, gexs `bispanslz` xs)) )
		{-
		If first col neutral then we can reduce the process
		to that on the value of (map tail).
		-}
		gaussElimlzIfGCD2_gen (Yes prNeut) = do {
				( nold ** (matold ** (echold, bisold)) )
					<- gaussElimlzIfGCD2 $ map tail xs
				return ( nold ** (map ((Pos 0)::) matold ** (echelonNullcolExtension echold, bispansNullcolExtension prNeut bisold)) )
			}
		{-
		Otherwise it's nonneutral, so we can show that since the elimFirstCol
		is DANRZ FZ FZ, its first row's leading nonzero entry is FZ. This leads
		to promoting the (rowEchelon) of one matrix to one with the same
		first row as the elimFirstCol.
		-}
		gaussElimlzIfGCD2_gen (No prNonneut) = do {
				-- Perform elimination on the first column.
				(xFCE::xsFCE ** (xnxsFCEdanrz, fceBisxs))
					<- elimFirstCol xs
				-- Recurse, eliminating the tail.
				(elimLen ** (xselim ** (xselimEch, coltailxsFCEBisElim)))
					<- gaussElimlzIfGCD2 $ map tail xsFCE

				{-
				Add the head of the first-column elimination
				to the tail's elimination to get the final elim.
				-}
				let endmat = xFCE::map ((Pos Z)::) xselim

				-- The final elim is bispannable with the original matrix.
				{-
				Chopping off a column of leading zeros of a matrix,
				finding a matrix bispannable with that, and adding
				leading zeros to that produces a matrix bispannable to
				the first matrix.

				Equivalently, we may let that first matrix equal the tail
				of one for which we have proof that the first column is
				zero below the matrix's head.

				We let the first matrix be the tail of the
				first-column elimination of (xs).
				-}
				let xsNullcolextElimBisFCE = bispansNulltailcolExtension
					xnxsFCEdanrz coltailxsFCEBisElim
				{-
				Introducing the head of the first-column elimination
				of (xs) to two matrices preserves their bispannability.

				Hence, from a matrix bispannable with the tail of the
				first-column elimination we produce one bispannable with
				the first-column elimination.
				-}
				let endmatBisxnFCE = bispansSamevecExtension
					xsNullcolextElimBisFCE xFCE
				-- This is hence bispannable with the original matrix.
				let endmatBisxs = bispanslztrans endmatBisxnFCE fceBisxs

				-- The final elim is in row echelon form.
				{-
				Adding a column of leading zeros preserves row echelon.
				Hence the eliminated tail of the original matrix is.
				-}
				let xsNullcolextElimEch = echelonNullcolExtension
					xselimEch
				{-
				Since the first-column elimination is zero in the first
				column while below the first row, it is either zero in
				the whole column or its first row's head is nonzero.

				But if the first column were zero, so would the original
				matrix have been, which we assumed was false.

				Hence, the leading nonzero entry of the first row
				is the head.
				-}
				let xnxsFCEFCZOrHeadxFCELeadingNonzero = mirror $ danrzLeadingZeroAlt xnxsFCEdanrz
				let xsFCZOrHeadxFCELeadingNonzero = map (spansImpliesSameFirstColNeutrality $ fst fceBisxs) xnxsFCEFCZOrHeadxFCELeadingNonzero
				let headxFCELeadingNonzero = runIso eitherBotRight $ map prNonneut xsFCZOrHeadxFCELeadingNonzero
				{-
				Thus, since the first row is the same for the final elim,
				they have the same leading zero, and this gives proof
				that the matrix is zero down and not right of the head's
				leading zero. This shows the final elim is (rowEchelon).
				-}
				let endmatEch = echelonHeadnonzerovecExtension {x=xFCE} headxFCELeadingNonzero xsNullcolextElimEch

				return (_ ** (endmat ** (endmatEch, endmatBisxs)))
			}



{-
Background info
-}



gcdOfVectZZ : (x : Vect n ZZ) -> ( v : Vect n ZZ ** ( i : Fin n ) -> (index i x) `quotientOverZZ` (v <:> x) )



{-
Main algorithm
-}



gaussElimlz : (xs : Matrix n m ZZ) -> (n' : Nat ** (gexs : Matrix n' m ZZ ** (rowEchelon gexs, gexs `bispanslz` xs)))
gaussElimlz = runIdentity $ runReaderT gaussElimlzIfGCD (\k => gcdOfVectZZ {n=k})
-- Why is this wrong, for if we put the argument inside the ReaderT gaussElimlzIfGCD?
-- gaussElimlz = runIdentity . ((flip runReaderT) $ (\k => gcdOfVectZZ {n=k})) . gaussElimlzIfGCD2
