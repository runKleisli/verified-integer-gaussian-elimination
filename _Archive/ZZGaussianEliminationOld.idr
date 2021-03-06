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



zzZOrOrPosNeg : (z : ZZ) -> Either (z=Pos 0) $ Either (k : _ ** z = Pos (S k)) $ (k : _ ** z = NegS k)
zzZOrOrPosNeg (Pos Z) = Left Refl
zzZOrOrPosNeg (Pos (S k)) = Right (Left (k ** Refl))
zzZOrOrPosNeg (NegS k) = Right (Right (k ** Refl))



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
echTy : (xs : Matrix n m ZZ) -> (nel : Fin n) -> Type
echTy {n} {m} xs nel with (leadingNonzeroCalc $ index nel xs)
	| Right someNonZness = downAndNotRightOfEntryImpliesZ xs nel $ getWitness someNonZness
	| Left _ = (nelow : Fin n) -> (ltpr : finToNat nel `LTRel` finToNat nelow)
			-> index nelow xs = Algebra.neutral

rowEchelon : (xs : Matrix n m ZZ) -> Type
rowEchelon {n} {m} xs = (narg : Fin n) -> echTy xs narg



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



danrzTailHasLeadingZeros : downAndNotRightOfEntryImpliesZ (x::xs) FZ FZ -> getCol FZ xs = Algebra.neutral
-- Should do this by noting (getCol FZ xs = map (index FZ) xs) and (\j => danrz j FZ ?lt ?lte : (j : Fin _) -> index FZ $ index j xs = Pos 0) becomes by (trans (indexMapChariz {f=index FZ})) a ((j : Fin _) -> index j $ map (index FZ) xs = Pos 0). So we just need a function ( ((i : Fin _) -> index i xs = index i ys) -> xs = ys ).
danrzTailHasLeadingZeros danrz = vecIndexwiseEq (\j => trans (indexMapChariz {f=index FZ}) $ trans (danrz (FS j) FZ (zLtSuccIsTrue $ finToNat j) $ Right Refl) $ sym $ indexNeutralIsNeutral1D j)

bispansNulltailcolExtension : downAndNotRightOfEntryImpliesZ (x::xs) FZ FZ
	-> ys `bispanslz` map Vect.tail xs
	-> map ((Pos Z)::) ys `bispanslz` xs
bispansNulltailcolExtension = bispansNullcolExtension . danrzTailHasLeadingZeros

||| (x::xs) leads with a nonzero for x not 0
leadingNonzeroIsFZIfNonzero : Not (index FZ x = Pos Z) -> map Sigma.getWitness $ leadingNonzeroCalc x = Right FZ
leadingNonzeroIsFZIfNonzero {x=x::xs} nonz with ( runIso eitherBotRight $ map nonz $ mirror $ zzZOrOrPosNeg x )
	| Left (k ** prposS) = rewrite prposS in Refl
	| Right (k ** prnegS) = rewrite prnegS in Refl

-- Corrollary : decEq w/ eitherBotRight lets you extract rowEchelon proofs.
-- In particular,
||| x|xs
||| 0|_
||| 0|_
||| ...
||| has 0th-col 0 or its 0th row leads with a nonzero
danrzLeadingZeroAlt : downAndNotRightOfEntryImpliesZ (x::xs) FZ FZ -> Either (getCol FZ (x::xs)=Algebra.neutral) (map Sigma.getWitness $ leadingNonzeroCalc x = Right FZ)
danrzLeadingZeroAlt {x} {xs} danrz with ( decEq (index FZ x) $ Pos Z )
	| Yes preq = Left (vecHeadtailsEq preq $ danrzTailHasLeadingZeros danrz)
	| No prneq = Right $ leadingNonzeroIsFZIfNonzero prneq

||| Hopefully, this subsumes (lnzcElim).
lnzcElim2 : {v : Vect n ZZ}
	-> Either (v = Algebra.neutral) (someNonZness : _ ** leadingNonzeroCalc v = Right someNonZness)
lnzcElim2 {v} with (leadingNonzeroCalc v)
	| Right someNonZness = Right (someNonZness ** Refl)
	| Left pr = Left pr

-- Using (the (leadingNonzero _) $ Right someNonZness) while debugging the type.
||| ∀ xs : n by m
||| ∀ narg : Fin n
||| xs_narg = 0 or
||| leadingNonzeroCalc xs_narg = Right k,
||| 
||| where k gives:
||| 
|||           ∃nel
||| xs          |
|||       *****|*|***
||| narg--00000|x|***
|||       *****|*|***
|||
||| w/ x nonzero.
||| 
||| Explicitly,
||| a (Fin m) nel
||| & a proof that
||| xs_narg_nel nonzero
||| & ∀ i < nel, xs_narg_i = 0
||| i.e. xs_narg is 0 to the left of the column index (nel) given.
lnzcElim : {xs : Matrix n m ZZ}
	-> (narg : Fin n)
	-> Either (index narg xs = Algebra.neutral)
	(someNonZness : (nel : Fin _
			** ({i : _} -> LTRel (finToNat i) (finToNat nel)
					-> index i $ index narg xs = Pos 0,
				Not (index nel $ index narg xs = Pos 0)))
		** leadingNonzeroCalc $ index narg xs = Right someNonZness)
lnzcElim {xs} narg with (leadingNonzeroCalc $ index narg xs)
	| Right someNonZness = Right $ (someNonZness ** Refl)
	| Left pr = Left pr

-- This is actually a test goal for producing a (void) from conflicting (leadingNonzeroCalc)s.
||| Application of (lnzcElim)
||| 
||| If xs is a row echelon form n by m matrix,
||| and xs' is
||| 
||| 	0|xs_0
||| 	0|xs_1
||| 	...,
||| 
||| then xs'_narg = 0 or
||| leadingNonzeroCalc xs'_narg = Right k,
||| 
||| where k gives:
||| 
|||            ∃nel
||| xs'          |
|||       0|****|*|***
||| narg--0|0000|x|***
|||       0|****|*|***
|||
||| w/ x nonzero.
||| 
||| Explicitly,
||| a (Fin (S m)) nel
||| & a proof that
||| xs'_narg_nel nonzero
||| & ∀ i < nel, xs'_narg_i = 0
||| i.e. xs'_narg is 0 to the left of the column index (nel) given.
echElim1 : {xs : Matrix n m ZZ}
	-> rowEchelon xs
	-> Either (index narg $ map ((Pos 0)::) xs = Algebra.neutral)
	(someNonZness : (nel : Fin _
			** ({i : _} -> LTRel (finToNat i) (finToNat nel)
					-> index i $ index narg $ map ((Pos 0)::) xs = Pos 0,
				Not (index nel $ index narg $ map ((Pos 0)::) xs = Pos 0)))
		** leadingNonzeroCalc $ index narg $ map ((Pos 0)::) xs
			= Right someNonZness)
echElim1 {xs} {narg} echxs with (leadingNonzeroCalc $ index narg $ map ((Pos 0)::) xs)
	| Right someNonZness = lnzcElim narg
	| Left pr with (leadingNonzeroCalc $ index narg xs)
		| Right someOtherNZ = void
			$ (snd $ getProof $ someOtherNZ)
			$ trans (cong {f=index $ getWitness someOtherNZ}
				$ vectInjective2 {x=Pos 0} {y=Pos 0}
				$ trans (sym $ indexMapChariz {k=narg} {f=((Pos 0)::)}) pr)
			$ indexNeutralIsNeutral1D $ getWitness someOtherNZ
		| Left pr2 = ?echElim1_rhs_2

{-
Because this can be written, the problem with reading a (rowEchelon) in a trivial way
- extracting a value of an explicit type - may have been mainly a problem with the type
we were trying to extract TO, which was the (either _ _ $ leadingNonZeroCalc _) seen in the commented functions below.
-}
||| ∀ xs : n by m
||| ∀ narg : Fin n
||| ∀ echval : echTy xs narg
||| either echval gives
||| 
||| xs
|||       ********
||| narg--********
|||       00000000
|||       00000000
||| 
||| or we have a (Fin m) nel such that echval gives
||| 
|||           nel
||| xs         |
|||       ****|*|***
||| narg--****|*|***
|||       0000|0|***
|||       0000|0|***
extractEchAlt : (xs : Matrix n m ZZ)
	-> (narg : Fin n)
	-> (echval : echTy xs narg)
	-> Either
		(leadfn : (nelow : Fin n) -> (ltpr : finToNat narg `LTRel` finToNat nelow)
				-> index nelow xs = Algebra.neutral
			** echval ~=~ leadfn)
		(nel : Fin m ** (danrz : downAndNotRightOfEntryImpliesZ xs narg nel
			** echval ~=~ danrz))
extractEchAlt xs narg echval with (leadingNonzeroCalc $ index narg xs)
	| Right someNonZness = Right (getWitness someNonZness ** (echval ** Refl))
	| Left _ = Left (echval ** Refl)

{-
extractEchDanrz : (xs : Matrix n m ZZ)
	-> (narg : Fin n)
	-> echTy xs narg
	-> either
		( const {a=Type}
			((nelow : Fin n) -> (ltpr : finToNat narg `LTRel` finToNat nelow)
				-> index nelow xs = Algebra.neutral) )
		( (downAndNotRightOfEntryImpliesZ xs narg) . (Sigma.getWitness
			{P=\nel : Fin m =>
				({i : Fin m} -> finToNat i `LTRel` finToNat nel
					-> indices narg i xs = Pos 0,
				Not (indices narg nel xs = Pos 0))}) )
		$ leadingNonzeroCalc $ index narg xs
-- extractEchDanrz xs narg echval = ?echval'
-}
{-
extractEchDanrz xs narg echval with (leadingNonzeroCalc $ index narg xs)
	| Right someNonZness = echval
	| Left _ = echval
-}
{-
extractEchDanrz xs narg with (leadingNonzeroCalc $ index narg xs)
	| Right someNonZness = ?echval1
	| Left _ = ?echval2
-}
{-
extractEchDanrz xs narg echval with (leadingNonzeroCalc $ index narg xs)
	| value = ?extractEchDanrz'
-}

{-
echExtractDanrz : {narg : Fin n}
	-> (xs : Matrix n m ZZ)
	-> rowEchelon xs
	-> (someNonZnessNel : Fin m)
	-> ( someNonZnessFn : ((i : Fin m) -> LTRel (finToNat i) (finToNat someNonZnessNel)
			-> indices narg i xs = Pos 0,
		Not (indices narg someNonZnessNel xs = Pos 0)) )
	-> leadingNonzeroCalc $ index narg xs = Right (someNonZnessNel ** someNonZnessFn)
	-> downAndNotRightOfEntryImpliesZ xs narg someNonZnessNel
echExtractDanrz xs echxs someNonZnessNel someNonZnessFn lnzEq = ?echExtractDanrz'
-}

-- Corollary:
-- 
||| ∀ xs : n by m
||| ∀ echxs : rowEchelon xs
||| ∀ narg : Fin n
||| either echxs narg gives
||| 
||| xs
|||       ********
||| narg--********
|||       00000000
|||       00000000
||| 
||| or we have a (Fin m) nel such that echxs narg gives
||| 
|||           nel
||| xs         |
|||       ****|*|***
||| narg--****|*|***
|||       0000|0|***
|||       0000|0|***
extractEchAltStep2 : (xs : Matrix n m ZZ)
	-> (echxs : rowEchelon xs)
	-> (narg : Fin n)
	-> Either
		(leadfn : (nelow : Fin n) -> (ltpr : finToNat narg `LTRel` finToNat nelow)
				-> index nelow xs = Algebra.neutral
			** echxs narg ~=~ leadfn)
		(nel : Fin m ** (danrz : downAndNotRightOfEntryImpliesZ xs narg nel
			** echxs narg ~=~ danrz))
extractEchAltStep2 xs echxs narg = extractEchAlt xs narg $ echxs narg

lnzIndInvar : (lnz : leadingNonzero v)
	-> (lnz = Right (k ** pr))
	-> (pr' : _ ** leadingNonzeroCalc v = Right (k ** pr'))
lnzIndInvar {v} {k} {pr} lnz lnzEq with (leadingNonzeroCalc v)
	| Left prNeut = void $ snd pr $ flip trans indexReplicateChariz $ cong {f=index k} prNeut
	| Right (k' ** pr') = ?lnzIndInvar_r -- reduces to proving (k = k').

lnzIndInvar_r = proof
	intros
	claim lnzIndEq k = k'
	unfocus
	rewrite sym lnzIndEq
	exact (pr' ** Refl)
	-- lnzIndEq : k = k'
	let trich_kk' = trichotomy (finToNat k) (finToNat k')
	-- Approximately:
	--	> exact either _ (either (finToNatInjective k k') _) trich_kk'
	-- But really that's lazy
	claim nlkk' LT (finToNat k) (finToNat k') -> Void
	unfocus
	claim ngkk' LT (finToNat k') (finToNat k) -> Void
	unfocus
	exact either (absurd . nlkk') (either (finToNatInjective k k') $ absurd . ngkk') trich_kk'
	-- nlkk'
	intro hlkk'
	-- can't apply (fst pr') directly to (hlkk')
	let fst_pr' = fst pr'
	exact snd pr $ fst_pr' hlkk'
	-- ngkk'
	intro hgkk'
	let fst_pr = fst pr
	exact snd pr' $ fst_pr hgkk'

{-
Type inference gripe:

lnzcNullext : {v : Vect n ZZ} -> {k : Fin n}
	-> map getWitness $ leadingNonzeroCalc {n=n} v = Right k
	-> map getWitness $ leadingNonzeroCalc {n=S n} $ (Pos 0)::v = Right (FS k)
lnzcNullext {v} {k} lnzcEq = ?lnzcNullext_pr

When checking type of ZZGaussianElimination.lnzcNullext:
When checking argument n to ZZGaussianElimination.leadingNonzeroCalc:
        Type mismatch between
                n (Inferred value)
        and
                S n (Given value)

should just be

lnzcNullext : map getWitness $ leadingNonzeroCalc v = Right k
	-> map getWitness $ leadingNonzeroCalc $ (Pos 0)::v = Right (FS k)
-}

lnzcNullext : leadingNonzeroCalc v = Right (k ** pr)
	-> (pr' : ((i : Fin _) -> LTRel (finToNat i) (finToNat (FS k))
			-> index i $ (Pos 0)::v = Pos 0,
			Not (index (FS k) $ (Pos 0)::v = Pos 0))
		** leadingNonzeroCalc $ (Pos 0)::v = Right (FS k ** pr'))
lnzcNullext {v} {k} {pr} lnzcEq = ?lnzcNullext_pr

lnzcNullext_pr = proof
	intros
	claim lnz leadingNonzero $ Pos 0 :: v
	claim pr2 ((i : Fin _) -> LTRel (finToNat i) (finToNat (FS k)) -> index i $ (Pos 0)::v = Pos 0, Not (index (FS k) $ (Pos 0)::v = Pos 0))
	unfocus
	unfocus
	claim lnzEq lnz = Right (FS k ** pr2)
	unfocus
	-- Main goal
	exact lnzIndInvar lnz lnzEq
	-- pr2 on stack
	unfocus
	-- lnz on stack
	exact Right (FS k ** pr2)
	-- lnzEq on stack
	exact Refl
	-- pr2
	-- w/c should follow from lnzcEq/pr
	exact (_ $ fst pr, snd pr)
	intro ltkThenZ
	intro i
	intro ltSk
	claim f (c : Fin n ** i = FS c) -> index i (Pos 0 :: v) = Pos 0
	unfocus
	exact either f (cong {f=flip index $ Pos 0::v}) $ splitFinFS i
	-- f
	intro iSplit
	rewrite sym $ getProof iSplit
	exact ltkThenZ $ the (LT (finToNat $ getWitness iSplit) (finToNat k)) _
	-- i `leq` k
	exact fromLteSucc _
	rewrite cong {f=finToNat} $ getProof iSplit
	exact ltSk

	{-
	The (f) solution was originally written

	-- f
	> intro iSplit
	> rewrite sym $ getProof iSplit
	> exact ltkThenZ _
	> rewrite cong {f=finToNat} $ getProof iSplit
	-- i `leq` k
	> exact fromLteSucc ltSk

	but apparently the compiler won't do the (cong) rewrite, nor will the proof engine when you hole
	the proof off into a second proposition after the

	> exact ltkThenZ _

	So, we have to do the cong rewrite over the hole in (fromLteSucc _).
	-}

-- Now we just need to show (nel) as the value of above
-- induces (echxsPrependZ narg = danrz ... $ FS nel)
-- relating the (rowEchelon xs)@narg to the (rowEchelon $ map ((Pos 0)::) xs)@narg.
||| If xs is a row echelon form n by predm matrix,
||| and xs' is
||| 
||| 	0|xs_0
||| 	0|xs_1
||| 	...,
||| 
||| then
||| ∀ narg : Fin n
||| If xs'_narg has xs'_narg_someNonZnessNel as its first nonzero entry,
||| 
|||       someNonZnessNel
||| xs'          |
|||       0|****|*|***
||| narg--0|0000|x|***
|||       0|****|*|***
||| 	for x nonzero
||| 
||| we have
||| someNonZnessNel = FS leadeln
||| where leadeln satisfies
||| 
|||         leadeln
||| xs         |
|||       ****|*|***
||| narg--****|*|***
|||       0000|0|***
|||       0000|0|***
echReduce1 : {xs : Matrix n predm ZZ}
	-> {narg : Fin n}
	-> {someNonZnessNel : Fin (S predm)}
	-> {someNonZnessFn : ({i : Fin _} -> LTRel (finToNat i) (finToNat someNonZnessNel)
			-> indices narg i $ map ((Pos 0)::) xs = Pos 0,
		Not (indices narg someNonZnessNel $ map ((Pos 0)::) xs = Pos 0))}
	-> rowEchelon xs
	-> leadingNonzeroCalc $ index narg $ map ((Pos 0)::) xs
		= Right (someNonZnessNel ** someNonZnessFn)
	-> (leadeln : Fin predm ** (downAndNotRightOfEntryImpliesZ xs narg leadeln,
		someNonZnessNel = FS leadeln))
echReduce1 {someNonZnessNel} {someNonZnessFn} {xs} {narg} echxs lnzcEq
	with (splitFinFS someNonZnessNel)
		| Left fspr = ?echReduce1_rhs_FS -- (getWitness fspr ** (_, getProof fspr))
		-- Except we want to show that (getWitness fspr) comes from (echxs), or
		-- take it from (echxs) instead of using the (fspr) that comes from this.
		-- So, the (downAndNotRightOfEntryImpliesZ) indices must be proved universal.
		-- That's where (lnzcEq) comes in, and shows (someNonZnessNel) is the (FS)er.
		-- So we just need to prove (leadingNonzeroCalc) is compatible w/ tails,
		-- and then unlock the (leadingNonzeroCalc $ index nel xs) (with) block
		-- in (rowEchelon xs) in such a way that that equation remains applicable.
		-- Perhaps best would be for the goal to be the implication from such an eq.
		-- together w/ any (rowEchelon xs) that the danrz exists.
		| Right fzpr = ?echReduce1_rhs_FZ -- Absurd; FZ not leading 0 of (Pos 0)::_.

echelonNullcolExtension : {xs : Matrix n m ZZ}
	-> rowEchelon xs
	-> rowEchelon $ map ((Pos 0)::) xs
{-
echelonNullcolExtension {n} {m} {xs} echxs narg
	with (leadingNonzeroCalc $ index narg $ map ((Pos 0)::) xs)
	| Right someNonZness with someNonZness
		| (leadeln ** _) = ?nullcol_danrz
	| Left _ = ?nullcol_nelowfn
-}

echelonHeadnonzerovecExtension : {xs : Matrix n (S m) ZZ}
	-> map Sigma.getWitness $ leadingNonzeroCalc x = Right FZ
	-> rowEchelon xs
	-> rowEchelon (x::xs)
{-
So the below doesn't work because we can't get the value of the (rowEchelon xs) at (nargxs) to take into account that (index nargxs xs = Algebra.neutral).

Perhaps then (rowEchelon) should be rewritten as

rowEchelon : (xs : Matrix n m ZZ) -> Type
rowEchelon {n} {m} xs = (narg : Fin n) -> either ( const ((nelow : Fin n) -> (ltpr : finToNat narg `LTRel` finToNat nelow) -> index nelow xs = Algebra.neutral) ) ( (downAndNotRightOfEntryImpliesZ xs narg) . Sigma.getWitness ) $ leadingNonzeroCalc $ index narg xs

However, the problem isn't with producing (rowEchelon) values (see (echelonFromDanrzLast)), it's with inspecting them based on the known (leadingNonzeroCalc) value. So if a combinator can be written which converts it to the above form, the (rowEchelon) as it is shouldn't be a problem. But since the above form is superficially the same as the current one, perhaps it won't affect anything if we swap the definitions!

Another possibility is matching on not just

	(leadingNonzeroCalc $ index nargxs xs)

but

	(leadingNonzeroCalc $ index nargxs xs, echxs nargxs)

but trying that:

echelonHeadnonzerovecExtension {n} {m} {x} {xs} prleadFZ echxs (FS nargxs) with ((leadingNonzeroCalc $ index nargxs xs, echxs nargxs))
	| (Right someNonZness, echval) with someNonZness
		| (leadeln ** _) = ?echelonHeadnonzerovecExtension_rhs_2_right
	| (Left _, echval) = ?echelonHeadnonzerovecExtension_rhs_2_left

the (with) block is not resolved.

Letting (rowEchelon2) be written as the above alternative definition for (rowEchelon), there is a problem with the type which is preventing us from writing a (rowEchelon2 xs -> rowEchelon xs), where if you try and accept the (rowEchelon2 xs) argument and the argument (narg : Fin n) to the intended value, even when the latter is only matched on by a local function, at the same time as you pattern match on the (leadingNonzeroCalc $ index narg xs), then you'll get an error

"
Type mismatch between
        Fin n
and
        Fin m
"

-----

echelonHeadnonzerovecExtension {n} {m} {x} {xs} prleadFZ echxs FZ with (leadingNonzeroCalc x)
	| Right someNonZness with someNonZness
		| (leadeln ** _) = ?echelonHeadnonzerovecExtension_rhs_1_right
	-- Contradicts prleadFZ
	| Left _ = ?echelonHeadnonzerovecExtension_rhs_1_left
-- Roughly: echelonHeadnonzerovecExtension prleadFZ echxs (FS nargxs) = echxs nargxs
echelonHeadnonzerovecExtension {n} {m} {x} {xs} prleadFZ echxs (FS nargxs) with (leadingNonzeroCalc $ index nargxs xs)
	| Right someNonZness with someNonZness
		| (leadeln ** _) = ?echelonHeadnonzerovecExtension_rhs_2_right
	| Left _ = echxnxs
		where {
			mkLTwkn : (S predn) `LTRel` (finToNat nelow) -> (nelow = FS prednelow) -> predn `LTRel` finToNat prednelow
			runEchxs : (nelow : Fin n) -> (ltpr : (finToNat nargxs) `LTRel` (finToNat nelow)) -> Vect.index nelow xs = Algebra.neutral
			{-
			Can't figure out that (echxs) matched the (Left _) pattern.
			Instead, we might be able to give (echxs) the (Left _) value
			by rewriting (echxs nargxs), the value of which is a (with) block expressed in terms of (leadingNonzeroCalc (index nargxs xs)), by a proof that (leadingNonzeroCalc (index nargxs)) of the form (Left _).
			However, a proof of (index nargxs xs = Pos 0 :: replicate m (Pos 0)) doesn't seem to affect the value alone, so.
			-}
			runEchxs ?= echxs nargxs
			echxnxs : (snelow : Fin (S n)) -> (ltpr : (finToNat $ FS nargxs) `LTRel` (finToNat snelow)) -> Vect.index snelow (x::xs) = Algebra.neutral
			echxnxs snelow ltpr = ( \nelow_succeq : (nelow : Fin n ** snelow = FS nelow) => trans (cong {f=\i => index i (x::xs)} $ getProof nelow_succeq) $ runEchxs (getWitness nelow_succeq) (mkLTwkn {nelow=snelow} ltpr $ getProof nelow_succeq) ) $ gtnatFZImpliesIsFinSucc snelow $ natGtAnyImpliesGtZ (finToNat $ FS nargxs) (finToNat snelow) ltpr
		}
-}

danrzLastcolImpliesAllcol : {mat : Matrix (S _) (S mu) ZZ}
	-> downAndNotRightOfEntryImpliesZ mat FZ (last {n=mu})
	-> downAndNotRightOfEntryImpliesZ mat FZ mel
danrzLastcolImpliesAllcol danrzlast i j ltrel _ = danrzlast i j ltrel $ ltenatLastIsTrue2 j

danrzLastcolImpliesTailNeutral : {xs : Matrix n (S mu) ZZ} -> downAndNotRightOfEntryImpliesZ (x::xs) FZ (last {n=mu}) -> xs=Algebra.neutral
danrzLastcolImpliesTailNeutral {x} {xs} {n} {mu} danrz = uniformValImpliesReplicate (replicate (S mu) $ Pos 0) xs $ \na => uniformValImpliesReplicate (Pos 0) (index na xs) (fn na)
	where
		fn : (prednel : Fin n) -> (j : Fin (S mu)) -> indices prednel j xs = Pos 0
		fn prednel j = danrz (FS prednel) j (zLtSuccIsTrue $ finToNat prednel) (ltenatLastIsTrue2 j)

-- echelonTrivial : rowEchelon [x]



echelonFromDanrzLast : {mat : Matrix (S n) (S mu) ZZ}
	-> downAndNotRightOfEntryImpliesZ mat FZ (last {n=mu})
	-> rowEchelon mat
echelonFromDanrzLast {mat=x::xs} {n} {mu} danrz FZ with (leadingNonzeroCalc x)
	| Right someNonZness = danrzLastcolImpliesAllcol
		{mel=getWitness $ someNonZness} danrz
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
	| Right someNonZness = void $ (snd $ getProof someNonZness)
		$ flip trans (indexNeutralIsNeutral1D $ getWitness someNonZness)
		$ cong {f=index $ getWitness someNonZness}
		$ trans (cong {f=index k}
		$ danrzLastcolImpliesTailNeutral {x=x} {xs=xs} danrz)
		$ indexNeutralIsNeutral2D k
	| Left _ = ?echelonFromDanrzLast_rhs_2

echelonFromDanrzLast_rhs_1 = proof
  intros
  exact trans (cong {f=\ts => Vect.index nelow (x::ts)} $ danrzLastcolImpliesTailNeutral {x=x} {xs=xs} danrz) $ trans (cong {f=(\i => Vect.index i (x::Algebra.neutral))} $ getProof $ gtnatFZImpliesIsFinSucc nelow ltpr) $ indexNeutralIsNeutral2D _

echelonFromDanrzLast_rhs_2 = proof
  intros
  exact trans (cong {f=\ts => Vect.index nelow (x::ts)} $ danrzLastcolImpliesTailNeutral {x=x} {xs=xs} danrz) $ trans (cong {f=(\i => Vect.index i (x::Algebra.neutral))} $ getProof $ gtnatFZImpliesIsFinSucc nelow $ natGtAnyImpliesGtZ (S $ finToNat k) (finToNat nelow) ltpr) $ indexNeutralIsNeutral2D _



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
