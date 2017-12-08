module ZZGaussianEliminationRedo

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

import RowEchelon
import ZZDivisors

import FinOrdering

import Control.Isomorphism



{-
Table of Contents:

* The induction algorithm used to verify first-column elimination
* Nice things for elimination algorithms to talk about
* Preliminary arguments to (elimFirstCol)
* Main elimination algorithms
-}



{-
The induction algorithm used to verify first-column elimination
-}



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
Nice things for elimination algorithms to talk about
-}



succImplWknProp :
	(omat : Matrix predonnom (S predm) ZZ)
	-> (senior : Vect (S predm) ZZ)
	-> (nu : Nat)
	-> (fi : Fin (S nu))
	-> Matrix (S nu) (S predm) ZZ
	-> Type
succImplWknProp omat senior nu fi tmat =
	( senior = head tmat
	, downAndNotRightOfEntryImpliesZ tmat fi FZ
	, tmat `bispanslz` (senior::omat) )

succImplWknPropSec2 :
	(nu : Nat)
	-> (fi : Fin (S nu))
	-> Matrix (S nu) (S predm) ZZ
	-> Type
succImplWknPropSec2 nu fi tmat = downAndNotRightOfEntryImpliesZ tmat fi FZ

danrzLast : (omat : Matrix (S predn) (S predm) ZZ)
	-> succImplWknPropSec2 predn (last {n=predn}) omat
danrzLast omat = (\i => \j => void . notSNatLastLTEAnything)



{-
Preliminary arguments to (elimFirstCol)
-}



{- (elimFirstCol) lemmas parameters -}
parameters (predm : Nat) {

{- (mkQFunc) parameters -}
parameters (predn : Nat) {

mkQFunc : (v : Vect (S predn) ZZ)
	-> (xs : Matrix (S predn) (S predm) ZZ)
	-> ( ( i : Fin (S predn) )
		-> (index i $ getCol FZ xs) `quotientOverZZ` (v <:> (getCol FZ xs)) )
	-> ( ( i : Fin (S $ S predn) )
		-> (indices i FZ $ (v<\>xs)::xs) `quotientOverZZ` (head $ v<\>xs) )
mkQFunc v xs fn FZ = quotientOverZZreflFromEq $ indexFZIsheadValued {xs=v<\>xs}
mkQFunc v xs fn (FS k) =
	( (quotientOverZZreflFromEq $ sym $ indexMapChariz {k=k} {f=index FZ} {xs=xs})
		`quotientOverZZtrans` fn k )
	`quotientOverZZtrans`
	( quotientOverZZreflFromEq $ sym $ headVecMatMultChariz {v=v} {xs=xs} )

} {- (mkQFunc) parameters -}



{- succImplWknStep lemmas parameters -}
parameters (
	mat : Matrix _ (S predm) ZZ
	, predn : Nat
	, senior : Vect (S predm) ZZ
	, srQfunc : ( i : Fin _ )
		-> (indices i FZ (senior::mat)) `quotientOverZZ` (head senior)
	, imat : Matrix (S (S predn)) (S predm) ZZ
	) {

succImplWknStep_Qfunclemma :
	( z : Matrix _ _ ZZ )
	-> ( quotchariz :
		( k : Fin _ )
		-> ( LinearCombinations.monoidsum
			$ zipWith (<#>) (index k z) (senior::mat)
			= index k imat ) )
	-> ( j : Fin _ ) -> (indices j FZ imat) `quotientOverZZ` (head senior)
succImplWknStep_Qfunclemma z quotchariz j
	= (getWitness lemma **
		trans (getProof lemma)
		$ trans (cong {f=head} $ quotchariz j)
		$ sym $ indexFZIsheadValued {xs=index j imat})
	where
	lemma : (head $ monoidsum $ zipWith (<#>) (index j z) (senior::mat))
		`quotientOverZZ` (head senior)
	lemma = linearComboQuotientRelation_corrollary senior mat (index j z)
		(\i => quotientOverZZtrans
			(quotientOverZZreflFromEq $ sym indexFZIsheadValued)
			$ srQfunc i)

succImplWknStep_stepQfunc :
	( reprolem : senior::mat `spanslz` imat )
	-> ( j : Fin _ ) -> (indices j FZ imat) `quotientOverZZ` (head senior)
succImplWknStep_stepQfunc reprolem = succImplWknStep_Qfunclemma (getWitness reprolem)
	(\k => trans (sym indexMapChariz)
		$ cong {f=index k} $ getProof reprolem)



{-
COMMENT - (succImplWknStep_unplumbed) PARAMETERS ERROR

Tried to use parameters to treat the assumptions to (succImplWknStep_unplumbed) as
both a (succImplWknProp) value and a tuple (as it's defined to be). The parameters
in the tuple can't be unpacked from it, and tupled definitions won't work neither
as a tupled parameter nor a tuple set equal to the (succImplWknProp) parameter.

Got error:

"
When checking left hand side of ZZGaussianEliminationRedo.seniorIsImatHead:
Can't match on seniorIsImatHead _
                                predm
                                mat
                                predn
                                senior
                                srQfunc
                                imat
                                predm
                                fi
                                prfTuple
"

Same error for others.



Attempted code:

> {- (succImplWknStep_unplumbed) & lemmas parameters -}
> parameters (
> 	fi : Fin (S predn)
> 	, prfTuple : succImplWknProp mat senior (S predn) (FS fi) imat
> 	) {

> seniorIsImatHead : ( senior = head imat )
> seniorIsImatHead = fst prfTuple

> imatDANRZ : downAndNotRightOfEntryImpliesZ imat (FS fi) FZ
> imatDANRZ = let (_,a,_,_) = prfTuple in a

> imatSpansOrig : imat `spanslz` (senior::mat)
> imatSpansOrig with ( prfTuple )
> 	| (_,_,a,_) = a

> origSpansImat : (senior::mat) `spanslz` imat
> origSpansImat with ( prfTuple )
> 	| (_,_,_,a) = a

> } {- (succImplWknStep_unplumbed) & lemmas parameters -}



Still similar errors here:



> {- (succImplWknStep_unplumbed) & lemmas parameters -}
> parameters (
> 	fi : Fin (S predn)
> 	, seniorIsImatHead : ( senior = head imat )
> 	, imatDANRZ : downAndNotRightOfEntryImpliesZ imat (FS fi) FZ
> 	, imatSpansOrig : imat `spanslz` (senior::mat)
> 	, origSpansImat : (senior::mat) `spanslz` imat
> 	) {

> succImplWknStep_stepQfunc' : ( j : Fin _ )
> 	-> (indices j FZ imat) `quotientOverZZ` (head senior)
> succImplWknStep_stepQfunc' = succImplWknStep_stepQfunc origSpansImat



And trying to make sure we use all the same implicit parameters we supplied to the
original definition, we get a different error, saying the (predm) in the type of
(imat) doesn't match the (predm) we're passing (downAndNotRightOfEntryImpliesZ):



> {- (succImplWknStep_unplumbed) & lemmas parameters -}
> parameters (
> 	fi : Fin (S predn)
> 	, seniorIsImatHead : ( senior = head imat )
> 	, imatDANRZ : downAndNotRightOfEntryImpliesZ {n=S $ S predn} {m=S predm} imat (FS fi) (FZ {k=predm})
> 	, imatSpansOrig : imat `spanslz` (senior::mat)
> 	, origSpansImat : (senior::mat) `spanslz` imat
> 	) {

> succImplWknStep_stepQfunc' : ( j : Fin _ )
> 	-> (indices j FZ imat) `quotientOverZZ` (head senior)

> } {- (succImplWknStep_unplumbed) & lemmas parameters -}



Finally, we see that the error that (predm) fails to match with itself
occurs when an extra parameter block is introduced to hold anything further,
whether or not it has any dependence on (predm).

In particular, if (fi : Fin (S predn)) from below is made the sole parameter to
the new block, this causes the error.



END COMMENT - (succImplWknStep_unplumbed) PARAMETERS ERROR

-}



{-
For the proof of (downAndNotRightOfEntryImpliesZ) for the output of the below function in human, consider the modification

> updateAt (weaken fi) (<-> (Sigma.getWitness $ fn (weaken fi)) <#> senior) imat

to imat. According to (fn $ weaken fi), we will get a value (imat') such that

> indices (weaken fi) FZ imat'
	= head $ index (weaken fi) imat <-> (Sigma.getWitness $ fn (weaken fi)) <#> senior
	= head (index (weaken fi) imat)
		<-> head ( (Sigma.getWitness $ fn (weaken fi)) <#> senior )
	= head (index (weaken fi) imat)
		<-> (Sigma.getWitness $ fn (weaken fi)) <.> (head senior)
	=	(by getProof $ fn (weaken fi))
	head (index (weaken fi) imat) <-> head (index (weaken fi) imat)
	=	(by groupInverseIsInverseL $ head (index (weaken fi) imat))
	Pos Z
-}
-- Including proof the head is equal to senior just makes this step easier.

succImplWknStep_unplumbed :
	(fi : Fin (S predn))
	-> succImplWknProp mat senior (S predn) (FS fi) imat
	-> ( imat' : Matrix (S (S predn)) (S predm) ZZ **
		succImplWknProp mat senior (S predn) (weaken fi) imat' )
succImplWknStep_unplumbed fi ( seniorIsImatHead, imatDANRZ, imatSpansOrig, origSpansImat )
	= (jmat ** ( seniorIsJmatHead, jmatDANRZ, jmatBispansOrig ) )
	where
		fn : ( j : Fin _ ) -> (indices j FZ imat) `quotientOverZZ` (head senior)
		fn = succImplWknStep_stepQfunc origSpansImat
		jmat : Matrix (S (S predn)) (S predm) ZZ
		jmat = updateAt (FS fi)
			(<-> (Sigma.getWitness $ fn (FS fi)) <#> senior)
			imat
		seniorIsJmatHead : senior = head jmat
		seniorIsJmatHead = trans seniorIsImatHead
			$ sym updateAtSuccRowVanishesUnderHead
		primatzAtWknFi : indices (FS fi) FZ jmat = Pos Z
		primatzAtWknFi =
			trans (cong {f=index FZ}
				$ indexUpdateAtChariz {xs=imat} {i=FS fi}
				{f=(<-> (Sigma.getWitness $ fn (FS fi)) <#> senior)})
			$ trans (zipWithEntryChariz {i=FZ {k=predm}} {m=(<+>)}
				{x=index (FS fi) imat}
				{y=inverse $ (Sigma.getWitness $ fn (FS fi)) <#> senior})
			$ trans (cong {f=plusZ $ indices (FS fi) FZ imat}
				$ trans (indexCompatInverse
					((<#>) (Sigma.getWitness $ fn $ FS fi) senior)
					FZ)
				(cong {f=inverse} $ indexCompatScaling
					(Sigma.getWitness $ fn $ FS fi)
					senior
					FZ))
			$ trans (cong {f=(<->) $ indices (FS fi) FZ imat}
				$ trans (cong {f=((Sigma.getWitness $ fn $ FS fi)<.>)}
					$ indexFZIsheadValued {xs=senior})
				$ getProof $ fn $ FS fi)
			$ groupInverseIsInverseL $ indices (FS fi) FZ imat
		jmatDANRZ : downAndNotRightOfEntryImpliesZ jmat (weaken fi) FZ
		jmatDANRZ = weakenDownAndNotRightFZ {prednel=fi} {mat=jmat}
			(afterUpdateAtCurStillDownAndNotRight
				{mat=imat} {prednel=fi} {mel=FZ}
				{f=(<-> (Sigma.getWitness $ fn (FS fi)) <#> senior)}
				imatDANRZ)
			primatzAtWknFi
		missingstep : head imat = (Algebra.unity::Algebra.neutral) <\> deleteRow (FS fi) imat
		missingstep = sym $ trans
			( timesVectMatAsLinearCombo (Algebra.unity::Algebra.neutral) $ deleteRow (FS fi) imat )
			$ trans ( cong {f=\m => monoidsum {t=Vect _} $ zipWith ((<#>) {a=ZZ}) (Algebra.unity::Algebra.neutral) m}
				$ headtails $ deleteRow (FS fi) imat )
			$ trans ( cong {f=monoidsum {a=Vect _ ZZ}}
				$ vecHeadtailsEq (zzVecScalarUnityIsUnity $ head
					$ deleteRow (FS fi) imat) Refl )
			$ trans monoidrec2D
			$ trans ( cong {f=((head $ deleteRow (FS fi) imat)<+>)}
				$ trans (sym
					$ timesVectMatAsLinearCombo Algebra.neutral
					$ tail $ deleteRow (FS fi) imat)
				$ zzVecNeutralIsVecMatMultZero
					(tail $ deleteRow (FS fi) imat) )
			$ trans ( zzVecNeutralIsNeutralL $ head $ deleteRow (FS fi) imat )
			$ deleteSuccRowVanishesUnderHead {k=fi} {xs=imat}
		jmatBispansOrig : jmat `bispanslz` (senior::mat)
		jmatBispansOrig =
			bispanslztrans
				( bispanslzreflFromEq {xs=jmat}
				$ cong {f=\z => updateAt (FS fi) (<-> z) imat}
				$ trans ( cong {f=((<#>) {a=ZZ} _)}
					$ trans seniorIsImatHead $ missingstep )
				$ sym
				$ vectMatLScalingCompatibility
					{z=Sigma.getWitness $ fn $ FS fi}
					{la=Algebra.unity::Algebra.neutral}
					{rs=deleteRow (FS fi) imat} )
			$ bispanslztrans
				( bispanslzSubtractiveExchangeAt (FS fi) {xs=imat}
					{z=(Sigma.getWitness $ fn (FS fi))<#>(Algebra.unity::Algebra.neutral)} )
			$ (imatSpansOrig, origSpansImat)



} {- succImplWknStep lemmas parameters -}



{- (succImplWknStep) parameters -}
parameters (
	mat : Matrix _ (S predm) ZZ
	, predn : Nat
	, senior : Vect (S predm) ZZ
	, srQfunc : ( i : Fin _ )
		-> (indices i FZ (senior::mat)) `quotientOverZZ` (head senior)
	) {

{-
Unexpectedly, (succImplWknStep_unplumbed) has to be given (predm) as an argument,
even though it's from the same (parameters) block in which (predm) was declared.

That might explain part of the earlier troubles with parametrizing
(succImplWknStep_unplumbed), if the parameters required (predm) or other implicit
arguments, but they'd passed out of scope from their declaration coming after the
closing of a nested parameter block that also references them.
-}
succImplWknStep :
	(fi : Fin (S predn))
	-> ( imat : Matrix (S (S predn)) (S predm) ZZ
		** succImplWknProp mat senior (S predn) (FS fi) imat )
	-> ( imat' : Matrix (S (S predn)) (S predm) ZZ
		** succImplWknProp mat senior (S predn) (weaken fi) imat' )
succImplWknStep fi imatAndPrs = succImplWknStep_unplumbed predm mat predn senior srQfunc
		(getWitness imatAndPrs)
		fi
		(getProof imatAndPrs)

} {- (succImplWknStep) parameters -}



{- (foldedFully) parameters -}
parameters (
	predn : Nat
	, mat : Matrix (S predn) (S predm) ZZ
	) {

foldedFully :
	(v : Vect (S predn) ZZ)
	-> ( vmatQfunc :
		( i : Fin _ )
		-> (indices i FZ ((v <\> mat)::mat)) `quotientOverZZ` (head $ v <\> mat) )
	-> ( mats : Vect (S (S predn)) $ Matrix (S (S predn)) (S predm) ZZ
		** (i : Fin (S (S predn)))
		-> succImplWknProp mat (v<\>mat) (S predn) i (index i mats) )
foldedFully v vmatQfunc = foldAutoind2 {predn=S predn} (\ne => Matrix (S ne) (S predm) ZZ)
	(succImplWknProp mat (v <\> mat))
	(succImplWknStep predm mat predn (v <\> mat) vmatQfunc)
	( (v<\>mat)::mat ** (Refl, danrzLast ((v <\> mat)::mat), bispanslzrefl) )

} {- (foldedFully) parameters -}



} {- (elimFirstCol) lemmas parameters -}



{-
Main elimination algorithms
-}



parameters (
	gcdOfVectAlg :
		-- Will making argument "k" implicit work?
		(k : Nat)
		-> (x : Vect k ZZ)
		-> ( v : Vect k ZZ **
			( i : Fin k )
			-> (index i x) `quotientOverZZ` (v <:> x) )
	) {



{-
Structure of (elimFirstCol):

succImplWknStep_Qfunclemma => succImplWknStep_stepQfunc => succImplWknStep_unplumbed => succImplWknStep => foldedFully

(mkQfunc, foldedFully) => elimFirstCol (after some work)

---

Better to refine this to a type that depends on (m=S predm) so that the case (m=Z) may also be covered.

Shall start from the bottom of the matrix (last) and work up to row (FS FZ) using a traversal based on (weaken) and a binary map from index (Fin n) and oldvals to newvals.
-}

elimFirstCol :
	(xs : Matrix n (S predm) ZZ)
	-> (gexs : Matrix (S n) (S predm) ZZ **
		(downAndNotRightOfEntryImpliesZ gexs FZ FZ
		, gexs `bispanslz` xs))
elimFirstCol [] {predm}
	= ( row {n=S predm} $ neutral ** ( nosuch, ([] ** Refl), ([neutral] ** Refl) ) )
	where
		nosuch : (i : Fin _) -> (j : Fin _)
			-> LTRel Z (finToNat i)
			-> LTERel (finToNat j) Z
			-> indices i j (row {n=S predm} Prelude.Algebra.neutral) = Pos 0
		nosuch FZ FZ _ = either (const Refl) (const Refl)
		nosuch (FS k) FZ _ = absurd k
		nosuch _ (FS k) _ = void . ( either succNotLTEzero SIsNotZ )
elimFirstCol mat {n=S predn} {predm} = ?elimFirstCol'

{-

elimFirstCol mat {n=S predn} {predm} with ( gcdOfVectAlg (S predn) (getCol FZ mat) )
	| ( v ** fn ) with ( foldedFully _ _ mat v $ mkQFunc _ _ v mat fn )
		| ( endmat ** endmatPropFn )
			= let bisWithGCD
				= the ((v<\>mat)::mat `bispanslz` mat)
				(extendSpanningLZsByPreconcatTrivially
					{zs=[_]} spanslzrefl
				, mergeSpannedLZs spanslzRowTimesSelf spanslzrefl);
			let ( headvecWasFixed, leftColZBelow, endmatBispansMatandgcd )
				= endmatPropFn FZ
			in ( index FZ endmat
				** (leftColZBelow
				, bispanslztrans endmatBispansMatandgcd bisWithGCD) )

-----

For now, showing it works verbatim:

-----

ZZGaussianEliminationRedo.elimFirstCol' = proof
  intros
  let vAndFn = gcdOfVectAlg (S predn) (getCol FZ mat)
  let v = getWitness vAndFn
  let fn = getProof vAndFn
  let endMatAndPropFn = foldedFully _ _ mat v $ mkQFunc _ _ v mat fn
  let endmat = getWitness endMatAndPropFn
  let endmatPropFn = getProof endMatAndPropFn
  let bisWithGCD = the ((v<\>mat)::mat `bispanslz` mat) (extendSpanningLZsByPreconcatTrivially {zs=[_]} spanslzrefl, mergeSpannedLZs spanslzRowTimesSelf spanslzrefl)
  let headvecWasFixed = fst $ endmatPropFn FZ
  let leftColZBelow = fst . snd $ endmatPropFn FZ
  let endmatBispansMatandgcd = snd . snd $ endmatPropFn FZ
  exact ( index FZ endmat ** (leftColZBelow, bispanslztrans endmatBispansMatandgcd bisWithGCD) )

-}



}
