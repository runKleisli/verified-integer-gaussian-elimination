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



{-

All with parameters
	predm

---

With parameters
	predn

mkQFunc : (v : Vect (S predn) ZZ)
	-> (xs : Matrix (S predn) (S predm) ZZ)
	-> ( ( i : Fin (S predn) )
		-> (index i $ getCol FZ xs) `quotientOverZZ` (v <:> (getCol FZ xs)) )
	-> ( ( i : Fin (S $ S predn) )
		-> (indices i FZ $ (v<\>xs)::xs) `quotientOverZZ` (head $ v<\>xs) )

With parameters
	predn
	mat
	senior
	srQfunc
	imat

succImplWknStep_Qfunclemma : ( senior : Vect (S predm) ZZ ) -> ( srQfunc : ( i : Fin _ ) -> (indices i FZ (senior::mat)) `quotientOverZZ` (head senior) )
	-> ( imat : Matrix (S (S predn)) (S predm) ZZ )
	-> ( z : Matrix _ _ ZZ )
	-> ( quotchariz : ( k : Fin _ ) -> ( LinearCombinations.monoidsum $ zipWith (<#>) (index k z) (senior::mat) = index k imat ) )
	-> ( ( j : Fin _ ) -> (indices j FZ imat) `quotientOverZZ` (head senior) )

succImplWknStep_stepQfunc : ( senior : Vect (S predm) ZZ ) -> ( srQfunc : ( i : Fin _ ) -> (indices i FZ (senior::mat)) `quotientOverZZ` (head senior) )
	-> ( imat : Matrix (S (S predn)) (S predm) ZZ )
	-> ( reprolem : senior::mat `spanslz` imat )
	-> ( ( j : Fin _ ) -> (indices j FZ imat) `quotientOverZZ` (head senior) )

-}

{- (elimFirstCol) lemmas parameters -}
parameters (predm : Nat) {

{- succImplWknStep section parameters -}
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



END COMMENT - (succImplWknStep_unplumbed) PARAMETERS ERROR

-}



} {- succImplWknStep section parameters -}

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
-}



}
