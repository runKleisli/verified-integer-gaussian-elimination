module ZZGaussianEliminationNoMonad

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

import Data.Matrix.ZZModuleSpan
import Data.Matrix.LinearCombinations

import Data.Matrix.RowEchelon
import Control.Algebra.ZZDivisors
import ZZGaussianEliminationLemmas

import Data.Fin.FinOrdering

import Control.Isomorphism



{-
Table of Contents:

* Main elimination algorithms
-}



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
elimFirstCol mat {n=S predn} {predm} =
	( index FZ endmat
		** (leftColZBelow, bispanslztrans endmatBispansMatandgcd bisWithGCD) )
	where
		{-
		Should just be nested (with) blocks over (vAndFn) & (endMatAndPropFn),
		but the typechecker is struggling.
		-}
		vAndFn : ( v : Vect (S predn) ZZ **
			( i : Fin (S predn) )
			-> (index i (getCol FZ mat))
				`quotientOverZZ` (v <:> (getCol FZ mat)) )
		vAndFn = gcdOfVectAlg (S predn) (getCol FZ mat)
		v : Vect (S predn) ZZ
		v = getWitness vAndFn
		fn : ( i : Fin (S predn) )
			-> (index i (getCol FZ mat))
				`quotientOverZZ` (v <:> (getCol FZ mat))
		fn = getProof vAndFn
		endMatAndPropFn : ( mats : Vect (S (S predn))
			$ Matrix (S (S predn)) (S predm) ZZ
			** (i : Fin (S (S predn)))
			-> succImplWknProp mat (v<\>mat) (S predn) i (index i mats) )
		endMatAndPropFn = foldedFully _ _ mat v $ mkQFunc _ _ v mat fn
		endmat : Vect (S (S predn)) $ Matrix (S (S predn)) (S predm) ZZ
		endmat = getWitness endMatAndPropFn
		endmatPropFn : (i : Fin (S (S predn)))
			-> succImplWknProp mat (v<\>mat) (S predn) i (index i endmat)
		endmatPropFn = getProof endMatAndPropFn
		bisWithGCD : (v<\>mat)::mat `bispanslz` mat
		bisWithGCD =
			(extendSpanningLZsByPreconcatTrivially {zs=[_]} spanslzrefl
			, mergeSpannedLZs spanslzRowTimesSelf spanslzrefl)
		{- In tuple match: headvecWasFixed = fst $ endmatPropFn FZ -}
		leftColZBelow : downAndNotRightOfEntryImpliesZ (index FZ endmat) FZ FZ
		leftColZBelow = fst . snd $ endmatPropFn FZ
		endmatBispansMatandgcd : (index FZ endmat) `bispanslz` ((v<\>mat)::mat)
		endmatBispansMatandgcd = snd . snd $ endmatPropFn FZ



}
