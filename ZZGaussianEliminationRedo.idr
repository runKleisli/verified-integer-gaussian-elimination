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
	senior |-> srQfunc |-> that divisibility
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
