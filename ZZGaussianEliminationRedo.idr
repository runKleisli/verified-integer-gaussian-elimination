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
import ZZGaussianEliminationLemmas

import FinOrdering

import Control.Isomorphism

-- Dependent pattern matching using (do) notation binds improves clarity
import Control.Monad.Identity



{-
Table of Contents:

* Main elimination algorithms
-}



{-
Dependent pattern matching using (do) notation binds improves clarity

---

Template & usage for technique:

> f : (a : ZZ ** a = Pos Z)
> f = runIdentity $ do {
> 		clause <- Id $ 'c'
> 		(s ** s_pr) <- Id $ the (r : ZZ ** r = Pos Z) (Pos 0 ** Refl)
> 		(t ** t_pr) <- Id $ (s ** s_pr)
> 		(a, b, c) <- Id $ ('x', ('y', 'z'))
> 		return $ believe_me "Placeholder for while argument incomplete"
> 		-- return (the ZZ _ ** ?foo)
> 	}

Note that two dependent pattern matches have occurred without nesting (with) blocks.

If we figure out the witness of the dependent pair value, we can test things out
interactively, which is sometimes helpful. Note that (clause) won't get recognized
as being ('c'), it's still only a monadic bind.

> g : (a : ZZ ** a = Pos Z)
> g = runIdentity $ do {
> 		clause <- Id $ 'c'
> 		(s ** s_pr) <- Id $ the (r : ZZ ** r = Pos Z) (Pos 0 ** Refl)
> 		-- return $ believe_me "Placeholder for while argument incomplete"
> 		return (the ZZ (Pos 0) ** ?bar)
> 	}

Likewise, we can't recognize (s_pr) is a proof that (Pos 0 = Pos 0), so it doesn't
match the actual goal. However, we can still change the last line to

> 		return (s ** ?bar)

at which point `s_pr` solves the goal.



While (Reader) without (runReader) can simulate a (parameters) block at the same time,
this adds some plumbing overhead, and (ask) may have to be passed its (MonadReader)
instance explicitly:

> z <- ask @{the (MonadReader ZZ _) %instance}

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
elimFirstCol mat {n=S predn} {predm} = runIdentity $ do {

		-- The application of (gcdOfVectAlg) to (mat) column 0.
		(v ** fn) <- Id $ vAndFn

		-- Refines endgoal
		let bisWithGCD = the ( (v<\>mat)::mat `bispanslz` mat )
			(extendSpanningLZsByPreconcatTrivially {zs=[_]} spanslzrefl
			, mergeSpannedLZs spanslzRowTimesSelf spanslzrefl)

		-- ( _ ** forall i. succImplWknProp mat (v<\>mat) _ i endmat_i )
		(endmat ** endmatPropFn)
			<- Id $ foldedFully _ _ mat v $ mkQFunc _ _ v mat fn

		-- (_, danrz endmat_0 0 0, endmat_0 bispans v<\>mat::mat)
		(_, leftColZBelow, endmatBispansMatandgcd) <- Id $ endmatPropFn FZ
		return $ ( index FZ endmat **
			(leftColZBelow
			, endmatBispansMatandgcd `bispanslztrans` bisWithGCD) )
	}
	where
		vAndFn : ( v : Vect (S predn) ZZ **
			( i : Fin (S predn) )
			-> (index i (getCol FZ mat))
				`quotientOverZZ` (v <:> (getCol FZ mat)) )
		vAndFn = gcdOfVectAlg (S predn) (getCol FZ mat)



}
