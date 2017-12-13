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



{- Gaussian elimination for width > 0 -}
{- Suppose case width = 1. -}

{-
Proof by

echelonPreFromDanrzLast :
	downAndNotRightOfEntryImpliesZ mat FZ last
	-> rowEchelonPre mat
-}

{-
Else case width > 1.

We handle recursion in different ways depending on whether the first column is neutral.
Since (with) blocks can't access local functions unless local to the case, and (case)
blocks have totality problems, we write it as a wrapping of a local function which
pattern matches on the equality decision.

The locally scoped functions in question were involved in partially completing the
proof, and this is retained as an artifact to retain compatibility this implementation
tool used.
-}

		{-
		If first col neutral then we can reduce the process
		to that on the value of (map tail).
		-}

		{-
		Proof by

		echelonPreNullcolExtension :
			rowEchelon xs
			-> rowEchelonPre (map ((Pos 0) ::) xs)
		-}

		{-
		Otherwise it's nonneutral, so we can show that since the elimFirstCol
		is DANRZ FZ FZ, its first row's leading nonzero entry is FZ. This leads
		to promoting the (rowEchelon) of one matrix to one with the same
		first row as the elimFirstCol.

		For a proof, compare with "Appendix Elim.General.Meta"
		-}

		{-
		Proof by

		danrzLeadingZeroAlt :
			downAndNotRightOfEntryImpliesZ (x::xs) FZ FZ
			-> Either
				(getCol FZ (x::xs) = Algebra.neutral)
				(leadingNonzeroNum x = Just FZ)
		-}



{- Gaussian elimination in general -}

{- Render proper row echelon property -}



}



{-

Appendix Elim.General.Meta

Case matrix has height > 0, width > 1 of gaussian elimination.

The following meta-analytic proof translates between the mathematical ideas and the realization in the formal logic.

---

Suppose we are to produce from a given (x::xs) of width > 1 a row-span-equivalent
row echelon matrix, given how to do this for all matrices of lesser height
and (nonzero) width, and given that the first column of (x::xs) is nonzero.

By (rowEchelonPreExtension), (leadingNonzeroNum v = Just FZ) & (rowEchelonPre vs)
--> row echelon v :: 0|vs

Eliminating the first column

	matchbind

converts a y::ys of width > 0 to an equivalent y' :: 0|ys' =: (yy'::yys') :: 0|ys'.

Being of this form is an unspoken equivalence to "danrz" (abbrev.): tautologically,
(downAndNotRightOfEntryImpliesZ (y'::0|ys') 0 0). Whence the type of & intention
behind (elimFirstCol).

	"y::ys === m where (m = y'::0|ys')"
	<==>
	y::ys `bispanslz` m & downAndNotRightOfEntryImpliesZ m 0 0

Since x::xs didn't have a 0 column, & bispannability preserves this (spansImpliesSameFirstColNeutrality), bispannability implies that xx' /= 0:

	"xx' /= 0"
	<==>
	lnzn x' = Just 0,

& the latter is proved through (danrzLeadingZeroAlt):

	danrz (_1::_2) 0 0, getCol 0 (_1::_2) /= 0
	==>	(danrzLeadingZeroAlt)
	(getCol 0 (_1::_2) = 0 | lnzn _1 = Just 0) & getCol 0 (_1::_2) /= 0
	==>
	lnzn _1 = Just 0

Eliminating ys' then gives a matrix equivalent to ys under bispannability

	matchbind

which is preserved (bispansSamevecExtension) by consing a common vector. Thus we can
convert each y::ys of width > 1 to an equivalent y' :: 0|zs =: (yy'::yys') :: 0|zs such
that yy' /= 0 and 0|zs is row echelon.

Sharing the head y' means preserving the leading nonzero of the head, shown to
be (Just 0).

Thus the hypothesis of (rowEchelonPreExtension) applies

	y'_0 /= 0 ==> leadingNonzeroNum y' = Just FZ

& we have that the y'::0|zs equivalent to the original y::ys is row echelon.

Such a matrix with the property of being equivalent to the original but row echelon is
wwtbd.

-}
