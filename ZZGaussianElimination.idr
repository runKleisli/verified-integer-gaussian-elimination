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

import Data.Matrix.ZZModuleSpan
import Data.Matrix.LinearCombinations

import RowEchelon
import Control.Algebra.ZZDivisors
import ZZGaussianEliminationLemmas

import Data.Fin.FinOrdering

import Control.Isomorphism

{-
(bezQTy) is the only thing actually used from here in the proof,
something req.d to potentially generalize to other Bezout domains.

However, the example (bezoutZT) is applied here to give a specific algorithm.
-}
import Control.Algebra.ZZBezoutsIdentity

-- Extension of a GCD operation to any number of arguments arguments
import Control.Algebra.ZZGCDOfVectAlg

-- Dependent pattern matching using (do) notation binds improves clarity
import Control.Monad.Identity



{-
Main elimination algorithms.

Index:

* Template & usage for do notation pattern matching technique
* elimFirstCol
* gaussElimlzIfVectGCD2
* gaussElimlzIfVectGCD
* gaussElimlzIfGCD
* The gaussian elimination instantiation derived from (bezoutZT)
* Appendix Elim.General.Meta
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

gaussElimlzIfVectGCD2 :
	(xs : Matrix n (S predm) ZZ)
	-> ( n' : Nat
		** (gexs : Matrix n' (S predm) ZZ
			** (rowEchelonPre gexs, gexs `bispanslz` xs)) )

{-
Suppose case width = 1.

If desired:

gaussElimlzIfVectGCD2 xs {predm=Z} with (elimFirstCol xs)
	| (gexs ** (danrz, bis)) = (_ ** ( gexs ** (echelonPreFromDanrzLast danrz, bis) ))

can't be done, because the typechecker thinks it's a (Vect 1 ZZ = ZZ) situation.

Not fixed if the (danrz, bis) is matched as (danrzAndBis).
Not fixed by passing (S n) into the hole.
-}

gaussElimlzIfVectGCD2 xs {predm=Z} = runIdentity $ do {
		(gexs ** (danrz, bis)) <- Id $ elimFirstCol xs
		return $ (_ ** ( gexs ** (echelonPreFromDanrzLast danrz, bis) ))
	}

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

gaussElimlzIfVectGCD2 xs {predm = S prededm}
	= gaussElimlzIfVectGCD2_gen $ decEq (getCol FZ xs) Algebra.neutral
	where
		gaussElimlzIfVectGCD2_gen :
			Dec (getCol FZ xs = Algebra.neutral)
			-> ( n' : Nat
				** (gexs : Matrix n' (S $ S prededm) ZZ
					** (rowEchelonPre gexs, gexs `bispanslz` xs)) )

		{-
		If first col neutral then we can reduce the process
		to that on the value of (map tail).
		-}

		gaussElimlzIfVectGCD2_gen (Yes prNeut) = runIdentity $ do {
			( nold ** (matold ** (echold, bisold)) )
				<- Id $ gaussElimlzIfVectGCD2 $ map tail xs
			return ( nold **
					(map ((Pos 0)::) matold
					** (echelonPreNullcolExtension echold
					, bispansNullcolExtension prNeut bisold)) )
			}

		{-
		Otherwise it's nonneutral, so we can show that since the elimFirstCol
		is DANRZ FZ FZ, its first row's leading nonzero entry is FZ. This leads
		to promoting the (rowEchelon) of one matrix to one with the same
		first row as the elimFirstCol.

		For a proof, compare with "Appendix Elim.General.Meta"
		-}

		gaussElimlzIfVectGCD2_gen (No prNonneut) = runIdentity $ do {
			-- Perform elimination on the first column.
			(xFCE::xsFCE ** (xnxsFCEdanrz, fceBisxs))
					<- Id $ elimFirstCol xs
			-- Recurse, eliminating the tail.
			(elimLen ** (xselim ** (xselimEch, coltailxsFCEBisElim)))
				<- Id $ gaussElimlzIfVectGCD2 $ map tail xsFCE

			{-
			Add the head of the first-column elimination
			to the tail's elimination to get the final elim.
			-}

			let endmat = xFCE::map ((Pos Z)::) xselim

			-- The final elim is bispannable with the original matrix.
			let xsNullcolextElimBisFCE = bispansNulltailcolExtension
				xnxsFCEdanrz coltailxsFCEBisElim
			-- Bispannability is preserved by consing a common vector
			let endmatBisxnFCE = bispansSamevecExtension
				xsNullcolextElimBisFCE xFCE
			-- This is hence bispannable with the original matrix.
			let endmatBisxs = bispanslztrans endmatBisxnFCE fceBisxs

			{-
			The first column being nonzero is invariant over the
			bispannability class,
			and we assumed (prNonneut) this to hold for (xs),
			thus it holds for (endmat).

			The first column being nonzero and the danrz for (endmat)
			imply (head endmat = xFCE) has (leadingNonzeroNum xFCE = Just 0).
			-}

			let headxFCELeadingNonzero = either
				( void
				. prNonneut
				. spansImpliesSameFirstColNeutrality (fst fceBisxs) )
				id
				$ danrzLeadingZeroAlt xnxsFCEdanrz

			{-
			Thus the hypothesis of (rowEchelonPreExtension) applies,
			and the final elim is row echelon.
			-}

			let endmatEch = rowEchelonPreExtension {x=xFCE}
				headxFCELeadingNonzero xselimEch

			return (_ ** (endmat ** (endmatEch, endmatBisxs)))

			}



{- Gaussian elimination in general -}

gaussElimlzIfVectGCD :
	(xs : Matrix n m ZZ)
	-> ( n' : Nat
		** (gexs : Matrix n' m ZZ
			** (rowEchelonPre gexs, gexs `bispanslz` xs)) )
gaussElimlzIfVectGCD {m=Z} xs = (_ ** (Algebra.neutral
	** (rowEchelonPreZeroWidth, bispanslzreflFromEq $ sym $ zeroVecVecId xs)))
gaussElimlzIfVectGCD {m=S predm} xs = gaussElimlzIfVectGCD2 xs

}



{-
Gaussian elimination from a GCD algorithm.
The premise of (gaussElimlzIfVect)s is equivalent to having a GCD.
-}

{- (gaussElimlzIfGCD) parameters -}
parameters (
	gcdAlg : (c, d : ZZ)
		-> ( zpar : (ZZ, ZZ) ** uncurry (bezQTy c d) zpar )
	) {

gaussElimlzIfGCD2 :
	(xs : Matrix n m ZZ)
	-> ( n' : Nat
		** (gexs : Matrix n' m ZZ
			** (rowEchelonPre gexs, gexs `bispanslz` xs)) )
gaussElimlzIfGCD2 = gaussElimlzIfVectGCD $ gcdToVectGCD gcdAlg

{- Render proper row echelon property -}

gaussElimlzIfGCD :
	(xs : Matrix n m ZZ)
	-> ( n' : Nat
		** (gexs : Matrix n' m ZZ
			** (rowEchelon gexs, gexs `bispanslz` xs)) )
gaussElimlzIfGCD xs = runIdentity $ do {
		(n' ** (gexs ** (echPre, bis))) <- Id $ gaussElimlzIfGCD2 xs
		return $ (n' ** (gexs ** (toRowEchelon echPre, bis)))
	}

} {- (gaussElimlzIfGCD) parameters -}



{-
The gaussian elimination instantiation derived from (bezoutZT)
-}



gaussElimlz :
	(xs : Matrix n m ZZ)
	-> ( n' : Nat
		** (gexs : Matrix n' m ZZ
			** (rowEchelon gexs, gexs `bispanslz` xs)) )
gaussElimlz = gaussElimlzIfGCD bezoutZT



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
