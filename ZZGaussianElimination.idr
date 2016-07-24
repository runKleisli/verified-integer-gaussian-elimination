module ZZGaussianElimination

import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module

import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20

import Data.ZZ
import Control.Algebra.NumericInstances
import Control.Algebra.ZZVerifiedInstances

import ZZModuleSpan

import FinOrdering

-- For style. ((Reader r a) equivalent to (r -> a))
import Control.Monad.Identity
import Control.Monad.Reader



{-
Properties of vectors and matrices.
-}



downAndNotRightOfEntryImpliesZ : (xs : Matrix n m ZZ) -> (row : Fin n) -> (col : Fin m) -> Type
downAndNotRightOfEntryImpliesZ xs nel mel {n} {m} = {i : Fin n} -> {j : Fin m} -> (finToNat nel `LTRel` finToNat i) -> (finToNat j `LTERel` finToNat mel) -> indices i j xs = Pos Z
{-
Equivalent properties:
1) map (take mel) (drop nel xs) = neutral
2) (nel `LT` i) -> (j `LTE` mel) -> indices i j xs = Pos Z
	# In pseudocode, because we decided not to use direct LT and LTE of Fins.
-}

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

{-
elimFirstCol : (xs : Matrix n m ZZ) -> Reader ZZGaussianElimination.gcdOfVectAlg (gexs : Matrix (S n) m ZZ ** (gexs `spanslz` xs, xs `spanslz` gexs, firstColZero $ tail gexs))
{-
-- Template
elimFirstCol xs = do {
		gcdalg <- ask @{the (MonadReader gcdOfVectAlg _) %instance}
		return $ believe_me "shshs"
		-- return (?foo ** (?bar1,?bar2,?bar3))
	}
-}
-- A 0-row matrix becomes the one-neutral-row matrix
elimFirstCol [] {m} = return (row {n=m} neutral ** ( ([] ** Refl), ([neutral] ** Refl), the (firstColZero [] {m=m}) () ))
elimFirstCol ([]::xs) = ?elimFirstCol_widthZero
elimFirstCol mat {n=S predn} {m=S predm} = do {
-- elimFirstCol mat@((xx::xxs)::xs) {n=S predn} {m=S predm} = do {
		gcdalg <- ask @{the (MonadReader ZZGaussianElimination.gcdOfVectAlg _) %instance}

		{-
		Error:

		> elimFirstCol (x::xs) {m} = do {
		> 	gcdalg <- ask @{the (MonadReader gcdOfVectAlg _) %instance}
		> 	let (v ** fn) = gcdalg _ x
		>	-- which is a ( v : Vect _ ZZ ** ( i : Fin k ) -> (index i x) `quotientOverZZ` (v <:> x) )

			gcdalg does not have a function type (gcdOfVectAlg)
		-}

		-- (v ** fn) : ( v : Vect _ ZZ ** ( i : Fin _ ) -> (index i matcolZ) `quotientOverZZ` (v <:> matcolZ) )
		let (v ** fn) = runGCDOfVectAlg gcdalg _ (getCol FZ mat)

		{-
		* We want the first entry of (gexs) to be (v <:> (getCol FZ mat)), and to acquire the full vector as a linear combination of (mat) rows.
		* index FZ (r<\>m) = r<:>(index FZ $ transpose m) = r<:>(getCol FZ m)
		* to that end, we begin construction by appending (v<\>mat) to (mat).
		-}

		let bisWithGCD = the ((v<\>mat)::mat `spanslz` mat, mat `spanslz` (v<\>mat)::mat)
			(extendSpanningLZsByPreconcatTrivially {zs=[_]} spanslzrefl, mergeSpannedLZs spanslzRowTimesSelf spanslzrefl)

		{-
		* Use the properties of fn to construct mat', with bar1 and bar2 following by construction and divisibility
		-}

		{-
		This has to be commented out if you reduce mat@((xx::xxs)::xs) to mat.
		They say it's a type mismatch.

		> let mat' = mat <-> (map (\i => (v <:> (getCol FZ mat))<.>(Sigma.getWitness $ fn i) <#> (index i mat)) range)
		-}

		{-
		Typechecks, but we'll try the above for now

		> let mat' = Data.Vect.zipWith (\i => \xi => updateAt i (<-> (v <:> (getCol FZ mat))<.>(Sigma.getWitness $ fn i) <#> xi) mat) range mat
		-}

		{-
		We could just foldl with (mat ** spanslzrefl) the seed to the accumulator and accumulate by transforming the matrix to a new one and deriving a proof of its (mat) bispannability from the old proof composed with a proof the transformation preserves bispannability. Refining this fold, an accumulation of the evidence required to show that the first column becomes null below the top/gcd row of the matrix (which is invariant under the transformations).
		-}

		{-
		(foldl Iteration 1)

		This has poor qualities for applying transformations with known proofs of bispannability and composing those proofs, and it arbitrarily indirects the construction of (gexs) by accumulation through the accumulation of the tail of the (gexs) to be.

		> let foldSomefuncPreservingBispan = \f => foldl {t=Vect (S predn)} {elt=Fin (S predn)} {acc=( imat : Matrix (S predn) (S predm) ZZ ** ( (v <\> mat)::imat `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` (v <\> mat)::imat, (i : Fin (S predn) ** {j : Fin (S predn)} -> finToNat j `LTERel` finToNat i -> indices j FZ imat = Pos Z) ) )} f
		-}

		{-
		(foldl Iteration 2)

		A rough specification at least
		This has base case a once-updated version of mat,
		among other undesirable qualities.

		> let foldSomefuncPreservingBispan2 = \f => foldl {t=Vect (S predn)} {elt=Fin (S predn)} {acc=( imat : Matrix (S (S predn)) (S predm) ZZ ** ( imat `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` imat, (i : Fin (S predn) ** {j : Fin (S predn)} -> finToNat j `LTERel` finToNat i -> indices j FZ (tail imat) = Pos Z) ) )} f
		> 	( updateAt (FS FZ) (<->(?makesXXTheHeadMatHeadless<\>(deleteRow (FS FZ) (v<\>mat)::mat))) (v<\>mat)::mat ** (spanslzSubtractiveExchangeAt FS FZ,?howel,(FZ ** ?initTheFirstRowOfTailIsZero)) ) (map FS range)
		-}

		{-
		(foldl Iteration 3)
		-}

		let foldSomefuncPreservingBispan3 = \f => foldl {t=Vect (S predn)} {elt=Fin (S predn)} {acc=( imat : Matrix (S (S predn)) (S predm) ZZ ** ( imat `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` imat, (i : Fin (S (S predn)) ** (j : Fin (S predn)) -> finToNat (FS j) `LTERel` finToNat i -> indices (FS j) FZ imat = Pos Z) ) )} f
			( (v<\>mat)::mat ** (spanslzrefl,spanslzrefl,(FZ ** ?proveItAbs)) ) range
		-- proveItAbs is like \j => void . ( spawnNotLTE (finToNat (FS j)) (finToNat FZ)) )
		-- spawnNotLTE is an explicit (LTERel _ _ -> Void) to be proved, avoiding any (decLTE) (Yes/No)-case handling problems.
		-- f should take its argument (elt:=Fin (S predn)) to its successor so it can be used to index (imat), starting in its tail, and so that it will always be non-FZ and thus never using the same (Fin (S (S predn))) as the base case has.

		{-
		Can't deduce that the final bound on the known rows zero in the first column starting from the top row of (tail endmat) is actually the final row.

			"Can't match on case block in case block in elimFirstCol at [...]"

		This and the redundant information in the (range) argument suggests an even cleaner structure and closer intermediary to the goal.

		> let ( endmat ** ( endmatSpansMatandgcd, matandgcdSpansEndmat, (last {n=S predn} ** downImpliesZ) ) ) = foldSomefuncPreservingBispan3 fancy
		-}

		let ( endmat ** ( endmatSpansMatandgcd, matandgcdSpansEndmat, (finalind ** notUpImpliesZ) ) ) = foldSomefuncPreservingBispan3 fancy

		{-
		We need to show that for every row (i) of (mat), there is a vector (u) such that (u_(FS i)<\>(droprow (FS i) (v<\>mat)::mat) has the same value as row (i) of (mat) at column FZ). Especially that this property is preserved in each (imat).
		-}

		-- See comment to def of mat' for why this is commented
		-- let fstcolz_mat' = the (firstColZero mat') ?lemma_fstcolz_mat'

		-- let downImpliesZ' = ?determineFirstColZ downImpliesZ

		-- return ( (v <\> mat)::mat' ** (?bar1,?bar2,fstcolz_mat'))
		return ( endmat ** (spanslztrans endmatSpansMatandgcd $ fst bisWithGCD, spanslztrans (snd bisWithGCD) matandgcdSpansEndmat, ?downImpliesZ'))
	}
	where
		extendedFunc : {imat : Matrix (S (S predn)) (S predm) ZZ}
			-> (sfi : Fin (S (S predn)))
			-> ( (j : Fin (S predn)) -> finToNat (FS j) `LTERel` finToNat i -> indices (FS j) FZ imat = Pos Z )
			-> (j : Fin (S predn))
			-> finToNat (FS j) `LTERel` finToNat sfi
			-> indices (FS j) FZ imat = Pos Z
		fancy : {v : Vect (S predn) ZZ} -> ( imat : Matrix (S (S predn)) (S predm) ZZ ** ( imat `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` imat, (i : Fin (S (S predn)) ** (j : Fin (S predn)) -> finToNat (FS j) `LTERel` finToNat i -> indices (FS j) FZ imat = Pos Z) ) )
			-> (fi : Fin (S predn))
			-> ( imat' : Matrix (S (S predn)) (S predm) ZZ ** ( imat' `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` imat', (i' : Fin (S (S predn)) ** (j : Fin (S predn)) -> finToNat (FS j) `LTERel` finToNat i' -> indices (FS j) FZ imat' = Pos Z) ) )
		fancy ( imat ** (imatSpansMatandgcd, matandgcdSpansImat, (i ** downImpl)) ) fi = ( updateAt
				(FS fi)
				(<->(?makesXXTheHeadMatHeadless<\>(deleteRow (FS fi) imat)))
				imat
			** (spanslztrans (spanslzSubtractiveExchangeAt $ FS fi) imatSpansMatandgcd,
				spanslztrans matandgcdSpansImat (spanslzSubtractivePreservationAt $ FS fi),
				(FS fi ** extendedFunc (FS fi) downImpl)
			) )
-}

{-
Better to refine this to a type that depends on (m=S predm) so that the case (m=Z) may also be covered.

Shall start from the bottom of the matrix (last) and work up to row (FS FZ) using a traversal based on (weaken) and a binary map from index (Fin n) and oldvals to newvals.
-}
elimFirstCol2 : (xs : Matrix n (S predm) ZZ) -> Reader ZZGaussianElimination.gcdOfVectAlg (gexs : Matrix (S n) (S predm) ZZ ** (gexs `spanslz` xs, xs `spanslz` gexs, downAndNotRightOfEntryImpliesZ gexs FZ FZ))

{-
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
