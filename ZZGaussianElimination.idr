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



quotientOverZZ : ZZ -> ZZ -> Type
quotientOverZZ x y = ( d : ZZ ** d<.>y=x )

-- Making argument "k" implicit will not work.
gcdOfVectAlg : Type
gcdOfVectAlg = (k : Nat) -> (x : Vect k ZZ) -> ( v : Vect k ZZ ** ( i : Fin k ) -> (index i x) `quotientOverZZ` (v <:> x) )

gaussElimlzIfGCD : Reader gcdOfVectAlg ( (xs : Matrix n m ZZ) -> (gexs : Matrix n' m ZZ ** (gexs `spanslz` xs, xs `spanslz` gexs, rowEchelon gexs)) )



{-
Background info
-}



gcdOfVectZZ : (x : Vect n ZZ) -> ( v : Vect n ZZ ** ( i : Fin n ) -> (index i x) `quotientOverZZ` (v <:> x) )



{-
Main algorithm
-}



gaussElimlz : (xs : Matrix n m ZZ) -> (gexs : Matrix n' m ZZ ** (gexs `spanslz` xs, xs `spanslz` gexs, rowEchelon gexs))
gaussElimlz = runIdentity $ runReaderT gaussElimlzIfGCD (\k => gcdOfVectZZ {n=k})
