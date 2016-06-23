module ZZGaussianElimination

import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module

import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20

import Data.ZZ
import Control.Algebra.NumericInstances

import ZZModuleSpan

import FinOrdering



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
		(nel : Fin n **
			( {i : Fin n}
			-> finToNat i `LTRel` finToNat nel
			-> index i v = Pos Z,
			Not (index nel v = Pos Z) )
		)
		(v = neutral)

leadingNonzeroCalc : (v : Vect n ZZ) -> leadingNonzero v
leadingNonzeroCalc [] = Right Refl
-- leadingNonzeroCalc (Z::xs) = 
-- leadingNonzeroCalc (a::xs) =

{-
There is a tricky part to matching on Right.

We might have this

> | Right _ = downAndNotRightOfEntryImpliesZ xs nel (last {n=predm})

but that only works if we guarantee `m` has a predecessor `predm`. Else we should use

> | Right _ = ()

So, we just simplify things and write

> | Right _ = {nelow : Fin n} -> (finToNat nel `LTRel` finToNat nelow) -> index nel xs = neutral
-}
rowEchelon : (xs : Matrix n m ZZ) -> Type
rowEchelon {n} {m} xs = (narg : Fin n) -> (ty narg)
	where
		ty : Fin n -> Type
		ty nel with (leadingNonzeroCalc $ index nel xs)
			| Left someNonZness with someNonZness
				| (leadeln ** _) = downAndNotRightOfEntryImpliesZ xs nel leadeln
			| Right _ = {nelow : Fin n} -> (finToNat nel `LTRel` finToNat nelow) -> index nel xs = neutral

gaussElimlz : (xs : Matrix n m ZZ) -> (gexs : Matrix n' m ZZ ** (gexs `spanslz` xs,rowEchelon gexs))
