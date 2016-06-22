import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module

import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20

import Data.ZZ
import Control.Algebra.NumericInstances

import ZZModuleSpan

import FinOrdering



rowReduced : (xs : Matrix n m ZZ) -> Type
{-
Something built from the same parts as this:
-----
rowReduced xs {n} {m} = {k : Fin n} -> {i, j : Fin m} -> (i `LT` j) -> (indices k i xs = Pos Z) -> (indices k j xs = Pos Z)
-}

gaussElimlz : (xs : Matrix n m ZZ) -> (gexs : Matrix n' m ZZ ** (gexs `spanslz` xs,rowReduced gexs))
