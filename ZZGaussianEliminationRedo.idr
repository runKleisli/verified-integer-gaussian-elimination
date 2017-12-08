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
A type synonym for talking about a GCD algorithm indirectly
-}



-- Making argument "k" implicit will not work.
gcdOfVectAlg : Type
gcdOfVectAlg = (k : Nat) -> (x : Vect k ZZ) -> ( v : Vect k ZZ ** ( i : Fin k ) -> (index i x) `quotientOverZZ` (v <:> x) )

-- Necessary because Idris won't unpack the definition of (gcdOfVectAlg) at occurrences.
runGCDOfVectAlg : ZZGaussianEliminationRedo.gcdOfVectAlg -> (k : Nat) -> (x : Vect k ZZ) -> ( v : Vect k ZZ ** ( i : Fin k ) -> (index i x) `quotientOverZZ` (v <:> x) )
runGCDOfVectAlg gcdalg = gcdalg



--
