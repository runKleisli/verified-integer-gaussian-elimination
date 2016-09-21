module Data.Matrix.Structural

-- For structural lemmas involving matrix operations
import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module
import Classes.Verified -- definition of verified algebras other than modules
import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20
import Data.Matrix.AlgebraicVerified

import Data.Vect.Structural



transposeNHead: with Data.Vect ( head $ transpose xs = map head xs )

tranposeIndexChariz : index k $ transpose xs = getCol k xs

transposeNTail : with Data.Vect ( transpose $ tail $ transpose xs = map tail xs )

transposeIsInvolution : with Data.Vect ( transpose $ transpose xs = xs )



vecMatMultIsTransposeVecMult : Ring a => (v : Vect n a) -> (xs : Matrix n m a) -> v <\> xs = (transpose xs) </> v
vecMatMultIsTransposeVecMult v xs = Refl

matVecMultIsVecTransposeMult : Ring a => (v : Vect m a) -> (xs : Matrix n m a) -> xs </> v = v <\> (transpose xs)
matVecMultIsVecTransposeMult v xs = sym $ trans (vecMatMultIsTransposeVecMult v $ transpose xs) $ cong {f=(</> v)} $ transposeIsInvolution {xs=xs}

headVecMatMultChariz : Ring a => {xs : Matrix _ (S _) a} -> head $ v<\>xs = v <:> (getCol FZ xs)
headVecMatMultChariz {v} {xs} = trans (sym $ indexFZIsheadValued {xs=v<\>xs})
	$ trans (indexMapChariz {k=FZ} {f=(v<:>)} {xs=transpose xs})
	$ cong {f=(v<:>)} $ tranposeIndexChariz {k=FZ} {xs=xs}



{-
Theorems about the module (Matrix n m a) over a ring (a):
* Compatibility between the Algebra.neutral of the ring (a) and of (Matrix n m a) as a module under (index).
-}



indexNeutralIsNeutral2D : Ring a => (k : Fin n) -> index k $ Algebra.neutral {a=Matrix n m a} = Algebra.neutral
indexNeutralIsNeutral2D FZ = Refl
indexNeutralIsNeutral2D (FS k) = indexNeutralIsNeutral2D k
