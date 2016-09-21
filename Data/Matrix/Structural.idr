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

transposeIndexChariz : index k $ transpose xs = getCol k xs

transposeNTail : with Data.Vect ( transpose $ tail $ transpose xs = map tail xs )

transposeIsInvolution : with Data.Vect ( transpose $ transpose xs = xs )



vecMatMultIsTransposeVecMult : Ring a => (v : Vect n a) -> (xs : Matrix n m a) -> v <\> xs = (transpose xs) </> v
vecMatMultIsTransposeVecMult v xs = Refl

matVecMultIsVecTransposeMult : Ring a => (v : Vect m a) -> (xs : Matrix n m a) -> xs </> v = v <\> (transpose xs)
matVecMultIsVecTransposeMult v xs = sym $ trans (vecMatMultIsTransposeVecMult v $ transpose xs) $ cong {f=(</> v)} $ transposeIsInvolution {xs=xs}

headVecMatMultChariz : Ring a => {xs : Matrix _ (S _) a} -> head $ v<\>xs = v <:> (getCol FZ xs)
headVecMatMultChariz {v} {xs} = trans (sym $ indexFZIsheadValued {xs=v<\>xs})
	$ trans (indexMapChariz {k=FZ} {f=(v<:>)} {xs=transpose xs})
	$ cong {f=(v<:>)} $ transposeIndexChariz {k=FZ} {xs=xs}
