module Data.Matrix.Structural

-- For structural lemmas involving matrix operations
import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module
import Classes.Verified -- definition of verified algebras other than modules
import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20
import Data.Matrix.AlgebraicVerified

import Data.Vect.Structural



transposeIndexChariz : {xs : Matrix n m a} -> index k $ transpose xs = getCol k xs
transposeIndexChariz {xs=[]} {k} = indexReplicateChariz
transposeIndexChariz {xs=x::xs} {k} = trans zipWithEntryChariz $ vectConsCong _ _ _ transposeIndexChariz

transposeNHead: with Data.Vect ( head $ transpose xs = map head xs )
transposeNHead = trans (sym indexFZIsheadValued) $ trans transposeIndexChariz $ extensionalEqToMapEq (\xs => indexFZIsheadValued {xs=xs}) _

transposeIndicesChariz : {xs : Matrix n m a} -> (i : Fin n) -> (j : Fin m) -> indices j i $ transpose xs = indices i j xs
transposeIndicesChariz i j = trans (cong {f=index i} transposeIndexChariz) indexMapChariz

transposeIsInvolution : with Data.Vect ( transpose $ transpose xs = xs )
transposeIsInvolution {xs} = vecIndexwiseEq (\i => vecIndexwiseEq (\j => trans (transposeIndicesChariz j i) $ transposeIndicesChariz i j))

transposeNTail : with Data.Vect ( transpose $ tail $ transpose xs = map tail xs )
transposeNTail {xs} = vecIndexwiseEq $ \i => vecIndexwiseEq $ \j => trans (transposeIndicesChariz j i)
	$ trans (cong {f=(index i) . (index $ FS j)} $ sym $ headtails $ transpose xs)
	$ trans (transposeIndicesChariz i (FS j))
	$ trans (cong {f=index $ FS j} $ headtails $ index i xs)
	$ sym $ cong {f=index j} indexMapChariz



vecMatMultIsTransposeVecMult : Ring a => (v : Vect n a) -> (xs : Matrix n m a) -> v <\> xs = (transpose xs) </> v
vecMatMultIsTransposeVecMult v xs = Refl

matVecMultIsVecTransposeMult : Ring a => (v : Vect m a) -> (xs : Matrix n m a) -> xs </> v = v <\> (transpose xs)
matVecMultIsVecTransposeMult v xs = sym $ trans (vecMatMultIsTransposeVecMult v $ transpose xs) $ cong {f=(</> v)} $ transposeIsInvolution {xs=xs}

headVecMatMultChariz : Ring a => {xs : Matrix _ (S _) a} -> head $ v<\>xs = v <:> (getCol FZ xs)
headVecMatMultChariz {v} {xs} = trans (sym $ indexFZIsheadValued {xs=v<\>xs})
	$ trans (indexMapChariz {k=FZ} {f=(v<:>)} {xs=transpose xs})
	$ cong {f=(v<:>)} $ transposeIndexChariz {k=FZ} {xs=xs}
