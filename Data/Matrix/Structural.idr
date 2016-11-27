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



matMultIndicesChariz : Ring a => {l : Matrix _ _ a} -> {r : Matrix _ _ a} -> indices i j (l<>r) = (index i l)<:>(getCol j r)
matMultIndicesChariz {l} {r} {i} {j} = trans (cong {f=index j} $ indexMapChariz {f=(<\>r)}) $ trans (indexMapChariz {f=((index i l)<:>)}) $ cong {f=((Vect.index i l)<:>)} transposeIndexChariz



-- But basically from (map) being a verifiable functor.
leadingElemExtensionFirstColReplicate : (r : a) -> getCol FZ $ map (r::) xs = replicate _ r
leadingElemExtensionFirstColReplicate {xs=[]} r = Refl
leadingElemExtensionFirstColReplicate {xs=x::xs} r = vecHeadtailsEq Refl $ leadingElemExtensionFirstColReplicate r

-- But basically from (map) being a verifiable functor.
leadingElemExtensionColFSId : getCol (FS i) $ map (r::) xs = getCol i xs
leadingElemExtensionColFSId {xs} {r} {i} = trans (composeUnderMap xs (index $ FS i) (r::)) $ the (map ((index $ FS i) . (r::)) xs = map (index i) xs) $ extensionalEqToMapEq (\v => Refl) xs

leadingElemExtensionAsZipWithCons : map (r::) xs = Vect.zipWith Vect.(::) (replicate _ r) xs
leadingElemExtensionAsZipWithCons {xs=[]} = Refl
leadingElemExtensionAsZipWithCons {xs=x::xs} = vecHeadtailsEq Refl leadingElemExtensionAsZipWithCons

nullcolExtensionEq : Monoid a => {xs : Matrix n (S predm) a} -> (getCol FZ xs=Algebra.neutral) -> map ((Algebra.neutral)::) $ map Vect.tail xs = xs
nullcolExtensionEq {xs} prColNeut = trans leadingElemExtensionAsZipWithCons
	-- = zipWith (::) Algebra.neutral $ map tail xs
	$ trans (cong {f=zipWith (::) Algebra.neutral} $ sym $ transposeNTail)
	-- = zipWith (::) Algebra.neutral $ transpose $ tail $ transpose xs
	-- === transpose $ Algebra.neutral :: (tail $ transpose xs)
	$ trans (cong {f=transpose}
		$ trans (vecHeadtailsEq
			(trans (sym prColNeut)
				-- Algebra.neutral = getCol FZ xs
				$ trans (sym transposeIndexChariz)
				-- = index FZ $ transpose xs
				$ indexFZIsheadValued)
			Refl)
		-- Algebra.neutral :: (tail $ transpose xs) = head _ :: tail _
		$ sym $ headtails $ transpose xs)
	-- = transpose $ transpose xs
	transposeIsInvolution
	-- = xs
