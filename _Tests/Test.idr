module Main

import Data.ZZ
import Data.Matrix
import Data.Matrix.RowEchelon
import Data.Matrix.ZZModuleSpan

import Data.Matrix.ZZGaussianElimination

%flag C "-O3"



-- 1s & 0s only, please.
testmat : Matrix 3 2 ZZ
testmat = map (map Pos) [[0,1],[1,1],[1,0]]

-- 1s & 0s only, please.
testmat2 : Matrix 2 2 ZZ
testmat2 = map (map Pos) [[1,0],[0,1]]

-- 1s & 0s only, please.
testmat3 : Matrix 1 2 ZZ
testmat3 = [[Pos 1, Pos 0]]

-- 1s & 0s only, please.
testmat4 : Matrix 1 2 ZZ
testmat4 = [[Pos 0, Pos 1]]

testmat5 : Matrix 2 1 ZZ
testmat5 = [[Pos 2],[Pos 3]]



testelim : (n' : Nat ** (gexs : Matrix n' 2 ZZ
		** (rowEchelon gexs, bispanslz gexs Main.testmat)))
testelim = gaussElimlz testmat

{-
testelim2 : (n' : Nat ** (gexs : Matrix n' 2 ZZ
		** (rowEchelon gexs, bispanslz gexs Main.testmat2)))
testelim2 = gaussElimlz testmat2

testelim2' : Matrix (getWitness Main.testelim2) 2 ZZ
testelim2' = getWitness $ getProof $ gaussElimlz testmat2
-}



testelim2_ : (n' : Nat ** Matrix n' 2 ZZ)
testelim2_ = (_ ** getWitness $ getProof $ gaussElimlz testmat2)

testelim4_ : (n' : Nat ** Matrix n' 2 ZZ)
testelim4_ = (_ ** getWitness $ getProof $ gaussElimlz testmat4)

testelim5_ : (n' : Nat ** Matrix n' 1 ZZ)
testelim5_ = (_ ** getWitness $ getProof $ gaussElimlz testmat5)



main : IO ()
main = putStrLn $ show $ getProof testelim4_
