module ZZGCDOfVectAlg

import Control.Algebra
import Classes.Verified
import Control.Algebra.VectorSpace

import Data.ZZ
import Control.Algebra.NumericInstances
import Control.Algebra.ZZVerifiedInstances

import Data.Matrix
import Data.Matrix.Algebraic
import Data.Matrix.AlgebraicVerified
import Data.Matrix.LinearCombinations -- for (vectVectLScalingCompatibility)

import Data.Vect.Structural

import ZZDivisors

import FinOrdering
import FinStructural

import ZZBezoutsIdentity

-- Dependent pattern matching using (do) notation binds improves clarity
import Control.Monad.Identity
import Syntax.PreorderReasoning

import Control.Algebra.DiamondInstances



{-
Table of contents:
* Some algebra about Vect groups
* Lemmas about extending a GCD to more than 2 numbers
* The extension of a GCD of 2 numbers to that of a Vect of numbers
-}



{-
Some algebra about groups
-}



groupSubtractionIsRDivision_Vect : VerifiedGroup t
	=> {auto ok :
		((<+>) @{vgrpSemigroupByGrp $ the (VerifiedGroup t) %instance})
		= ((<+>) @{vgrpSemigroupByVMon $ the (VerifiedGroup t) %instance})
		}
	-> (a, b : Vect n t)
	-> (a <-> b) <+> b = a
groupSubtractionIsRDivision_Vect [] [] = Refl
groupSubtractionIsRDivision_Vect (a::as) (b::bs)
	= vecHeadtailsEq (groupSubtractionIsRDivision a b)
	$ groupSubtractionIsRDivision_Vect as bs



{-
Lemmas about extending a GCD to more than 2 numbers
-}



lemma1Fn : ( t : Fin n -> ZZ )
	-> ( r, r' : ZZ )
	-> Fin (S n) -> ZZ
lemma1Fn _ _ r' FZ = r'
lemma1Fn t r _ (FS prel) = t prel <.> r

lemma1 : ( t : Fin n -> ZZ )
	-> ( factorizationAtInd : ( j : Fin n )
		-> t j <.> ( vs <:> xs ) = index j xs )
	-> ( factorizationX : r' <.> s = x )
	-> ( factorizationWithin : r <.> s = vs <:> xs )
	-> ( i : Fin (S n) )
	-> lemma1Fn t r r' i <.> s = index i (x :: xs)
lemma1 t factorizationAtInd factorizationX factorizationWithin FZ = factorizationX
lemma1 t factorizationAtInd factorizationX factorizationWithin (FS prel)
	= trans (sym $ ringOpIsAssociative _ _ _)
	$ trans (cong factorizationWithin)
	$ factorizationAtInd prel

lemma1_2 : ( factorizationAtInd : ( j : Fin n )
		-> index j xs `quotientOverZZ` ( vs <:> xs ) )
	-> ( factorizationX : x `quotientOverZZ` s )
	-> ( factorizationWithin : (vs <:> xs) `quotientOverZZ` s )
	-> ( i : Fin (S n) )
	-> index i (x :: xs) `quotientOverZZ` s
lemma1_2 factorizationAtInd (factnXDiv ** factnXPr) (factnWinDiv ** factnWinPr) i
	= let lemma1Fn' = \j => getWitness $ factorizationAtInd j
	in let lemma1Pr = \j => getProof $ factorizationAtInd j
	in ( lemma1Fn lemma1Fn' factnWinDiv factnXDiv i
		** lemma1 lemma1Fn' lemma1Pr factnXPr factnWinPr i )

lemma2 : {a : ZZ}
	-> a<.>x <+> b<.>(vs <:> xs) = (a :: (b <#> vs)) <:> (x :: xs)
lemma2 {a} {b} {x} {xs} {vs} = (
	a<.>x <+> b<.>(vs <:> xs)
	) ={ cong $ sym vectVectLScalingCompatibility }= (
	a<.>x <+> ( (b <#> vs)<:>xs )
	) ={ sym monoidrec1D }= (
	(a :: (b <#> vs)) <:> (x :: xs)
	) QED



{-
The extension of a GCD of 2 numbers to that of a Vect of numbers
-}



{- (gcdToVectGCD) parameters -}
parameters (
	gcdAlg : (c, d : ZZ)
		-> ( zpar : (ZZ, ZZ) ** uncurry (bezQTy c d) zpar )
	) {

gcdToVectGCD :
	(k : Nat)
	-> (x : Vect k ZZ)
	-> ( v : Vect k ZZ **
		( i : Fin k )
		-> (index i x) `quotientOverZZ` (v <:> x) )
gcdToVectGCD Z [] = ( [] ** \i => FinZElim i )
gcdToVectGCD (S predk) (x::xs) with (gcdToVectGCD predk xs)
	| (vs ** recQFn) = runIdentity $ do {
			( (a, b) ** (gcdivA, gcdivB) )
				<- Id $ gcdAlg x (vs <:> xs)
			let Lem1_2_Ap = lemma1_2
				{s=a<.>x <+> b<.>(vs <:> xs)}
				{xs=xs}
				{vs=vs}
				{x=x}
				recQFn gcdivA gcdivB
			return $ ( a::(b<#>vs) **
				\i => let apAtI = Lem1_2_Ap i
				in (getWitness apAtI
					** trans (cong $ sym lemma2) $ getProof apAtI)
				)
		}

} {- (gcdToVectGCD) parameters -}
