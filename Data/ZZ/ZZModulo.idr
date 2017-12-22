module Data.ZZ.ZZModulo

import Control.Algebra
import Classes.Verified

import Data.ZZ
import Control.Algebra.NumericInstances

import Data.Fin.FinOrdering
import Data.Fin.Structural

import Control.Algebra.ZZDivisors
import Data.ZZ.ModuloVerification



{-
Table of contents

* Modulo for naturals
* Lemmas for applying (modNatFnIsRemainder)
* Derived modulo for ZZ
-}



{-
Modulo for naturals
-}



||| A manually verifiably total modulo for naturals:
||| It recurses precisely when
||| 	( Not (x `LT` m) ) & ( m, x > 0 ).
||| Not (x `LT` m) -> Either (x = m) (m `LT` x),
||| in former case ((x `minus` m) `modNat` m) is defined,
||| & latter case cannot hold indefinitely since
||| m > 0
||| ==>
||| the iterates of (`minus` m) are decreasing.
%reflection
modNatT : Nat -> Nat -> Nat
modNatT Z _ = Z
modNatT x Z = x
modNatT (S predx) (S predm) with (decLT (S predx) (S predm))
	| No notlt = ((S predx) `minus` (S predm)) `modNatT` (S predm)
	| Yes prlt = S predx



{-
Lemmas for applying (modNatFnIsRemainder)
-}



total
modNatTIdModZero : (x : Nat) -> x `modNatT` Z = x
modNatTIdModZero Z = Refl
modNatTIdModZero (S predx) = Refl

-- The LT implies subtracting m is reversible
total
modNatTCharizLT :
	(x, m : Nat)
	-> (x `LT` m)
	-> x `modNatT` m = x
modNatTCharizLT Z _ _ = Refl
modNatTCharizLT x Z ltpr = void $ succNotLTEzero ltpr
modNatTCharizLT (S predx) (S predm) ltpr with (decLT (S predx) (S predm))
	| No notlt = void $ notlt ltpr
	| Yes prlt = Refl

total
modNatTCharizEq : (m : Nat) -> m `modNatT` m = Z
modNatTCharizEq Z = Refl
modNatTCharizEq (S predm) with (decLT (S predm) (S predm))
	| No notlt = rewrite sym $ minusZeroN predm in Refl
	| Yes prlt = void $ notLTSelf prlt

total
modNatTCharizGTE :
	(x, m : Nat)
	-> (m `plus` x) `modNatT` m = x `modNatT` m
modNatTCharizGTE Z m
	= trans (rewrite plusZeroRightNeutral m in Refl)
	$ modNatTCharizEq m
modNatTCharizGTE x Z = Refl
modNatTCharizGTE (S predx) (S predm) with (decLT (S predm `plus` S predx) (S predm))
	| No notlt = rewrite natPlusInvertibleL (S predx) predm in Refl
	| Yes prlt = void $ notLTSelf $ lteUnsumLeftSummandLeft {y=S predx} prlt

total
modNatTIsRemainder :
	(x, m : Nat)
	-> (d : Nat ** (d `mult` m) `plus` (x `modNatT` m) = x)
modNatTIsRemainder =
	modNatFnIsRemainder
		modNatT
		modNatTIdModZero
		modNatTCharizLT
		modNatTCharizGTE



{-
-- Totally superfluous
modNatTCharizSucc :
	(x, m : Nat)
	-> S x `modNatT` m = (S $ x `modNatT` m) `modNatT` m
modNatTCharizSucc Z _ = ?modNatTCharizSucc_rhs_1
modNatTCharizSucc (S predx) m = ?modNatTCharizSucc_rhs_2
-}



{-
Derived modulo for ZZ
-}



total
modZT : ZZ -> ZZ -> ZZ
modZT = modZGenFn modNatT modNatTIsRemainder

quotientPartModZT :
	(x, m : ZZ)
	-> (x <-> (x `modZT` m)) `quotientOverZZ` m
quotientPartModZT = modZGenQuot modNatT modNatTIsRemainder
