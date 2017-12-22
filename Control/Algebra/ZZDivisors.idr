module Control.Algebra.ZZDivisors

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

import Data.Matrix.ZZModuleSpan
import Data.Matrix.LinearCombinations



{-
Trivial lemmas and plumbing
-}



bileibniz : (f : a -> b -> c) -> (x1=x2) -> (y1=y2) -> f x1 y1 = f x2 y2
bileibniz f {x1} {x2} {y1} {y2} xeq yeq = rewrite (cong {f=f} xeq) in cong {f=f x2} yeq



{-
A divisibility relation
-}



-- Should be modified to account for (gcd x 0 = 0).
quotientOverZZ : ZZ -> ZZ -> Type
quotientOverZZ x y = ( d : ZZ ** d<.>y=x )

quotientOverZZrefl : x `quotientOverZZ` x
quotientOverZZrefl {x} = ( unity ** ringWithUnityIsUnityR x )

quotientOverZZtrans : x `quotientOverZZ` y -> y `quotientOverZZ` z -> x `quotientOverZZ` z
quotientOverZZtrans (dx ** prx) (dy ** pry) {x} {y} {z} = ( dx<.>dy ** trans (sym $ ringOpIsAssociative dx dy z) $ trans (cong pry) prx )

quotientOverZZreflFromEq : (a=b) -> a `quotientOverZZ` b
quotientOverZZreflFromEq {a} {b} eq with (quotientOverZZrefl {x=b})
	| (d ** pr) = (d ** trans pr $ sym eq)



{-
Interactions between integer divisibility and linear combinations
-}



||| Examples:
||| 
||| > divisorByDistrib (Pos 4) ((Pos 8)::(Pos 0)::[]) (\x => case x of { FZ => (Pos 2 ** Refl); (FS FZ) => (Pos 0 ** Refl) })
||| 
||| (Pos 2 ** ?divisorByDistrib_pr) : (d : ZZ ** multZ d (Pos 4) = Pos 8)
||| 
||| > divisorByDistrib (Pos 4) ((Pos 8)::(Pos 4)::[]) (\x => case x of { FZ => (Pos 2 ** Refl); (FS FZ) => (Pos 1 ** Refl) })
||| 
||| (Pos 3 ** ?divisorByDistrib_pr) : (d : ZZ ** multZ d (Pos 4) = Pos 12)
||| 
||| > divisorByDistrib (Pos 4) ((Pos 8)::(Pos 1)::[]) (\x => case x of { FZ => (Pos 2 ** Refl); (FS FZ) => (Pos 0 ** Refl) })
||| 
||| ... Type mismatch between 0 and 1
divisorByDistrib : (z : ZZ)
	-> (x : Vect n ZZ)
	-> ( (k : _) -> index k x `quotientOverZZ` z )
	-> (LinearCombinations.monoidsum x) `quotientOverZZ` z
divisorByDistrib z [] fn = (0 ** ringNeutralIsMultZeroL z)
{-
-- Doesn't like the (fn . FS) passed to divisorByDistrib in the recursive step.
divisorByDistrib z (xx::xxs) fn with ( divisorByDistrib z xxs (fn . FS) )
	| (dxxs ** prxxs) with (fn FZ)
		| (dxx ** prxx) = (dxx<+>dxxs ** ?divisorByDistrib_pr)
	-- divisorByDistrib_pr {z} {xx} {xxs} {fn} {dxx} {dxxs} =
	-- 	(dxx<+>dxxs)<.>z	={ ringOpIsDistributiveR dxx dxxs z }=
	-- 	(dxx<.>z)<+>(dxxs<.>z)	={ cong {f=((dxx<.>z)<+>)} prxxs }=
	-- 	(dxx<.>z)<+>sum xxs	={ cong {f=(<+>_)} prxx }=
	-- 	xx<+>sum xxs	={ rewrite sym $ monoidrec1D {v=xx} {vs=xxs} }=
	-- 	sum (x::xxs)	QED
-}
divisorByDistrib z (xx::xxs) {n=S predn} fn = ( dxx<+>dxxs ** divisorByDistrib' )
	where
		dxx : ZZ
		dxx = getWitness $ fn FZ
		prxx : dxx<.>z = xx
		prxx = getProof $ fn FZ
		dxxs : ZZ
		-- Passing (fn . FS) as an arg during proof reqs implicit arg (n).
		{-
		In REPL: "No such variable __pi_arg7"
		Otherwise:
		"Type mismatch between
			(k1 : Fin (S k)) ->
			quotientOverZZ (index k1 (xx :: xxs)) z (Type of fn)
		and
			Fin (S k) ->
			(\k1 =>
				quotientOverZZ (index k1 xxs) z) (__pi_arg7) (Expected type)

		Specifically:
			Type mismatch between
				index v1 (xx :: xxs)
			and
				index (__pi_arg7) xxs
		"

		> dxxs = getWitness $ divisorByDistrib z xxs (fn . FS)
		-}
		dxxs = getWitness $ divisorByDistrib z xxs (\i => fn (FS i))
		prxxs : dxxs<.>z = LinearCombinations.monoidsum xxs
		-- prxxs = getProof $ divisorByDistrib z xxs (fn . FS)
		prxxs = getProof $ divisorByDistrib z xxs (\i => fn (FS i))
		{-
		If you only write the following (note the missing (<.>_) from (_<.>_ = _))

		> divisorByDistrib' : (dxx<+>dxxs) = LinearCombinations.monoidsum (xx::xxs)

		then you get a type mismatch error that looks like

		"type mismatch between _ and _, specifically between

			foldrImpl (flip plusZ) (Pos 0) (plusZ xx) xxs

		and

			foldrImpl (flip plusZ) (Pos 0) (plusZ xx) xxs
		"

		which is not at all what's wrong, and is an unhelpful error message.
		-}
		divisorByDistrib' : (dxx<+>dxxs)<.>z = LinearCombinations.monoidsum (xx::xxs)
		divisorByDistrib' = trans (ringOpIsDistributiveR dxx dxxs z) $ trans (bileibniz (<+>) prxx prxxs) $ sym $ monoidrec1D {v=xx} {vs=xxs}



{-
We need to modify this formula to make the right-hand-argument of (quotientOverZZ) constant. It should perhaps be saying the (quotientOverZZ)'s right-hand-arg lies in the transpose of xs in a constant position.
-}
zipWithHeadsQuotientRelation : {zs : Vect (S predn) ZZ} -> {xs : Matrix (S predn) (S predm) ZZ} -> (k : _ ) -> ( index k $ map head $ zipWith (<#>) zs xs ) `quotientOverZZ` (head $ index k xs)
zipWithHeadsQuotientRelation {zs=z::zs} {xs=(xx::xxs)::xs} FZ = (z ** Refl)
zipWithHeadsQuotientRelation {zs=z::zs} {xs=(xx::xxs)::xs} {predn=Z} (FS prelk) = FinZElim prelk
zipWithHeadsQuotientRelation {zs=z::zs} {xs=x::xs} {predn=S prededn} (FS prelk) = zipWithHeadsQuotientRelation {zs=zs} {xs=xs} {predn=prededn} prelk

-- Should be applied to (fn) as given by the gcd equality.
zipWithHeadsQuotientRelation2 : {zs : Vect (S predn) ZZ} -> {xs : Matrix (S predn) (S predm) ZZ} -> ( fn : ( i : Fin _ ) -> (head $ Vect.index i xs) `quotientOverZZ` (head $ Vect.head xs) ) -> (k : _ ) -> ( Vect.index k $ map head $ Vect.zipWith (<#>) zs xs ) `quotientOverZZ` (head $ Vect.head xs)
zipWithHeadsQuotientRelation2 {zs} {xs} fn k = quotientOverZZtrans (zipWithHeadsQuotientRelation {zs=zs} {xs=xs} k) (fn k)

linearComboQuotientRelation : (x : Vect (S predm) ZZ) -> (xs : Matrix predn (S predm) ZZ) -> (z : Vect (S predn) ZZ)
	-> ( fn : ( i : Fin _ ) -> (head $ Vect.index i (x::xs)) `quotientOverZZ` (head x) )
	-> ( LinearCombinations.monoidsum $
			map head $
			zipWith (<#>) z (x::xs) )
		`quotientOverZZ` (head x)
linearComboQuotientRelation x xs z fn = divisorByDistrib _ _ (zipWithHeadsQuotientRelation2 {zs=z} {xs=x::xs} fn)

-- Motivation: succImplWknStep_Qfunclemma
linearComboQuotientRelation_corrollary : (x : Vect (S predm) ZZ) -> (xs : Matrix predn (S predm) ZZ) -> (z : Vect (S predn) ZZ)
	-> ( fn : ( i : Fin _ ) -> (head $ Vect.index i (x::xs)) `quotientOverZZ` (head x) )
	-> ( head $
			LinearCombinations.monoidsum $
			zipWith (<#>) z (x::xs) )
		`quotientOverZZ` (head x)
linearComboQuotientRelation_corrollary x xs z fn = quotientOverZZtrans (quotientOverZZreflFromEq $ headOfSumIsSumOfHeads _) $ linearComboQuotientRelation x xs z fn
