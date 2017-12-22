module Data.ZZ.ModuloVerification

import Control.Algebra
import Classes.Verified

import Data.ZZ
import Control.Algebra.NumericInstances
import Control.Algebra.ZZVerifiedInstances
import Data.Matrix.AlgebraicVerified	-- For (groupDivisionAddLToSubR)

import Control.Algebra.ZZDivisors

import Data.Fin.FinOrdering
import Data.Fin.Structural

-- For (groupDivisionAddLToSubR)
import Control.Algebra.DiamondInstances



{-
Table of contents

* ZZ algebraic theorems
* Lemmas for (modNatFnIsRemainder)
* (modNatFnIsRemainder)
	Generate proofs of the quotient-remainder relation for binary
	modulo operations on naturals from simpler properties.
* modZGen - generate a verified ZZ modulo from a verified Nat modulo.
-}



{-
ZZ algebraic theorems
-}



invertByNegativity : ZZ -> ZZ -> ZZ
invertByNegativity x (Pos y) = x
invertByNegativity x (NegS y) = inverse x

timesToAbs :
	(x, y : ZZ)
	-> (x `invertByNegativity` y) <.> y = x <.> Pos (absZ y)
timesToAbs (Pos x') (Pos y') = Refl
timesToAbs (Pos x') (NegS y') =
	trans ( cong {f=((inverse $ Pos x')<.>) . NegS}
		$ sym $ multOneRightNeutral y' )
	$ ringNegationCancelsWithMult (Pos x') (Pos (S y'))
timesToAbs (NegS x') (Pos y') = Refl
timesToAbs (NegS x') (NegS y') = rewrite multOneRightNeutral x' in Refl



{- (modNatFnIsRemainder) parameters -}

parameters (
	modNatFn : Nat -> Nat -> Nat
	, modNatFnIdModZero :
		(x : Nat)
		-> x `modNatFn` Z = x
	, modNatFnCharizLT :
		(x, m : Nat)
		-> (x `LT` m)
		-> x `modNatFn` m = x
	, modNatFnCharizGTE :
		(x, m : Nat)
		-> (m `plus` x) `modNatFn` m = x `modNatFn` m
	){



{-
Lemmas for (modNatFnIsRemainder)

* (modNatFnPreservesZero)
* What to do with induction on constructed quotient-remainder pairs.
-}



modNatFnPreservesZero :
	(m : Nat) -> Z `modNatFn` m = Z
modNatFnPreservesZero Z = modNatFnIdModZero Z
modNatFnPreservesZero (S predm) = modNatFnCharizLT Z (S predm) $ LTESucc LTEZero



modNatFnCharizModulusPlus2 :
	(x, m, k : Nat)
	-> x = (k `mult` m) `plus` (x `modNatFn` m)
	-> m `plus` x = (S k `mult` m) `plus` (x `modNatFn` m)
modNatFnCharizModulusPlus2 x m k pr
	= trans (cong {f=plus m} pr)
	$ plusAssociative m _ _

-- by (modNatFnCharizModulusPlus2) & (modNatFnCharizGTE)
modNatFnCharizModulusPlus :
	(x, m, k : Nat)
	-> x = (k `mult` m) `plus` (x `modNatFn` m)
	-> m `plus` x = (S k `mult` m) `plus` ((m `plus` x) `modNatFn` m)
modNatFnCharizModulusPlus x m k pr
	= trans (modNatFnCharizModulusPlus2 x m k pr)
	$ cong $ sym $ modNatFnCharizGTE x m

modNatFnLTToDiffZ :
	(x, m : Nat)
	-> (x `LT` m)
	-> (Z `mult` m) `plus` (x `modNatFn` m) = x
modNatFnLTToDiffZ = modNatFnCharizLT



{-
(modNatFnIsRemainder):
Proof of the quotient-remainder expression for (modNatFn)

Proof of the quotient-remainder expression
for any natural in terms of any modulus
-}



{-
Proof sketch:

Either x < m or x of the form m+x' for some x.
(lteToSumExpr)

If m+x' then (modNatFnCharizModulusPlus):

x = (k `mult` m) `plus` (x `modNatFn` m)
-> m `plus` x = (S k `mult` m) `plus` ((m `plus` x) `modNatFn` m)

so that (modNatFnCharizModulusPlus x' m)
applied to
the divisor-remainder factorization for x'
gives a divisor-remainder factorization for (m `plus` x')
which by transitivity with the proof (x = m `plus` x')
gives the divisor-remainder factorization for x.
wwtbd.

(multDistributesOverPlusRight), implicitly.
(modNatFnLTToDiffZ)

---

Totality:

This proof recurses from an (x) of the form (m+x') into (x') when (m <= x).
However, it only does so in cases where (m > 0).
Thus,
m + x' = x
==>
x' = x - m < x

---

Structure:

Note that the proof itself follows the recursion pattern of one modulo proof.

Thus, given a better modulo algorithm, there should be a corresponding
better proof of the quotient-remainder property.

-}



%reflection
modNatFnIsRemainder :
	(x, m : Nat)
	-> (d : Nat ** (d `mult` m) `plus` (x `modNatFn` m) = x)
modNatFnIsRemainder Z _ = (0 ** modNatFnPreservesZero _)
modNatFnIsRemainder x Z = (0 ** modNatFnIdModZero _)
modNatFnIsRemainder x m
	= either
		(\ltXM => (Z ** modNatFnLTToDiffZ x m ltXM))
		(\gteXM =>
			let gteXM' = lteRelToLTE $ either (Right . sym) Left gteXM
			in let xAsMPlus = lteToSumExpr x m gteXM'
			in let divremx' = modNatFnIsRemainder (getWitness xAsMPlus) m
			in let prevNatTChariz
				= modNatFnCharizModulusPlus
					(getWitness xAsMPlus)
					m
					(getWitness divremx')
					$ sym $ getProof divremx'
			in (S $ getWitness divremx'
				** sym
				$ trans (getProof xAsMPlus)
				$ trans prevNatTChariz
				$ rewrite (sym $ getProof xAsMPlus) in Refl))
	$ trichotomy x m

} {- (modNatFnIsRemainder) parameters -}



{- modZGen parameters -}
parameters (
	modN : Nat -> Nat -> Nat
	, quotientPartN : (x, m : Nat)
		-> (d : Nat ** (d `mult` m) `plus` (x `modN` m) = x)
	) {

modZGenFn2 : ZZ -> ZZ -> ZZ
modZGenFn2 x m = Pos (absZ x `modN` absZ m)

modZGenFn : ZZ -> ZZ -> ZZ
modZGenFn x@(Pos x') m = x `modZGenFn2` m
modZGenFn x@(NegS x') m = inverse $ inverse x `modZGenFn2` m

{-
Bug: Registers as "possibly not total due to recursive path" in self,
but the pattern-matching recursion graph is

case NegS
 |
 v
case Pos (no call to (modZGenQuot) from Pos)

-}
modZGenQuot : (x : ZZ) -> (m : ZZ)
	-> (x <-> (x `modZGenFn` m)) `quotientOverZZ` m
modZGenQuot x@(Pos x') m =
	let quotientPartN' = quotientPartN x' (absZ m)
	in let witty = Pos (getWitness quotientPartN') `invertByNegativity` m
	in (witty
		** groupDivisionAddLToSubR
			(witty <.> m)
			(x `modZGenFn` m)
			x
		$ trans (cong {f=(<+>(Pos $ x' `modN` absZ m))}
			$ timesToAbs (Pos $ getWitness quotientPartN') m)
		$ cong {f=Pos} $ getProof quotientPartN'
		)
modZGenQuot x@(NegS x') m =
	quotientOverZZtrans
	(inverse Algebra.unity
		**
		trans (ringOpIsDistributiveL (inverse Algebra.unity) (Pos $ S x') _)
		$ bileibniz (<+>)
			(cong $ plusZeroRightNeutral x')
			(trans (ringOpIsCommutative_ZZ _ _)
			$ cong {f=inverse . inverse . Pos . (\t => t `modN` absZ m) . S}
			$ sym $ multOneRightNeutral x'
			)
		)
	$ modZGenQuot (Pos $ S x') m



} {- modZGen parameters -}
