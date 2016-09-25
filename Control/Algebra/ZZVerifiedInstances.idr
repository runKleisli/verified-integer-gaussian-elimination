module Control.Algebra.ZZVerifiedInstances
-- We will forego treating this as Control.Algebra.NumericVerifiedInstances

import Data.ZZ
import Control.Algebra
import Classes.Verified
import Control.Algebra.NumericInstances

-- These can be proven through an isomorphism with the free ring on the empty type.

monoidNeutralIsNeutralL_ZZ : (l : ZZ) -> l <+> Algebra.neutral = l
monoidNeutralIsNeutralL_ZZ (Pos n) = cong {f=Pos} $ plusZeroRightNeutral n
monoidNeutralIsNeutralL_ZZ (NegS n) = Refl

monoidNeutralIsNeutralR_ZZ : (r : ZZ) -> Algebra.neutral <+> r = r
monoidNeutralIsNeutralR_ZZ (Pos n) = cong {f=Pos} $ plusZeroLeftNeutral n
monoidNeutralIsNeutralR_ZZ (NegS n) = Refl

negPlusNegnatToNegnatPlus : (l, r : Nat) -> (NegS l) <+> negNat r = negNat $ S $ l `plus` r
negPlusNegnatToNegnatPlus l Z = rewrite plusZeroRightNeutral l in Refl
negPlusNegnatToNegnatPlus l (S predr) = cong {f=NegS} $ plusSuccRightSucc l predr

onePlusMinusNatReduction : (a, b : Nat) -> Pos 1 <+> minusNatZ a (S b) = minusNatZ a b
onePlusMinusNatReduction Z b = Refl
onePlusMinusNatReduction (S preda) Z = Refl
onePlusMinusNatReduction (S preda) (S predb) = onePlusMinusNatReduction preda predb

plusNegOneMinusNatProduction : (a, b : Nat) -> minusNatZ a b <+> NegS 0 = minusNatZ a (S b)
plusNegOneMinusNatProduction Z Z = Refl
plusNegOneMinusNatProduction Z (S predb) = rewrite plusZeroRightNeutral predb in Refl
plusNegOneMinusNatProduction (S preda) Z = Refl
plusNegOneMinusNatProduction (S preda) (S predb) = plusNegOneMinusNatProduction preda predb

semigroupOpIsAssociative_ZZ : (l, c, r : ZZ) -> l <+> (c <+> r) = l <+> c <+> r
semigroupOpIsAssociative_ZZ (Pos l) (Pos c) (Pos r) = cong $ plusAssociative _ _ _
semigroupOpIsAssociative_ZZ (Pos l) (Pos Z) (NegS r) = rewrite plusZeroRightNeutral l in Refl
semigroupOpIsAssociative_ZZ (Pos l) (Pos (S predc)) (NegS Z) = rewrite sym $ plusSuccRightSucc l predc in Refl
semigroupOpIsAssociative_ZZ (Pos l) (Pos (S predc)) (NegS (S predr)) = ?semigroupOpIsAssociative_ZZ_rhs_2
semigroupOpIsAssociative_ZZ (Pos l) (NegS Z) (Pos Z) = sym $ monoidNeutralIsNeutralL_ZZ _
semigroupOpIsAssociative_ZZ (Pos Z) (NegS Z) (Pos (S predr)) = Refl
semigroupOpIsAssociative_ZZ (Pos (S predl)) (NegS Z) (Pos (S predr)) = rewrite plusSuccRightSucc predl predr in Refl
semigroupOpIsAssociative_ZZ (Pos Z) (NegS (S predc)) (Pos r) = monoidNeutralIsNeutralR_ZZ _
semigroupOpIsAssociative_ZZ (Pos (S predl)) (NegS (S predc)) (Pos Z) = sym $ monoidNeutralIsNeutralL_ZZ _
semigroupOpIsAssociative_ZZ (Pos (S predl)) (NegS (S predc)) (Pos (S predr)) = ?semigroupOpIsAssociative_ZZ_rhs_3
semigroupOpIsAssociative_ZZ (Pos Z) (NegS c) (NegS r) = Refl
semigroupOpIsAssociative_ZZ (Pos (S predl)) (NegS Z) (NegS r) = Refl
semigroupOpIsAssociative_ZZ (Pos (S predl)) (NegS (S predc)) (NegS r) = ?semigroupOpIsAssociative_ZZ_rhs_4
semigroupOpIsAssociative_ZZ (NegS l) (Pos Z) (Pos r) = Refl
semigroupOpIsAssociative_ZZ (NegS Z) (Pos (S predc)) (Pos r) = Refl
semigroupOpIsAssociative_ZZ (NegS (S predl)) (Pos (S predc)) (Pos r) = ?semigroupOpIsAssociative_ZZ_rhs_5
-- This one's harder
semigroupOpIsAssociative_ZZ (NegS l) (Pos Z) (NegS Z) = Refl
semigroupOpIsAssociative_ZZ (NegS l) (Pos Z) (NegS (S predr)) = Refl
semigroupOpIsAssociative_ZZ (NegS l) (Pos (S predc)) (NegS Z) = sym $ plusNegOneMinusNatProduction predc l
{- 
* Recurses to case [ (NegS l) (Pos predc) (NegS predr) ]
* Depends on cases for [ x (NegS 0) (NegS predr) ]
-}
semigroupOpIsAssociative_ZZ (NegS l) (Pos (S predc)) (NegS (S predr)) = ?semigroupOpIsAssociative_ZZ_rhs_6
semigroupOpIsAssociative_ZZ (NegS l) (NegS Z) (Pos Z) = Refl
semigroupOpIsAssociative_ZZ (NegS l) (NegS Z) (Pos (S predr)) = rewrite plusZeroRightNeutral l in Refl
semigroupOpIsAssociative_ZZ (NegS l) (NegS c) (Pos Z) = Refl
semigroupOpIsAssociative_ZZ (NegS l) (NegS (S predc)) (Pos (S predr)) = ?semigroupOpIsAssociative_ZZ_rhs_7
semigroupOpIsAssociative_ZZ (NegS l) (NegS c) (NegS r) = rewrite sym $ plusSuccRightSucc l (c+r) in cong {f=NegS . S . S} $ plusAssociative l c r

semigroupOpIsAssociative_ZZ_rhs_2 = proof
  intros
  exact rewrite sym $ plusSuccRightSucc l predc in semigroupOpIsAssociative_ZZ (Pos l) (Pos predc) (NegS predr)

semigroupOpIsAssociative_ZZ_rhs_3 = proof
  intros
  exact semigroupOpIsAssociative_ZZ (Pos (S predl)) (NegS $ S predc) (Pos $ S predr)

semigroupOpIsAssociative_ZZ_rhs_4 = proof
  intros
  exact semigroupOpIsAssociative_ZZ (Pos predl) (NegS predc) (NegS r)

semigroupOpIsAssociative_ZZ_rhs_5 = proof
  intros
  exact semigroupOpIsAssociative_ZZ (NegS predl) (Pos predc) (Pos r)

semigroupOpIsAssociative_ZZ_rhs_6 = proof
  intros
  exact trans (semigroupOpIsAssociative_ZZ (NegS l) (Pos predc) (NegS predr)) $ _
  exact trans (cong {f=flip plusZ $ NegS predr} $ sym $ plusNegOneMinusNatProduction predc l) $ _
  exact sym $ semigroupOpIsAssociative_ZZ ((NegS l)<+>(Pos (S predc))) (NegS 0) (NegS predr)

semigroupOpIsAssociative_ZZ_rhs_7 = proof
  intros
  exact rewrite sym $ plusSuccRightSucc l predc in semigroupOpIsAssociative_ZZ (NegS l) (NegS predc) (Pos predr)

minusNatZSelfZ : (n : Nat) -> minusNatZ n n = Pos 0
minusNatZSelfZ Z = Refl
minusNatZSelfZ (S predn) = minusNatZSelfZ predn

groupInverseIsInverseL_ZZ : (l : ZZ) -> l <+> inverse l = Algebra.neutral
groupInverseIsInverseL_ZZ (Pos Z) = Refl
groupInverseIsInverseL_ZZ (Pos (S predn)) = trans (cong {f=minusNatZ predn} $ multOneRightNeutral predn) $ minusNatZSelfZ predn
groupInverseIsInverseL_ZZ (NegS n) = trans (cong {f=flip minusNatZ n} $ multOneRightNeutral n) $ minusNatZSelfZ n

groupInverseIsInverseR_ZZ : (r : ZZ) -> inverse r <+> r = Algebra.neutral
groupInverseIsInverseR_ZZ (Pos Z) = Refl
groupInverseIsInverseR_ZZ (Pos (S predn)) = trans (cong {f=minusNatZ predn} $ multOneRightNeutral predn) $ minusNatZSelfZ predn
groupInverseIsInverseR_ZZ (NegS n) = trans (cong {f=flip minusNatZ n} $ multOneRightNeutral n) $ minusNatZSelfZ n

abelianGroupOpIsCommutative_ZZ : (l, r : ZZ) -> l <+> r = r <+> l
abelianGroupOpIsCommutative_ZZ (Pos n) (Pos m) = cong $ plusCommutative _ _
abelianGroupOpIsCommutative_ZZ (NegS n) (NegS m) = cong {f=NegS . S} $ plusCommutative _ _
abelianGroupOpIsCommutative_ZZ (Pos n) (NegS m) = Refl
abelianGroupOpIsCommutative_ZZ (NegS n) (Pos m) = Refl

multZPosZRightZero : (left : ZZ) -> multZ left (Pos 0) = Pos 0
multZPosZRightZero (Pos n) = cong {f=Pos} $ multZeroRightZero _
multZPosZRightZero (NegS n) = cong {f=negNat} $ multZeroRightZero _

multZPosZLeftZero : (right : ZZ) -> multZ (Pos 0) right = Pos 0
multZPosZLeftZero (Pos n) = Refl
multZPosZLeftZero (NegS n) = Refl

ringOpIsAssociative_ZZ : (l, c, r : ZZ) -> l <.> (c <.> r) = l <.> c <.> r
ringOpIsAssociative_ZZ (Pos l) (Pos c) (Pos r) = cong $ multAssociative _ _ _
ringOpIsAssociative_ZZ (NegS l) (Pos Z) (Pos r) = rewrite cong {f=negNat} $ multZeroRightZero l in Refl
ringOpIsAssociative_ZZ (NegS l) (Pos c) (Pos Z) = trans (rewrite multZeroRightZero c in rewrite multZeroRightZero l in Refl) $ sym $ multZPosZRightZero _
ringOpIsAssociative_ZZ (NegS l) (Pos (S predc)) (Pos (S predr)) = cong {f=negNat} $ multAssociative (S l) (S predc) (S predr)
ringOpIsAssociative_ZZ (NegS l) (NegS c) (Pos Z) = rewrite multZeroRightZero c in trans (cong {f=negNat} $ multZeroRightZero l) $ cong {f=Pos} $ sym $ multZeroRightZero $ _
ringOpIsAssociative_ZZ (NegS l) (NegS c) (Pos (S predr)) = cong {f=Pos} $ multAssociative (S l) (S c) (S predr)
ringOpIsAssociative_ZZ (NegS l) (Pos Z) (NegS r) = rewrite multZeroRightZero l in Refl
ringOpIsAssociative_ZZ (NegS l) (Pos (S predc)) (NegS r) = cong {f=Pos} $ multAssociative (S l) (S predc) (S r)
ringOpIsAssociative_ZZ (NegS l) (NegS c) (NegS r) = cong {f=negNat} $ multAssociative (S l) (S c) (S r)
ringOpIsAssociative_ZZ (Pos Z) (NegS c) (Pos r) = multZPosZLeftZero _
ringOpIsAssociative_ZZ (Pos l) (NegS c) (Pos Z) = rewrite multZeroRightZero c in trans (multZPosZRightZero (Pos l)) $ sym $ multZPosZRightZero _
ringOpIsAssociative_ZZ (Pos (S predl)) (NegS c) (Pos (S predr)) = cong {f=negNat} $ multAssociative (S predl) (S c) (S predr)
ringOpIsAssociative_ZZ (Pos Z) (Pos c) (NegS r) = multZPosZLeftZero _
ringOpIsAssociative_ZZ (Pos l) (Pos Z) (NegS r) = rewrite (multZeroRightZero l) in Refl
ringOpIsAssociative_ZZ (Pos (S predl)) (Pos (S predc)) (NegS r) = cong {f=negNat} $ multAssociative (S predl) (S predc) (S r)
ringOpIsAssociative_ZZ (Pos Z) (NegS c) (NegS r) = Refl
ringOpIsAssociative_ZZ (Pos (S predl)) (NegS c) (NegS r) = cong {f=Pos} $ multAssociative (S predl) (S c) (S r)

negativeIsNegOneTimesRight : (right : ZZ) -> inverse right = (inverse Algebra.unity) <.> right
negativeIsNegOneTimesRight (Pos r) = cong {f=negNat} $ trans (multOneRightNeutral r) $ sym $ plusZeroRightNeutral r
negativeIsNegOneTimesRight (NegS r) = cong {f=Pos . S} $ trans (multOneRightNeutral r) $ sym $ plusZeroRightNeutral r

minusNatZNegOneTimesFlip : multZ (NegS 0) $ minusNatZ a b = minusNatZ b a
minusNatZNegOneTimesFlip {a=Z} {b=Z} = Refl
minusNatZNegOneTimesFlip {a=Z} {b=S predb} = cong {f=Pos . S} $ plusZeroRightNeutral predb
minusNatZNegOneTimesFlip {a=S preda} {b=S predb} = minusNatZNegOneTimesFlip {a=preda} {b=predb}

negOneDistributesL_ZZ : (c, r : ZZ) -> (inverse Algebra.unity) <.> (c <+> r) = (inverse Algebra.unity)<.>c <+> (inverse Algebra.unity)<.>r
negOneDistributesL_ZZ (Pos Z) r = rewrite monoidNeutralIsNeutralR_ZZ (NegS 0 <.> r) in rewrite monoidNeutralIsNeutralR_ZZ r in Refl
negOneDistributesL_ZZ (Pos (S predc)) (Pos Z) = rewrite plusZeroRightNeutral predc in rewrite plusZeroRightNeutral predc in Refl
negOneDistributesL_ZZ (Pos (S predc)) (Pos (S predr)) = rewrite plusZeroRightNeutral predr in rewrite plusZeroRightNeutral predc in rewrite plusZeroRightNeutral (predc+(S predr)) in cong {f=NegS} $ sym $ plusSuccRightSucc predc predr
negOneDistributesL_ZZ (Pos (S Z)) (NegS Z) = Refl
negOneDistributesL_ZZ (Pos (S $ S predc)) (NegS Z) = Refl
negOneDistributesL_ZZ (Pos (S predc)) (NegS (S predr)) = trans minusNatZNegOneTimesFlip $ rewrite plusZeroRightNeutral predc in rewrite plusZeroRightNeutral predr in Refl
negOneDistributesL_ZZ (NegS c) (Pos Z) = rewrite plusZeroRightNeutral c in rewrite plusZeroRightNeutral c in Refl
negOneDistributesL_ZZ (NegS c) (Pos (S predr)) = rewrite plusZeroRightNeutral c in rewrite plusZeroRightNeutral predr in minusNatZNegOneTimesFlip
negOneDistributesL_ZZ (NegS c) (NegS r) = cong {f=Pos . S} $ rewrite plusZeroRightNeutral (c+r) in rewrite plusZeroRightNeutral c in rewrite plusZeroRightNeutral r in plusSuccRightSucc c r

{-
If the cases where values are given as proofs are to be given as values, the totality checker must accept that, though they reference other cases of (ringOpIsDistributiveL_ZZ), (ringOpIsDistributiveL_ZZ) remains total.
-}
ringOpIsDistributiveL_ZZ : ( l, c, r : ZZ ) -> l <.> (c <+> r) = l <.> c <+> l <.> r
ringOpIsDistributiveL_ZZ (Pos l) (Pos c) (Pos r) = cong {f=Pos} $ multDistributesOverPlusRight _ _ _
ringOpIsDistributiveL_ZZ (NegS l) (Pos Z) (Pos r) = rewrite (multZeroRightZero l) in sym $ plusZeroLeftNeutralZ _
ringOpIsDistributiveL_ZZ (NegS l) (Pos (S predc)) (Pos r) = trans (cong {f=negNat} $ multDistributesOverPlusRight (S l) (S predc) r) $ sym $ negPlusNegnatToNegnatPlus _ _
ringOpIsDistributiveL_ZZ (Pos l) (NegS c) (Pos Z) = rewrite multZeroRightZero l in sym $ plusZeroRightNeutralZ _
-- if (r) is a successor, induce from the theorem on its predecessor.
ringOpIsDistributiveL_ZZ (Pos l) (NegS c) (Pos (S predr)) = ?ringOpIsDistributiveL_ZZ_rhs_3_2
-- reduces to 3 and the special case (negOneDistributesL_ZZ)
ringOpIsDistributiveL_ZZ (NegS l) (NegS c) (Pos r) = ?ringOpIsDistributiveL_ZZ_rhs_4
-- reduces to 3
ringOpIsDistributiveL_ZZ (Pos l) (Pos c) (NegS r) = ?ringOpIsDistributiveL_ZZ_rhs_5
-- reduces to 4
ringOpIsDistributiveL_ZZ (NegS l) (Pos c) (NegS r) = ?ringOpIsDistributiveL_ZZ_rhs_6
ringOpIsDistributiveL_ZZ (Pos Z) (NegS c) (NegS r) = Refl
ringOpIsDistributiveL_ZZ (Pos (S predl)) (NegS c) (NegS r) = cong {f=NegS . S}
	$ trans (cong
		$ trans (cong $ plusSuccRightSucc (S c) r)
		$ multDistributesOverPlusRight predl (S c) (S r))
	$ trans (sym $ plusAssociative c r _)
	$ trans (cong {f=plus c}
		$ trans (plusCommutative r _)
		$ trans (sym $ plusAssociative (mult predl $ S c) (mult predl $ S r) r)
		$ cong $ plusCommutative _ r)
	$ plusAssociative c (mult predl $ S c) $ plus r $ mult predl $ S r
-- Reduces to 7 and the special case (negOneDistributesL_ZZ)
ringOpIsDistributiveL_ZZ (NegS l) (NegS c) (NegS r) = ?ringOpIsDistributiveL_ZZ_rhs_8

ringOpIsDistributiveL_ZZ_rhs_3_2 = proof
  intros
  exact trans (trans (cong $ sym $ onePlusMinusNatReduction predr c) $ trans (ringOpIsDistributiveL_ZZ (Pos l) (Pos 1) (minusNatZ predr (S c))) $ rewrite multOneRightNeutral l in Refl) $ trans (cong {f=((Pos l)<+>)} $ ringOpIsDistributiveL_ZZ (Pos l) (NegS c) (Pos predr)) $ trans (semigroupOpIsAssociative_ZZ (Pos l) (negNat $ mult l $ S c) $ Pos $ mult l predr) $ trans (trans (cong {f=flip plusZ $ Pos $ mult l predr} $ abelianGroupOpIsCommutative_ZZ (Pos l) (negNat $ mult l $ S c)) $ sym $ semigroupOpIsAssociative_ZZ (negNat $ mult l $ S c) (Pos l) (Pos $ mult l predr)) $ cong {f=(plusZ $ negNat $ mult l $ S c) . Pos} $ trans (cong {f=flip plus $ mult l predr} $ sym $ multOneRightNeutral l) $ sym $ multDistributesOverPlusRight l 1 predr

{-
-- As written in REPL
ringOpIsDistributiveL_ZZ_rhs_4 = proof
  intros
  exact trans (cong {f=(flip multZ $ minusNatZ r $ S c) . NegS} $ sym $ plusZeroRightNeutral l) $ trans (sym $ ringOpIsAssociative_ZZ (inverse Algebra.unity) (Pos (S l)) $ minusNatZ r (S c)) _
  exact trans (cong {f=multZ $ inverse unity} $ ringOpIsDistributiveL_ZZ (Pos (S l)) (NegS c) (Pos r)) $ _
  exact trans (negOneDistributesL_ZZ (Pos (S l) <.> NegS c) (Pos (S l) <.> Pos r)) _
  exact trans (cong $ sym $ negativeIsNegOneTimesRight (Pos (S l) <.> Pos r)) _
  exact trans (rewrite plusZeroRightNeutral $ c+l*(S c) in Refl) $ cong {f=plusZ $ Pos $ S $ plus c $ mult l $ S c} _
  exact cong {f=negNat} $ multOneRightNeutral _

-----

-- Two lines, works in REPL. Patched to derive proof seen below.
ringOpIsDistributiveL_ZZ_rhs_4 = proof
  intros
  exact trans (cong {f=(flip multZ $ minusNatZ r $ S c) . NegS} $ sym $ plusZeroRightNeutral l) $ trans (sym $ ringOpIsAssociative_ZZ (inverse Algebra.unity) (Pos (S l)) $ minusNatZ r (S c)) $ trans (cong {f=multZ $ inverse unity} $ ringOpIsDistributiveL_ZZ (Pos (S l)) (NegS c) (Pos r)) $ trans (negOneDistributesL_ZZ (Pos (S l) <.> NegS c) (Pos (S l) <.> Pos r)) $ trans (cong $ sym $ negativeIsNegOneTimesRight (Pos (S l) <.> Pos r)) $ _
  exact trans (rewrite plusZeroRightNeutral $ c+l*(S c) in Refl) $ cong {f=plusZ $ Pos $ S $ plus c $ mult l $ S c} $ cong {f=negNat} $ multOneRightNeutral _
-}
-- One line/ squashed.
ringOpIsDistributiveL_ZZ_rhs_4 = proof
  intros
  exact trans (cong {f=(flip multZ $ minusNatZ r $ S c) . NegS} $ sym $ plusZeroRightNeutral l) $ trans (sym $ ringOpIsAssociative_ZZ (inverse Algebra.unity) (Pos (S l)) $ minusNatZ r (S c)) $ trans (cong {f=multZ $ inverse unity} $ ringOpIsDistributiveL_ZZ (Pos (S l)) (NegS c) (Pos r)) $ trans (negOneDistributesL_ZZ (Pos (S l) <.> NegS c) (Pos (S l) <.> Pos r)) $ trans (cong $ sym $ negativeIsNegOneTimesRight (Pos (S l) <.> Pos r)) $ trans (cong {f=(flip plusZ $ negNat (mult (plus r (mult l r)) 1)) . Pos . S} $ plusZeroRightNeutral _) $ cong {f=plusZ $ Pos $ S $ plus c $ mult l $ S c} $ cong {f=negNat} $ multOneRightNeutral _

ringOpIsDistributiveL_ZZ_rhs_5 = proof
	intros
	exact trans (cong {f=((Pos l) <.>)} $ abelianGroupOpIsCommutative_ZZ (Pos c) (NegS r)) $ trans (ringOpIsDistributiveL_ZZ (Pos l) (NegS r) (Pos c)) $ abelianGroupOpIsCommutative_ZZ ((Pos l)<.>(NegS r)) ((Pos l)<.>(Pos c))

ringOpIsDistributiveL_ZZ_rhs_6 = proof
	intros
	exact trans (cong {f=((NegS l) <.>)} $ abelianGroupOpIsCommutative_ZZ (Pos c) (NegS r)) $ trans (ringOpIsDistributiveL_ZZ (NegS l) (NegS r) (Pos c)) $ abelianGroupOpIsCommutative_ZZ ((NegS l)<.>(NegS r)) ((NegS l)<.>(Pos c))

-- mirrors the proof of rhs_4 / case (NegS l) (NegS c) (Pos r).
ringOpIsDistributiveL_ZZ_rhs_8 = proof
  intros
  exact trans (rewrite sym $ plusZeroRightNeutral l in Refl) $ _
  -- THIS LINE HERE IS CLEARER THAN IN rhs_4's proof! Change (NegS r) to (Pos r).
  exact trans (sym $ ringOpIsAssociative_ZZ (inverse Algebra.unity) (Pos (S l)) $ NegS c <+> NegS r) $ _
  exact trans (cong {f=multZ $ inverse unity} $ ringOpIsDistributiveL_ZZ (Pos (S l)) (NegS c) (NegS r)) $ _
  exact trans (negOneDistributesL_ZZ (Pos (S l) <.> NegS c) (Pos (S l) <.> NegS r)) _
  exact trans ( cong {f=plusZ (multZ (NegS 0) (Pos (S l) <.> NegS c))} $ sym $ negativeIsNegOneTimesRight (Pos (S l) <.> NegS r) ) $ _
  {-
  HERE THE PROOF IS DIFFERENT BECAUSE THE CONGs ON THE (multOneRightNeutral)
  WOULD HAVE TO BE DIFFERENT.
  -}
  exact trans (rewrite plusZeroRightNeutral $ c+l*(S c) in Refl) $ _
  exact rewrite multOneRightNeutral (r+l*(S r)) in Refl

ringOpIsCommutative_ZZ : ( l, r : ZZ ) -> l <.> r = r <.> l
ringOpIsCommutative_ZZ (Pos l) (Pos r) = cong $ multCommutative l r
ringOpIsCommutative_ZZ (NegS l) (Pos r) = cong {f=negNat} $ multCommutative (S l) r
ringOpIsCommutative_ZZ (Pos l) (NegS r) = cong {f=negNat} $ multCommutative l (S r)
ringOpIsCommutative_ZZ (NegS l) (NegS r) = cong {f=Pos} $ multCommutative (S l) (S r)

ringOpIsDistributiveR_ZZ : ( l, c, r : ZZ ) -> (l <+> c) <.> r = l <.> r <+> c <.> r
ringOpIsDistributiveR_ZZ l c r = trans (ringOpIsCommutative_ZZ (l<+>c) r)
	$ trans (ringOpIsDistributiveL_ZZ r l c)
	$ trans (cong {f=((r<.>l) <+>)} $ ringOpIsCommutative_ZZ r c)
	$ cong {f=(<+> (c<.>r))} $ ringOpIsCommutative_ZZ r l

ringWithUnityIsUnityL_ZZ : ( l : ZZ ) -> l <.> Algebra.unity = l
ringWithUnityIsUnityL_ZZ (Pos l) = cong $ multOneRightNeutral l
ringWithUnityIsUnityL_ZZ (NegS l) = cong $ multOneRightNeutral l

ringWithUnityIsUnityR_ZZ : ( r : ZZ ) -> Algebra.unity <.> r = r
ringWithUnityIsUnityR_ZZ (Pos r) = cong $ multOneLeftNeutral r
ringWithUnityIsUnityR_ZZ (NegS r) = cong $ multOneLeftNeutral r

instance VerifiedSemigroup ZZ where
	semigroupOpIsAssociative = semigroupOpIsAssociative_ZZ

instance VerifiedMonoid ZZ where {
	monoidNeutralIsNeutralL = monoidNeutralIsNeutralL_ZZ
	monoidNeutralIsNeutralR = monoidNeutralIsNeutralR_ZZ
}

instance VerifiedGroup ZZ where {
	groupInverseIsInverseL = groupInverseIsInverseL_ZZ
	groupInverseIsInverseR = groupInverseIsInverseR_ZZ
}

instance VerifiedAbelianGroup ZZ where {
	abelianGroupOpIsCommutative = abelianGroupOpIsCommutative_ZZ
}

instance VerifiedRing ZZ where {
	ringOpIsAssociative = ringOpIsAssociative_ZZ
	ringOpIsDistributiveL = ringOpIsDistributiveL_ZZ
	ringOpIsDistributiveR = ringOpIsDistributiveR_ZZ
}

instance VerifiedRingWithUnity ZZ where {
	ringWithUnityIsUnityL = ringWithUnityIsUnityL_ZZ
	ringWithUnityIsUnityR = ringWithUnityIsUnityR_ZZ
}
