module RowEchelon

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

import ZZModuleSpan
import Data.Matrix.LinearCombinations

import FinOrdering
import FinStructural

-- For style. ((Reader r a) equivalent to (r -> a))
import Control.Monad.Identity
import Control.Monad.Reader

import Control.Isomorphism



{-
Table of contents:
* ZZ proofs
* Vect/Matrix proofs
* The leading nonzero of a vector
* DANRZ property
* Corollary bispannability property
* Row echelon properties
-}



{-
ZZ proofs
-}



zzZOrOrPosNeg : (z : ZZ) -> Either (z=Pos 0) $ Either (k : _ ** z = Pos (S k)) $ (k : _ ** z = NegS k)
zzZOrOrPosNeg (Pos Z) = Left Refl
zzZOrOrPosNeg (Pos (S k)) = Right (Left (k ** Refl))
zzZOrOrPosNeg (NegS k) = Right (Right (k ** Refl))



{-
Vect/Matrix proofs
-}



indicesConstColChariz : indices i FZ (map (r::) xs) = r
indicesConstColChariz {i} {r}
	= trans (sym $ indexMapChariz {f=index FZ})
	$ trans (cong {f=index i} $ leadingElemExtensionFirstColReplicate r)
	indexReplicateChariz

indicesConstColChariz2 : indices i (FS j) (map (r::) xs) = indices i j xs
indicesConstColChariz2 {i} {j}
	= trans (sym $ indexMapChariz {f=index (FS j)})
	$ trans (cong {f=index i} leadingElemExtensionColFSId)
	$ indexMapChariz {f=index j}



{-
The leading nonzero of a vector

* (leadingNonzeroNum) Its computation
* (leadingNonzeroProp) The leading nonzero property of a (Maybe (Fin n)) for a vector --
	if Nothing, the vector is 0
	if Just k, k is the leading nonzero of the vector
* (leadingNonzeroProof) Proof the computation gives the leading nonzero (has the leading nonzero prop)
-}



leadingNonzeroNum : (v : Vect n ZZ) -> Maybe (Fin n)
leadingNonzeroNum [] = Nothing
leadingNonzeroNum {n= S predn} (Pos Z::xs) = map FS $ leadingNonzeroNum xs
leadingNonzeroNum {n= S predn} (k::xs) = Just FZ

leadingNonzeroProp : (v : Vect n ZZ) -> Maybe (Fin n) -> Type
leadingNonzeroProp {n} v mnel =
	Either
		(mnel = Nothing, v = neutral)
		( nel : Fin n **
			(mnel = Just nel
			, {i : Fin n}
				-> finToNat i `LTRel` finToNat nel
				-> index i v = Pos Z
			, Not (index nel v = Pos Z) )
		)

leadingNonzeroProof_lemmaNeutToNothing : leadingNonzeroNum Algebra.neutral = Nothing
leadingNonzeroProof_lemmaNeutToNothing = ?leadingNonzeroProof_lemmaNeutToNothing'

leadingNonzeroProof_lemmaNeutToNothing' = proof
	intro n
	induction n
	exact Refl
	intro predn
	exact cong {f=map FS}



leadingNonzeroProof : {v : Vect n ZZ} -> leadingNonzeroProp v (leadingNonzeroNum v)
leadingNonzeroProof {v=[]} = Left (Refl, Refl)
leadingNonzeroProof {n=S predn} {v=Pos Z::rs} with (leadingNonzeroProof {v=rs})
	| Left (_, pr) = rewrite pr
		in Left (cong {f=map FS} leadingNonzeroProof_lemmaNeutToNothing, Refl)
	| Right (nel ** (isJ, l_fn, r_pr))
		= Right (FS nel ** (cong {f=map FS} isJ, l_fn', r_pr))
		where
			l_fn' : {ii : Fin (S predn)}
				-> finToNat ii `LTRel` finToNat (FS nel)
				-> index ii (Pos Z::rs) = Pos Z
			l_fn' {ii=FZ} _ = Refl
			l_fn' {ii=FS j} precondit = l_fn $ fromLteSucc precondit
leadingNonzeroProof {n=S predn} {v=Pos (S k)::rs}
	= Right ( FZ **
		(Refl, void . succNotLTEzero, flip (replace {P=distinguish_Z_SZ}) ()) )
		where
			distinguish_Z_SZ : ZZ -> Type
			distinguish_Z_SZ (Pos Z) = Void
			distinguish_Z_SZ z = ()
leadingNonzeroProof {n=S predn} {v=NegS k::rs}
	= Right ( FZ **
		(Refl, void . succNotLTEzero, flip (replace {P=distinguish_Z_SZ}) ()) )
		where
			distinguish_Z_SZ : ZZ -> Type
			distinguish_Z_SZ (Pos Z) = Void
			distinguish_Z_SZ z = ()



{-
lemma1 : leadingNonzeroNum rs = Nothing -> leadingNonzeroNum (Pos Z :: rs) = Nothing
lemma1 = ?lemma1'

lemma1_mat : leadingNonzeroNum (index nel xs) = Nothing
	-> leadingNonzeroNum (index (FS nel) $ map ((Pos Z)::) xs) = Nothing

lemma2 : leadingNonzeroNum rs = Nothing -> rs = Algebra.neutral
lemma2 = ?lemma2'

lemma3 : leadingNonzeroNum rs = Just mel
	-> leadingNonzeroNum (Pos Z :: rs) = Just (FS mel)

lemma3_mat : leadingNonzeroNum (index nel xs) = Just mel
	-> leadingNonzeroNum (index (FS nel) $ map ((Pos Z)::) xs) = Just (FS mel)
-}

||| (x::xs) leads with a nonzero for x not 0
leadingNonzeroIsFZIfNonzero :
	Not (index FZ x = Pos Z)
	-> leadingNonzeroNum x = Just FZ
leadingNonzeroIsFZIfNonzero {x=x::xs} nonz with ( runIso eitherBotRight $ map nonz $ mirror $ zzZOrOrPosNeg x )
	| Left (k ** prposS) = rewrite prposS in Refl
	| Right (k ** prnegS) = rewrite prnegS in Refl



{-
DANRZ property:
That every entry (<= horiz, > vert) below and not to the right of this one is 0.
-}



downAndNotRightOfEntryImpliesZ : (xs : Matrix n m ZZ) -> (row : Fin n) -> (col : Fin m) -> Type
downAndNotRightOfEntryImpliesZ xs nel mel {n} {m} = (i : Fin n) -> (j : Fin m) -> (finToNat nel `LTRel` finToNat i) -> (finToNat j `LTERel` finToNat mel) -> indices i j xs = Pos Z
{-
Equivalent properties:
1) map (take mel) (drop nel xs) = neutral
2) (nel `LT` i) -> (j `LTE` mel) -> indices i j xs = Pos Z
	# In pseudocode, because we decided not to use direct LT and LTE of Fins.

---

We cannot write

> downAndNotRightOfEntryImpliesZ : (xs : Matrix n m ZZ) -> (row : Fin n) -> (col : Fin m) -> Type
> downAndNotRightOfEntryImpliesZ xs nel mel {n} {m} = {i : Fin n} -> {j : Fin m} -> (finToNat nel `LTRel` finToNat i) -> (finToNat j `LTERel` finToNat mel) -> indices i j xs = Pos Z

because the error described in ImplicitArgsError applied to (i) and (j) in ({i : Fin n} -> {j : Fin m} -> ...).
-}



weakenDownAndNotRight :
	downAndNotRightOfEntryImpliesZ mat (FS prednel) mel
	-> ((j : _)
		-> LTERel (finToNat j) (finToNat mel)
		-> indices (FS prednel) j mat = Pos Z)
	-> downAndNotRightOfEntryImpliesZ mat (weaken prednel) mel
weakenDownAndNotRight {prednel} {mat} danrz newzfn i j iDown jNotRight
	= either
		(\b => danrz i j b jNotRight)
		(\pr => trans (cong {f=\e => indices e j mat} pr) $ newzfn j jNotRight)
	$ partitionNatWknLT prednel i iDown

||| A special case of (weakenDownAndNotRight).
weakenDownAndNotRightFZ :
	downAndNotRightOfEntryImpliesZ mat (FS prednel) FZ
	-> indices (FS prednel) FZ mat = Pos Z
	-> downAndNotRightOfEntryImpliesZ mat (weaken prednel) FZ
weakenDownAndNotRightFZ {prednel} {mat} danrz newz i FZ iDown fzNotRight
	= either
		(\b => danrz i FZ b fzNotRight)
		(\pr => trans (cong {f=\e => indices e FZ mat} pr) newz)
	$ partitionNatWknLT prednel i iDown
weakenDownAndNotRightFZ _ _ _ (FS prel) _ fzNotRight
	= void . succNotLTEzero . lteRelToLTE $ fzNotRight



total
afterUpdateAtCurStillDownAndNotRight :
	(downAndNotRightOfEntryImpliesZ mat (FS prednel) mel)
	-> (downAndNotRightOfEntryImpliesZ (updateAt (FS prednel) f mat) (FS prednel) mel)
afterUpdateAtCurStillDownAndNotRight {prednel=FZ} {mat=x::y::xs} {mel} danrz FZ j iDown jNotRight = void $ succNotLTEzero $ iDown
afterUpdateAtCurStillDownAndNotRight {prednel=FZ} {mat=x::y::xs} {mel} danrz (FS FZ) j iDown jNotRight = void $ succNotLTEzero $ fromLteSucc iDown
afterUpdateAtCurStillDownAndNotRight {prednel=FZ} {mat=x::y::xs} {mel} danrz (FS $ FS i) j iDown jNotRight = danrz (FS $ FS i) j iDown jNotRight
afterUpdateAtCurStillDownAndNotRight {prednel=FS predednel} {mat=x::xs} {f} danrz FZ j iDown jNotRight = danrz FZ j iDown jNotRight
afterUpdateAtCurStillDownAndNotRight {prednel=FS predednel} {mat=x::xs} {mel} {f} danrz (FS i) j iDown jNotRight = afterUpdateAtCurStillDownAndNotRight {prednel=predednel} {mat=xs} {mel=mel} {f=f} (\i_xs => \j_xs => \iDown_xs => \jNotRight_xs => danrz (FS i_xs) j_xs (LTESucc iDown_xs) jNotRight_xs) i j (fromLteSucc iDown) jNotRight



{-
Subsection proving (danrzLeadingZeroAlt)
-}

{-
Proved by noting
	getCol FZ xs = map (index FZ) xs
and
	\j => danrz j FZ ?lt ?lte :
		(j : Fin _) -> index FZ $ index j xs = Pos 0
becomes by (trans (indexMapChariz {f=index FZ})) a
	(j : Fin _) -> index j $ map (index FZ) xs = Pos 0.

So that it suffices to prove
	((i : Fin _) -> index i xs = index i ys)
	-> xs = ys.
-}
danrzTailHasLeadingZeros :
	downAndNotRightOfEntryImpliesZ (x::xs) FZ FZ
	-> getCol FZ xs = Algebra.neutral
danrzTailHasLeadingZeros danrz = vecIndexwiseEq
	(\j => trans (indexMapChariz {f=index FZ})
		$ trans (danrz (FS j) FZ (zLtSuccIsTrue $ finToNat j) $ Right Refl)
	$ sym $ indexNeutralIsNeutral1D j)

-- Corrollary : decEq w/ eitherBotRight lets you extract rowEchelon proofs.
-- In particular,
||| x|xs
||| 0|_
||| 0|_
||| ...
||| has 0th-col 0 or its 0th row leads with a nonzero
danrzLeadingZeroAlt :
	downAndNotRightOfEntryImpliesZ (x::xs) FZ FZ
	-> Either
		(getCol FZ (x::xs) = Algebra.neutral)
		(leadingNonzeroNum x = Just FZ)
danrzLeadingZeroAlt {x} {xs} danrz with ( decEq (index FZ x) $ Pos Z )
	| Yes preq = Left (vecHeadtailsEq preq $ danrzTailHasLeadingZeros danrz)
	| No prneq = Right $ leadingNonzeroIsFZIfNonzero prneq



danrzLastcolImpliesAllcol : {mat : Matrix (S _) (S mu) ZZ}
	-> downAndNotRightOfEntryImpliesZ mat FZ (last {n=mu})
	-> downAndNotRightOfEntryImpliesZ mat FZ mel
danrzLastcolImpliesAllcol danrzlast i j ltrel _ = danrzlast i j ltrel $ ltenatLastIsTrue2 j

danrzLastcolImpliesTailNeutral : {xs : Matrix n (S mu) ZZ}
	-> downAndNotRightOfEntryImpliesZ (x::xs) FZ (last {n=mu})
	-> xs=Algebra.neutral
danrzLastcolImpliesTailNeutral {x} {xs} {n} {mu} danrz
	= uniformValImpliesReplicate (replicate (S mu) $ Pos 0) xs
	$ \na => uniformValImpliesReplicate (Pos 0) (index na xs) (fn na)
	where
		fn : (prednel : Fin n) -> (j : Fin (S mu)) -> indices prednel j xs = Pos 0
		fn prednel j = danrz (FS prednel) j
			(zLtSuccIsTrue $ finToNat prednel)
			(ltenatLastIsTrue2 j)



{-
Corollary bispannability property
-}



bispansNulltailcolExtension : downAndNotRightOfEntryImpliesZ (x::xs) FZ FZ
	-> ys `bispanslz` map Vect.tail xs
	-> map ((Pos Z)::) ys `bispanslz` xs
bispansNulltailcolExtension = bispansNullcolExtension . danrzTailHasLeadingZeros



{-
Row echelon properties

Definitions
* (echPreTy) The per-row component of (rowEchelonPre)
* (rowEchelonPre) The row echelon property in terms of (leadingNonzeroNum) & its correctness
* (echTy) The per-row component of (rowEchelon)
* (rowEchelon) The row echelon property -- (rowEchelonPre) but with numbers having the leading nonzero property (leadingNonzeroProp) -- inferable about (leadingNonzeroNum) using (leadingNonzeroProof), hence inferable from a given (rowEchelonPre) proof.

Theorems
* rowEchelonPreZeroHeight
* rowEchelonPreExtension
	Inducing gaussian elimination verification from the lesser height & width cases,
	done when first column is nonzero.
* echelonPreNullcolExtension
	Inducing gaussian elimination from the lesser width cases,
	done when first column is zero.
* echelonPreFromDanrzLast
	For verifying gaussian elimination in the width = 1 case
* toEchTy
* toRowEchelon
-}



echPreTy : (xs : Matrix n m ZZ) -> (nel : Fin n) -> Type
echPreTy {n} {m} xs nel =
	Either
		((nelow : Fin n) -> (ltpr : finToNat nel `LTERel` finToNat nelow)
			-> index nelow xs = Algebra.neutral)
		(mel : Fin m ** (leadingNonzeroNum $ index nel xs = Just mel
			, downAndNotRightOfEntryImpliesZ xs nel mel))

{-
Lemma about left case of (echPreTy):

Everything zero below or at a row of xs
=>
for all (x::xs)
for mel = last
downAndNotRightOfEntryImpliesZ xs nel mel

See also (echelonFromDanrzLast),
the converse (danrzLastcolImpliesTailNeutral) of this from (ZZGaussianElimination)
-}

rowEchelonPre : (xs : Matrix n m ZZ) -> Type
rowEchelonPre {n} {m} xs = (narg : Fin n) -> echPreTy xs narg

||| For best results, prove in terms of `echPreTy` using `toEchTy`
echTy : (xs : Matrix n m ZZ) -> (nel : Fin n) -> Type
echTy {n} {m} xs nel =
	Either
		((nelow : Fin n) -> (ltpr : finToNat nel `LTERel` finToNat nelow)
			-> index nelow xs = Algebra.neutral)
		(mel : Fin m ** (leadingNonzeroProp (index nel xs) (Just mel)
			, downAndNotRightOfEntryImpliesZ xs nel mel))

||| For best results, prove in terms of `rowEchelonPre` using `toRowEchelon`
rowEchelon : (xs : Matrix n m ZZ) -> Type
rowEchelon {n} {m} xs = (narg : Fin n) -> echTy xs narg



rowEchelonPreZeroHeight : rowEchelonPre []
rowEchelonPreZeroHeight = \narg => FinZElim narg

rowEchelonPreZeroWidth : rowEchelonPre $ replicate n []
rowEchelonPreZeroWidth = \narg => Left $ \_ => \_ => indexReplicateChariz

rowEchelonPreExtension :
	{x : Vect (S predm) ZZ}
	-> {xs : Matrix n predm ZZ}
	-> leadingNonzeroNum x = Just FZ
	-> rowEchelonPre xs
	-> rowEchelonPre $ x :: map ((Pos 0)::) xs
rowEchelonPreExtension {n} {predm} {x} {xs} lnz ech FZ =
	Right (FZ ** (lnz, danrzFn))
	where
		danrzFn : (i : Fin (S n))
			-> (j : Fin (S predm))
			-> LTE 1 (finToNat i)
			-> Either (LTE (S (finToNat j)) 0) (finToNat j = 0)
			-> indices i j $ x :: map ((Pos 0)::) xs = Pos 0
		danrzFn FZ _ lteOZ _ = void $ succNotLTEzero lteOZ
		{- column 0 and row > 0 to x::(0-col|xs) is index 0 to a 0::(xs!i) is 0 -}
		danrzFn (FS k) j _ orJZ
			= rewrite
			either (void . succNotLTEzero) (finToNatInjective j FZ) orJZ
			in indicesConstColChariz
rowEchelonPreExtension {n} {predm} {x} {xs} lnz ech (FS narg) with ( ech narg )
	{-
	Left case
	---

	Outline:

	indices i j xs = Pos Z <=> index j $ index i xs = Pos Z

	index nelow xs = replicate predm (Pos 0)
	<=> forall j, index j $ index nelow xs = Pos Z

	Consider:

	lteSuccRight :: LTE (S m) n -> LTE (S m) (S n)

	Consider this context:

	intros
	exact Left _
	intro snelow
	intro ltReSnelow

	But instead we do:

	exact Left _
	intro snelow
	either snelow is FZ or snellow is FS k.
	If snelow is FZ, we need to show (index FZ $ x::_ = 0 === x = 0),
		so we must show snelow can't be FZ
		which follows from (ltReSnelow) being an either of two
		characterizations of (finToNat snelow) as a successor.
	If snelow is (FS predsnelow), we need to show
		(index predsnelow xs = 0),
	which follows from (neutfn predsnelow)
	given a weakening of the LTE
	-}
	| Left neutfn = Left zFn
		where
			zFn : (snelow : Fin (S n))
				-> Either
					((S $ finToNat narg) `LTRel` (finToNat snelow))
					(S $ finToNat narg = finToNat snelow)
				-> index snelow $ x :: map ((Pos 0)::) xs
					= Algebra.neutral
			zFn FZ ltReSnelow = void
				$ either succNotLTEzero SIsNotZ ltReSnelow
			zFn (FS predsnelow) ltReSnelow = trans indexMapChariz
				$ cong $ neutfn predsnelow
				$ either
					(Left . fromLteSucc)
					(Right . succInjective
						(finToNat narg)
						(finToNat predsnelow))
					ltReSnelow
	{-
	Right case
	---

	* lnzJMelEq -> lnzJMelEq' :
		If (leadingNonzeroNum xs!narg = Just mel),
		so will the extension (x::(0-col|xs)) have (Just (FS mel)) at (FS narg)
	* See (danrzFn) comments
	-}
	| Right (mel ** (lnzJMelEq, danrzNelMel))
		= Right (FS mel **
				(trans (cong {f=leadingNonzeroNum} indexMapChariz)
					$ cong {f=map FS} lnzJMelEq
				, danrzFn))
		where
			{-
			When i and j a successor, apply danrzNelMel.
			When i a successor and j = 0, const (const Refl).
			When i = 0, the LTE is absurd.
			-}
			danrzFn : (i : Fin (S n))
				-> (j : Fin (S predm))
				-> (S $ finToNat narg) `LTRel` (finToNat i)
				-> Either ((finToNat j) `LTRel` (S $ finToNat mel))
					(finToNat j = S $ finToNat mel)
				-> indices i j $ x :: map ((Pos 0)::) xs = Pos 0
			danrzFn FZ _ ltNI _ = void $ succNotLTEzero ltNI
			danrzFn (FS i') FZ ltNI ltJSM = indicesConstColChariz
			danrzFn (FS i') (FS j') ltNI ltJSM
				= trans indicesConstColChariz2
					$ danrzNelMel i' j' ltNI' ltJSM'
				where
					ltNI' = fromLteSucc ltNI
					ltJSM' = either
						(Left . fromLteSucc)
						(Right . succInjective
							(finToNat j')
							(finToNat mel))
						ltJSM

echelonPreNullcolExtension :
	{xs : Matrix n predm ZZ}
	-> rowEchelonPre xs
	-> rowEchelonPre $ map ((Pos 0)::) xs
echelonPreNullcolExtension {n} {predm} {xs} ech narg with ( ech narg )
	| Left neutfn = Left $ \nelow => \ltpr =>
		trans indexMapChariz
		$ cong {f=((Pos 0)::)} $ neutfn nelow ltpr
	| Right (mel ** (lnzJMelEq, danrzNelMel))
		= Right (FS mel **
			(trans (cong {f=leadingNonzeroNum} indexMapChariz)
			$ cong {f=map FS} lnzJMelEq
			, danrzFn))
		where
			{-
			When j = 0, const (const Refl)
			When j a successor, apply (danrzNelMel).
			-}
			danrzFn : (i : Fin n)
				-> (j : Fin (S predm))
				-> finToNat narg `LTRel` finToNat i
				-> finToNat j `LTERel` (S $ finToNat mel)
				-> indices i j $ map ((Pos 0)::) xs = Pos 0
			danrzFn i FZ _ _ = indicesConstColChariz
			danrzFn i (FS j') ltNI ltJSM = trans indicesConstColChariz2
				$ danrzNelMel i j' ltNI
				$ either
					(Left . fromLteSucc)
					(Right . succInjective
						(finToNat j')
						(finToNat mel))
					ltJSM



echelonPreFromDanrzLast :
	{mat : Matrix (S n) (S mu) ZZ}
	-> downAndNotRightOfEntryImpliesZ mat FZ (last {n=mu})
	-> rowEchelonPre mat
echelonPreFromDanrzLast {mat=x::xs} {n} {mu} danrz FZ with (leadingNonzeroProof {v=x})
	| Left nothPrAndZeroPr = Left echelonPreFromDanrzLast_Nothing
	where
		echelonPreFromDanrzLast_Nothing :
			(nelow : Fin (S n))
			-> (ltepr : Either (0 `LT` finToNat nelow) (0 = finToNat nelow))
			-> index nelow (x::xs) = Algebra.neutral
		echelonPreFromDanrzLast_Nothing nelow (Left ltpr)
			= trans
				(cong {f=\ts => Vect.index nelow (x::ts)}
				$ danrzLastcolImpliesTailNeutral {x=x} {xs=xs} danrz)
			$ trans (cong {f=(\i => Vect.index i (x::Algebra.neutral))}
				$ getProof $ gtnatFZImpliesIsFinSucc nelow ltpr)
			$ indexNeutralIsNeutral2D _
		echelonPreFromDanrzLast_Nothing nelow (Right eqpr)
			= rewrite sym $ finToNatInjective FZ nelow eqpr
			in snd nothPrAndZeroPr
	| Right (mel ** melpr)
		= Right $ (mel ** (fst melpr, danrzLastcolImpliesAllcol {mel=mel} danrz))
echelonPreFromDanrzLast {mat=x::xs} danrz (FS k) with (leadingNonzeroProof {v=index k xs})
	| Left nothPrAndZeroPr = Left echelonPreFromDanrzLast_Nothing2
	where
		echelonPreFromDanrzLast_Nothing2 :
			(nelow : Fin (S _))
			-> (ltepr : Either
				(finToNat (FS k) `LT` finToNat nelow)
				(finToNat (FS k) = finToNat nelow))
			-> index nelow (x::xs) = Algebra.neutral
		echelonPreFromDanrzLast_Nothing2 nelow (Left ltpr)
			= trans
				(cong {f=\ts => Vect.index nelow (x::ts)}
				$ danrzLastcolImpliesTailNeutral {x=x} {xs=xs} danrz)
			$ trans (cong {f=(\i => Vect.index i (x::Algebra.neutral))}
				$ getProof $ gtnatFZImpliesIsFinSucc nelow
				$ natGtAnyImpliesGtZ
					(S $ finToNat k) (finToNat nelow) ltpr)
			$ indexNeutralIsNeutral2D _
		echelonPreFromDanrzLast_Nothing2 nelow (Right eqpr)
			= rewrite sym $ finToNatInjective (FS k) nelow eqpr
			in snd nothPrAndZeroPr
	| Right (mel ** melpr) = void $ (snd $ snd melpr)
		$ flip trans (indexNeutralIsNeutral1D mel)
		$ cong {f=index mel}
		$ trans (cong {f=index k}
			$ danrzLastcolImpliesTailNeutral {x=x} {xs=xs} danrz)
		$ indexNeutralIsNeutral2D k



toEchTy : echPreTy xs nel -> echTy xs nel
toEchTy ech = map prrw ech
	where
		prrw (mel ** (pr, danrz))
			= (mel ** (rewrite sym pr in leadingNonzeroProof, danrz))

toRowEchelon : rowEchelonPre xs -> rowEchelon xs
toRowEchelon echxs = \narg => toEchTy (echxs narg)
