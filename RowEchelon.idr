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

-- For style. ((Reader r a) equivalent to (r -> a))
import Control.Monad.Identity
import Control.Monad.Reader

import Control.Isomorphism



{-
Table of contents:
* Fin proofs
* Vect/Matrix proofs
* The leading nonzero of a vector
* DANRZ property
* Row echelon properties
-}



{-
Fin proofs
-}



total
FinSZAreFZ : (x : Fin 1) -> x=FZ
FinSZAreFZ FZ = Refl
FinSZAreFZ (FS voda) = FinZElim voda

commuteFSWeaken : (i : Fin n) -> (FS $ weaken i = weaken $ FS i)
commuteFSWeaken i = Refl



{-
"
LTE (S (finToNat last)) (finToNat i)  cannot be a parameter of Prelude.Uninhabited.Uninhabited
(Type class arguments must be injective)
"

> instance Uninhabited (LTE (S $ finToNat $ last {n=n}) (finToNat $ the (Fin (S n)) i)) where {
> 	uninhabited = ?notSNatLastLTEAnything
> }
-}

-- notSNatLastLTEAnything : LTE (S $ finToNat $ last {n=n}) (finToNat $ the (Fin (S n)) i) -> Void

total
notSNatLastLTEAnything : {n : Nat} -> {i : Fin (S n)} -> LTE (S $ finToNat $ last {n=n}) (finToNat i) -> Void
notSNatLastLTEAnything {n} {i=FZ} = uninhabited
notSNatLastLTEAnything {n=Z} {i=FS pri} = FinZElim pri
notSNatLastLTEAnything {n=S predn} {i=FS pri} = notSNatLastLTEAnything . fromLteSucc



finToNatWeaken : {k : Fin n} -> finToNat k = finToNat (weaken k)
finToNatWeaken {k=FZ} = Refl
finToNatWeaken {k=FS k} = cong {f=S} $ finToNatWeaken {k}

partitionNatWknLT : (pnel : Fin n) -> (el : Fin (S n)) -> (elDown : LTRel (finToNat $ weaken pnel) (finToNat el)) -> Either ( LTRel (finToNat $ FS pnel) (finToNat el) ) ( el=FS pnel )
partitionNatWknLT pnel el elDown = map (sym . (finToNatInjective (FS pnel) el)) $ lteToLTERel $ lteFromEqLeft (cong {f=S} $ sym finToNatWeaken) elDown
	where
		lteFromEqLeft : (a=b) -> LTE a c -> LTE b c
		lteFromEqLeft pr lel = rewrite (sym pr) in lel



total
splitFinS : (i : Fin (S predn)) -> Either ( k : Fin predn ** i = weaken k ) ( i = Data.Fin.last )
splitFinS {predn=Z} FZ = Right Refl
splitFinS {predn=Z} (FS j) = absurd j
splitFinS {predn=S prededn} FZ = Left ( FZ ** Refl )
splitFinS {predn=S prededn} (FS prednel) with ( splitFinS prednel )
	| Left ( k ** pr ) = Left ( FS k ** cong pr )
	| Right pr = Right $ cong pr



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



weakenDownAndNotRight : (downAndNotRightOfEntryImpliesZ mat (FS prednel) mel) -> ((j : _) -> LTERel (finToNat j) (finToNat mel) -> indices (FS prednel) j mat = Pos Z) -> downAndNotRightOfEntryImpliesZ mat (weaken prednel) mel
weakenDownAndNotRight {prednel} {mat} danrz newzfn i j iDown jNotRight = either (\b => danrz i j b jNotRight) (\pr => trans (cong {f=\e => indices e j mat} pr) $ newzfn j jNotRight) $ partitionNatWknLT prednel i iDown

||| A special case of (weakenDownAndNotRight).
weakenDownAndNotRightFZ : (downAndNotRightOfEntryImpliesZ mat (FS prednel) FZ) -> (indices (FS prednel) FZ mat = Pos Z) -> downAndNotRightOfEntryImpliesZ mat (weaken prednel) FZ
weakenDownAndNotRightFZ {prednel} {mat} danrz newz i FZ iDown fzNotRight = either (\b => danrz i FZ b fzNotRight) (\pr => trans (cong {f=\e => indices e FZ mat} pr) newz) $ partitionNatWknLT prednel i iDown



{-
Row echelon properties
* (echPreTy) The per-row component of (rowEchelonPre)
* (rowEchelonPre) The row echelon property in terms of (leadingNonzeroNum) & its correctness
* (rowEchelon) The row echelon property -- (rowEchelonPre) but with numbers having the leading nonzero property (leadingNonzeroProp) -- inferable about (leadingNonzeroNum) using (leadingNonzeroProof), hence inferable from a given (rowEchelonPre) proof.
-}



echPreTy : (xs : Matrix n m ZZ) -> (nel : Fin n) -> Type
echPreTy {n} {m} xs nel =
	Either
		((nelow : Fin n) -> (ltpr : finToNat nel `LTERel` finToNat nelow)
			-> index nelow xs = Algebra.neutral)
		(mel : Fin m ** (leadingNonzeroNum $ index nel xs = Just mel
			, downAndNotRightOfEntryImpliesZ xs nel mel))

{-
Lemma about left case:

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



rowEchelonPreEmpty : rowEchelonPre []
rowEchelonPreEmpty = \narg => FinZElim narg

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
