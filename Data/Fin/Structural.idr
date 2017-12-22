module Data.Fin.Structural

import Data.Fin
import Data.ZZ
import Control.Isomorphism

import Data.Fin.FinOrdering

{-
Structure of (Fin)s
* in general
* in terms of ordering
-}



ltePredLeft : LTE (S n) m -> LTE n m
ltePredLeft = fromLteSucc . lteSuccRight



gtnatFZImpliesIsFinSucc :
	(nel : Fin (S nu))
	-> (LTRel Z $ finToNat nel)
	-> (prednel : Fin nu ** nel = FS prednel)
gtnatFZImpliesIsFinSucc FZ ltpr = void $ succNotLTEzero ltpr
gtnatFZImpliesIsFinSucc (FS prednel) ltpr = (prednel ** Refl)



trichotomy : (n,m : Nat) -> Either (n `LT` m) $ Either (n = m) (m `LT` n)
trichotomy Z Z = Right $ Left Refl
trichotomy (S predn) Z = Right $ Right $ zLtSuccIsTrue predn
trichotomy Z (S predm) = Left $ zLtSuccIsTrue predm
trichotomy (S predn) (S predm)
	= either ( Left . LTESucc )
		( Right . either (Left . cong) (Right . LTESucc) )
	$ trichotomy predn predm

||| See (trichotomy)
eqOrGTToLT :
	Either (n = m) (LT m n)
	-> LTE m n
eqOrGTToLT = lteRelToLTE . either (Right . sym) Left

||| Allows: under decEq : (-) {smaller=notLTToGTE notlt}
notLTToGTE : Not (LT a b) -> LTE b a
notLTToGTE {a} {b} nonpr = eqOrGTToLT
	$ either (void . nonpr) id
	$ trichotomy a b



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



wknLTLast : (a : Fin n) -> LT (finToNat $ weaken a) (finToNat $ last {n=n})
wknLTLast FZ = zLtSuccIsTrue _
wknLTLast (FS k) = LTESucc $ wknLTLast k

ltenatLastIsTrue2 : (i : Fin (S nu)) -> LTERel (finToNat i) $ finToNat $ last {n=nu}
ltenatLastIsTrue2 FZ {nu=Z} = Right Refl
ltenatLastIsTrue2 (FS k) {nu=Z} = absurd k
ltenatLastIsTrue2 i {nu=S prednu} with (splitFinS i)
	| Left (k ** prwkn) = Left $ rewrite prwkn in wknLTLast {n=S prednu} k
	| Right prLast = Right $ cong {f=finToNat} prLast



{- (ltenatLastIsTrue) subsection -}

notLTSelf : Not (LT a a)
notLTSelf {a=Z} = succNotLTEzero
notLTSelf {a=S preda} = notLTSelf . fromLteSucc

lteUnique : {a, b : Nat} -> (x, y : LTERel a b) -> x = y
lteUnique (Left LTEZero) (Left LTEZero) impossible
lteUnique (Left LTEZero) (Left (LTESucc ltY)) impossible
lteUnique (Left (LTESucc ltX)) (Left LTEZero) impossible
lteUnique (Left (LTESucc ltX)) (Left (LTESucc ltY)) {b=Z} impossible
lteUnique (Left (LTESucc LTEZero)) (Left (LTESucc LTEZero)) {a=Z} {b=S right} = Refl
lteUnique (Left (LTESucc ltX)) (Left (LTESucc ltY)) {a=S left} {b=S right}
	with (lteUnique (Left ltX) (Left ltY))
	| prEq = cong {f=Left . LTESucc} $ leftInjective prEq
lteUnique (Left ltX) (Right prEq) {b}
	= void $ notLTSelf $ replace prEq {P=\x => LT x b} ltX
lteUnique (Right prEq) (Left ltY) {b}
	= void $ notLTSelf $ replace prEq {P=\x => LT x b} ltY
lteUnique (Right Refl) (Right Refl) = Refl
lteUnique (Right Refl) (Right Refl) {a=Z} {b = S right} impossible
lteUnique (Right Refl) (Right Refl) {a = S left} {b=Z} impossible

ltenatLastIsTrue : Iso (nel : Fin (S nu) ** LTERel (finToNat nel) $ finToNat $ last {n=nu}) $ Fin (S nu)
ltenatLastIsTrue = MkIso
	getWitness
	(\nel => (nel ** ltenatLastIsTrue2 nel))
	(\y => Refl)
	ltenatLastIsTrue_fromTo
	where
		ltenatLastIsTrue_fromTo :
			(x : (nel : Fin (S nu)
				** LTERel (finToNat nel) $ finToNat $ last {n=nu}))
			-> (getWitness x ** ltenatLastIsTrue2 (getWitness x)) = x
		ltenatLastIsTrue_fromTo (nel ** ltepr)
			= rewrite sameLTEPr in Refl
			where
				sameLTEPr : ltenatLastIsTrue2 nel = ltepr
				sameLTEPr = lteUnique (ltenatLastIsTrue2 nel) ltepr



{-
Nat algebraic theorems
-}



lteUnsumLeftSummandRight : (x `plus` y) `LT` z -> y `LT` z
lteUnsumLeftSummandRight {x=Z} = id
lteUnsumLeftSummandRight {x=S predx} = lteUnsumLeftSummandRight . ltePredLeft

lteUnsumLeftSummandLeft : (x `plus` y) `LT` z -> x `LT` z
lteUnsumLeftSummandLeft {x} {y} = rewrite (plusCommutative x y)
	in lteUnsumLeftSummandRight

ltePlus : (a, b : Nat) -> b `LTE` (a `plus` b)
ltePlus a Z = LTEZero
ltePlus a (S predb) = rewrite sym $ plusSuccRightSucc a predb in LTESucc $ ltePlus a predb



lteImplSuccMinusPreserved : (a, b : Nat)
	-> b `LTE` a
	-> (S a) `minus` b = S (a `minus` b)
lteImplSuccMinusPreserved a Z _ = cong $ sym $ minusZeroRight a
lteImplSuccMinusPreserved Z (S predb) lteBA = void $ succNotLTEzero lteBA
lteImplSuccMinusPreserved (S preda) (S predb) lteBA
	= lteImplSuccMinusPreserved preda predb $ fromLteSucc lteBA

natPlusInvertibleR : (a, b : Nat) -> (a `plus` b) `minus` b = a
natPlusInvertibleR a Z = trans (cong $ plusZeroRightNeutral a) $ minusZeroRight a
natPlusInvertibleR Z b = sym $ minusZeroN b
natPlusInvertibleR (S preda) (S predb)
	= trans (cong {f=\t => t `minus` predb} $ sym $ plusSuccRightSucc preda predb)
	$ trans (lteImplSuccMinusPreserved (plus preda predb) predb
		$ ltePlus preda predb)
	$ cong {f=S} $ natPlusInvertibleR preda predb

natPlusInvertibleL : (a, b : Nat) -> (b `plus` a) `minus` b = a
natPlusInvertibleL a b = rewrite plusCommutative b a in natPlusInvertibleR a b



lteToSumExpr :
	(x, m : Nat)
	-> m `LTE` x
	-> (k : Nat ** x = m `plus` k)
lteToSumExpr x Z lteMX = (x ** Refl)
lteToSumExpr Z (S predm) lteMX = void $ succNotLTEzero lteMX
lteToSumExpr (S predx) (S predm) lteMX
	= either
		(\ltMX =>
			let ltPMPX = fromLteSucc ltMX
			in let oldpr = lteToSumExpr predx (S predm) ltPMPX
			in (S $ getWitness oldpr
				** cong {f=S} $ trans (getProof oldpr)
				$ plusSuccRightSucc _ _))
		(\eqMX => (Z ** sym $ trans (cong $ plusZeroRightNeutral predm) eqMX))
	$ lteToLTERel lteMX
