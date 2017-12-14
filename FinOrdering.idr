module FinOrdering
-- Classes (OrdRel, DecLT) are redundant with IntegerOrdering.idr

import Data.Fin
import Data.ZZ
import Control.Isomorphism



{-
Definitions
-}



-- Note that unlike (=) the types do not inherently need to be ambiguous
class OrdRel A where
	LTRel : A -> A -> Type

LTERel : OrdRel s => s -> s -> Type
LTERel a b = Either (LTRel a b) (a=b)

class (OrdRel s) => DecLT s where
	decLT : (x1 : s) -> (x2 : s) -> Dec ( LTRel x1 x2 )

class (OrdRel s) => DecLTE s where
	decLTE : (x1 : s) -> (x2 : s) -> Dec ( LTERel x1 x2 )

implDeclte : (DecLT s, DecEq s) => (a, b: s) -> Dec ( LTERel a b )
implDeclte a b with (decEq a b)
	| Yes x = Yes (Right x)
	| No x with (decLT a b)
		| Yes y = Yes (Left {b=(a=b)} y)
		| No y = No (either y x)

{-
Won't let us work with this at all.
---
instance (DecLT s, DecEq s) => DecLTE s where
	-- decLTE = implDeclte
	decLTE = ?declte_from_ltNeq

=====

Compiles but doesn't resolve any of the falsely split instances
---
instance (OrdRel s, DecLT s, DecEq s) => DecLTE s where
	decLTE ?= implDeclte {s=s} @{the (DecLT s) %instance} @{the (DecEq s) %instance}

=====

Other things we tried
---

instance (OrdRel s, DecLT s, DecEq s) => DecLTE s where
	decLTE ?= implDeclte {s=s} @{the (OrdRel s) %instance} @{the (DecLT s) %instance} @{the (DecEq s) %instance}

instance (OrdRel s, DecLT s, DecEq s) => DecLTE s where
	decLTE = ?declte_from_ltNeq
-}

instance OrdRel Nat where
	LTRel = LT

instance DecLT Nat where
	decLT a b = isLTE (S a) b

||| Normalizes the notion of decidable LTE provided by Prelude.Nat.isLTE.
decLTENat : (n, m : Nat) -> Dec ( LTERel n m )
decLTENat a b with (decEq a b)
	| Yes pr = Yes (Right pr)
	| No prneq with (decLT a b)
		| Yes pr = Yes (Left pr)
		| No pr = No ( either pr prneq )

instance DecLTE Nat where
	decLTE = decLTENat

{-
-- Just use `finToNat`.
instance DecLT (Fin n) where
	decLT {n} = decLTFin n
-}



{-
Equivalence between LTERel and LTE
-}



lteToLTERel : {a, b : Nat} -> LTE a b -> LTERel a b
lteToLTERel LTEZero {b=Z} = Right Refl
lteToLTERel LTEZero {b=S predb} = Left $ LTESucc $ LTEZero {right=predb}
lteToLTERel (LTESucc ltepr) {a=S preda} {b=S predb} = either
	(Left . LTESucc)
	(Right . (cong {f=S}))
	$ lteToLTERel ltepr

lteRelToLTE : LTERel a b -> LTE a b
lteRelToLTE (Left lt) = fromLteSucc . lteSuccRight $ lt
lteRelToLTE (Right pr) = rewrite pr in lteRefl



{-
Productions
-}



zLtSuccIsTrue : (k : Nat) -> LTRel Z (S k)
zLtSuccIsTrue _ = LTESucc LTEZero

natGtAnyImpliesGtZ : (m, n : Nat) -> LTRel m n -> LTRel Z n
natGtAnyImpliesGtZ m Z = absurd
natGtAnyImpliesGtZ m (S n) = const $ zLtSuccIsTrue n



{-
Structure of (Fin)s
* in general
* in terms of ordering
-}



gtnatFZImpliesIsFinSucc :
	(nel : Fin (S nu))
	-> (LTRel Z $ finToNat nel)
	-> (prednel : Fin nu ** nel = FS prednel)
gtnatFZImpliesIsFinSucc FZ ltpr = void $ succNotLTEzero ltpr
gtnatFZImpliesIsFinSucc (FS prednel) ltpr = (prednel ** Refl)

ltenatLastIsTrue : Iso (nel : Fin (S nu) ** LTERel (finToNat nel) $ finToNat $ last {n=nu}) $ Fin (S nu)

ltenatLastIsTrue2 : (i : Fin (S nu)) -> LTERel (finToNat i) $ finToNat $ last {n=nu}

trichotomy : (n,m : Nat) -> Either (n `LT` m) $ Either (n = m) (m `LT` n)
trichotomy Z Z = Right $ Left Refl
trichotomy (S predn) Z = Right $ Right $ zLtSuccIsTrue predn
trichotomy Z (S predm) = Left $ zLtSuccIsTrue predm
trichotomy (S predn) (S predm)
	= either ( Left . LTESucc )
		( Right . either (Left . cong) (Right . LTESucc) )
	$ trichotomy predn predm
