module FinOrdering
-- Classes (OrdRel, DecLT) are redundant with IntegerOrdering.idr

import Data.Fin
import Data.ZZ


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

lteToLTERel : {a, b : Nat} -> LTE a b -> LTERel a b
lteToLTERel LTEZero {b=Z} = Right Refl
lteToLTERel LTEZero {b=S predb} = Left $ LTESucc $ LTEZero {right=predb}
lteToLTERel (LTESucc ltepr) {a=S preda} {b=S predb} = either
	(Left . LTESucc)
	(Right . (cong {f=S}))
	$ lteToLTERel ltepr
