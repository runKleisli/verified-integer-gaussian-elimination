module WeakenedPredicateError

import Data.Fin

{-
-- Can't do this for some reason
bad1 : { p : {m : Nat} -> Fin (S m) -> a -> Type }
	-> ( (i : Fin predn)
		-> Sigma a (p $ weaken $ FS i)
		-> Sigma a (p $ weaken $ weaken i) )
	-> (i : Fin predn)
	-> Sigma a ((p . weaken) $ FS i)
	-> Sigma a ((p . weaken) $ weaken i)
-}

{-
-- Universe inconsistency when not entered in REPL.
bad2 : ?bad2_ty
bad2_ty = proof
  exact {a : Type} -> { p : {m : Nat} -> Fin (S m) -> a -> Type } -> {predn : Nat} -> _
  exact _ -> _
  exact (i : Fin predn) -> Sigma a (p $ weaken $ FS i) -> Sigma a (p $ weaken $ weaken i)
  exact (i : Fin predn) -> Sigma a _ -> Sigma a _
  exact (p . weaken) $ FS i
  exact (p . weaken) $ weaken i
-}

{-
-- Same as bad1 but with the implicit argument to (p) filled in in each application.
bad3 : { p : {m : Nat} -> Fin (S m) -> a -> Type }
	-> ( (i : Fin predn)
		-> Sigma a (p {m=S predn} $ weaken $ FS i)
		-> Sigma a (p {m=S predn} $ weaken $ weaken i) )
	-> (i : Fin predn)
	-> Sigma a (((p {m=S predn}) . weaken) $ FS i)
	-> Sigma a (((p {m=S predn}) . weaken) $ weaken i)
-}

good1 : (p : {m : Nat} -> Fin m -> a -> Type)
	-> (i : Fin n)
	-> (fn : (x : a) -> (j : Fin n) -> p j x -> p (weaken j) x)
	-> (pr : Sigma a (p i))
	-> Sigma a (p $ weaken i)
good1 = ?good1_pr

good1_pr = proof
  intros
  exact (getWitness pr ** fn (getWitness pr) i (getProof pr))

good2 : (p : {m : Nat} -> Fin m -> a -> Type)
	-> (i : Fin n)
	-> ( fn : (j : Fin n) -> Sigma a (p j) -> Sigma a (p $ weaken j) )
	-> (pr : Sigma a (p i))
	-> Sigma a (p $ weaken i)
good2 = ?good2_pr

good2_pr = proof
  intros
  exact fn i pr

good3 : (n : Nat)
	-> (p : (m : Nat) -> Fin m -> a -> Type)
	-> (i : Fin n)
	-> (fn : (x : a) -> (j : Fin n) -> p n j x -> p (S n) (weaken j) x)
	-> Sigma a (p n i)
	-> Sigma a (p (S n) (weaken i))

-- Same as bad3 but with the first argument of (p) explicit.
good4 : { p : (m : Nat) -> Fin (S m) -> a -> Type }
	-> ( (i : Fin predn)
		-> Sigma a (p (S predn) $ weaken $ FS i)
		-> Sigma a (p (S predn) $ weaken $ weaken i) )
	-> (i : Fin predn)
	-> Sigma a (((p (S predn)) . weaken) $ FS i)
	-> Sigma a (((p (S predn)) . weaken) $ weaken i)

{-
bad4 : { p : {m : Nat} -> Fin (S m) -> a -> Type }
	-> ( (i : Fin predn)
		-> Sigma a (p {m=S predn} $ weaken $ FS i)
		-> Sigma a (p {m=S predn} $ weaken $ weaken i) )
	-> Nat
-}

{-
bad5 : { p : {m : Nat} -> Fin (S m) -> a -> Type }
	-> (i : Fin predn)
	-> Sigma a (((p {m=S predn}) . weaken) $ FS i)
-}

{-
bad6 : ( p : {m : Nat} -> Nat -> a -> Type )
	-> (i : Nat)
	-> Sigma a (p {m=Z} i)
-}

{-
bad7 : ( p : {m : Nat} -> a -> Type )
	-> Sigma a (p {m=Z})
-}

{-
bad8 : (a : Type)
	-> ( p : {m : Nat} -> a -> Type )
	-> Sigma a (p {m=Z})
-}

{-
-- Different error : No such variable (p)
bad9 : (a : Type)
	-> ( p : {m : Nat} -> a -> Type )
	-> (x : a)
	-> (p {m=Z} x)
	-> Sigma a (p {m=Z})
-}

{-
-- No such variable (p)
bad10 : ( p : {m : Nat} -> Type )
	-> Sigma Nat (\n => p {m=n})
-}

{-
-- No such variable (p)
bad11 : ( p : {m : Nat} -> Type )
	-> (p {m=Z})
	-> Sigma Nat Fin
-}

-- For whatever reason, this is fine to declare.
good5 : ( p : {m : Nat} -> Type )
	-> Sigma Nat p
good5 = ?good5_pr

{-
> :prove good5_pr
----------                 Goal:                  ----------
{hole0} : (p : Type) -> Sigma Nat p
-WeakenedPredicateError.good5_pr> intro
----------              Other goals:              ----------
{hole0}
----------              Assumptions:              ----------
 p : Type
----------                 Goal:                  ----------
{hole1} : Sigma Nat p
-WeakenedPredicateError.good5_pr> exact (Z ** _)

----------              Assumptions:              ----------
 p : Type
----------                 Goal:                  ----------
{pf505} : p 0
-}

{-
-- No such variable (p)
bad12 : ( p : {m : Nat} -> Type )
	-> p Z
	-> Sigma Nat p
-}

{-
-- No such variable (p)
bad13 : ( p : {m : Nat} -> Type )
	-> (a : Nat ** p {m=a})
-}

{-
"
When checking argument P to type constructor Builtins.Sigma:
        Type mismatch between
                Type (Type of p)
        and
                Type (Expected type)
"

---

bad14 : ( p : {m : Nat} -> Type )
	-> (a : Nat ** p)
-}
