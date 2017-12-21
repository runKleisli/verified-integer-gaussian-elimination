module ImplicitArgsError

import Data.Vect

{-
Expected behavior here - Idris throws an error

> implTy : Type -> Type
> implTy ty = Vect n ty -> Nat

"
When checking right hand side of implTy with expected type
        Type

When checking an application of type constructor Data.Vect.Vect:
        No such variable n
"
-}

-- This creates a problem down the line
implTy : Type -> Type
implTy ty = {n : Nat} -> Vect n ty -> Nat

-- This seems fine
fn : (ty : Type) -> (offender : implTy ty) -> Nat
fn ty offender = foo
	where
		barA : Vect 5 ()	
		barB : implTy ty
		foo : Nat

{-
-- However, this one is a problem
fn2 : (ty : Type) -> (offender : implTy ty) -> Nat
fn2 ty offender = foo
	where
		barA : Type	
		barB : implTy barA
		foo : Nat
-}

-- Similar problem here, with implTy2 and fn3
implTy2 : Vect n () -> Type
implTy2 v {n} = {m : Nat} -> Vect m (Vect n ()) -> Nat

{-
fn3 : (xs : Vect n ()) -> (offender : implTy2 xs) -> Nat
fn3 xs offender = foo
	where
		barA : Vect 5 ()	
		barB : implTy2 barA
		foo : Nat
-}

{-
This seems okay, where there is no parameter to the type, because the problem occurs when (offender) interacts with another value of the type-valued function.
-}
implTy3 : Type
implTy3 = {n : Nat} -> Vect n () -> Nat

fn4 : (xs : Vect n ()) -> (offender : implTy3) -> Nat
fn4 xs offender = foo
	where
		bar : implTy3
		foo : Nat

{-
Namespace refinement doesn't help

---

fn5 : (xs : Vect n ()) -> (offender : ImplicitArgsError.implTy2 xs) -> Nat
fn5 xs offender = foo
	where
		barA : Vect 5 ()
		barB : ImplicitArgsError.implTy2 barA
		foo : Nat
-}

{-
Independence of the other arguments of the function type on the implicit argument does not resolve the situation.
-}
implTy4 : Vect n () -> Type
implTy4 v {n} = {m : Nat} -> Integer

{-
fn6 : (xs : Vect n ()) -> (offender : implTy4 xs) -> Integer
fn6 xs offender = foo
	where
		barA : Vect 5 ()
		barB : implTy4 barA
		foo : Integer
-}

-- It does not matter if there is no implicit argument to the type-valued function.
implTy5 : Either () () -> Type
implTy5 v = {m : Nat} -> Integer

{-
fn7 : (xs : Either () ()) -> (offender : implTy5 xs) -> Integer
fn7 xs offender = foo
	where
		barA : Either () ()
		barB : implTy5 barA
		foo : Integer
-}

{-
Finally, when the type-valued function is given explicit parameters in the inner value, you get a relevant error:

"Can't infer argument m1 to offender"

---

fn7 : (xs : Either () ()) -> (offender : implTy5 xs) -> Integer
fn7 xs offender = foo
	where
		bar : implTy5 $ Left ()
		foo : Integer

-----

... But not if the explicit parameter is specified indirectly.

---

fn8 : (xs : Either () ()) -> (offender : implTy5 xs) -> Integer
fn8 xs offender = foo
	where
		barA : Either () ()
		barA = Left ()
		barB : implTy5 barA
		foo : Integer

-}

{-

Relevant error:

"Can't infer argument m1 to offender"

---

fn9 : (offender : implTy5 $ Left ()) -> Integer
fn9 offender = foo
	where
		foo : Integer
-}

{-
Relevant error

	"Can't infer argument m1 to offender"

and no explicit arguments passed to the type-valued function.

---

fn10 : (xs : Either () ()) -> (offender : implTy5 xs) -> Integer
fn10 xs offender = foo
	where
		bar : ()
		foo : Integer
-}

{-
A distinct irrelevant error:

"
When checking right hand side of fn11 with expected type
        Integer

No such variable offender
"

---

fn11 : (xs : Either () ()) -> (offender : implTy5 xs) -> Integer
fn11 xs offender = offender {m=0}
-}

{-
When checking argument l to constructor Prelude.Either.Left:
        () is not a numeric type

---

fn12 : (offender : implTy5 $ Left 5) -> Integer
fn12 offender = offender {m=0}

---

fn13 : (offender : implTy5 $ Left 5) -> Integer
fn13 = (\offender => offender {m=0})

---

fn13 : (offender : implTy5 $ Left 5) -> Integer
fn13 = (\offender => offender 0)

---

fn14 : (offender : implTy5 $ Left 5) -> Integer
fn14 = ?fn14'
-}

{-
When checking right hand side of fn15 with expected type
        (xs : Either () ()) -> implTy5 xs -> Integer

No such variable friend

---

fn15 : (xs : Either () ()) -> (offender : implTy5 xs) -> Integer
fn15 = (\xs => \friend => friend 0)

---

fn16 : (xs : Either () ()) -> (offender : implTy5 xs) -> Integer
fn16 = (\xs => (\friend => friend {m=0}))
-}
