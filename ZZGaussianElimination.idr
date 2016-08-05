module ZZGaussianElimination

import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module

import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20

import Data.ZZ
import Control.Algebra.NumericInstances
import Control.Algebra.ZZVerifiedInstances

import ZZModuleSpan

import FinOrdering

-- For style. ((Reader r a) equivalent to (r -> a))
import Control.Monad.Identity
import Control.Monad.Reader



{-
Trivial lemmas and plumbing
-}



total
FinSZAreFZ : (x : Fin 1) -> x=FZ
FinSZAreFZ FZ = Refl
FinSZAreFZ (FS voda) = FinZElim voda

last_rw : Fin (n+(S predk))
last_rw {n} {predk} = rewrite sym (plusSuccRightSucc n predk) in last {n=n+predk}

{-
-- Impossible to have this type
last_rw2 : ( the (Fin (S $ n+predk)) last = the (Fin (n + (S predk))) last )
last_rw2 {n} {predk} = rewrite sym (plusSuccRightSucc n predk) in Refl
-}

{-
-- Seems impossible to prove this, actually. Maybe with careful study.
last_rw2 : ( last_rw {n=n} {predk=predk} ~=~ Data.Fin.last {n=n+predk} )
last_rw2 = ?last_rw2_pr
-- last_rw2 {n} {predk} = rewrite sym (plusSuccRightSucc n predk) in Refl
-}

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

notSNatLastLTEAnything : {n : Nat} -> {i : Fin (S n)} -> LTE (S $ finToNat $ last {n=n}) (finToNat i) -> Void



total
splitFinS : (i : Fin (S predn)) -> Either ( k : Fin predn ** i = weaken k ) ( i = Data.Fin.last )
splitFinS {predn=Z} FZ = Right Refl
splitFinS {predn=Z} (FS j) = absurd j
splitFinS {predn=S prededn} FZ = Left ( FZ ** Refl )
splitFinS {predn=S prededn} (FS prednel) with ( splitFinS prednel )
	| Left ( k ** pr ) = Left ( FS k ** cong pr )
	| Right pr = Right $ cong pr

plusOneVectIsSuccVect : Vect (n+1) a = Vect (S n) a
plusOneVectIsSuccVect {a} {n} = sym $ cong {f=\k => Vect k a} $ trans (cong {f=S} $ sym $ plusZeroRightNeutral n) $ plusSuccRightSucc n Z

appendedSingletonAsSuccVect : (xs : Vect n a) -> (v : a) -> Vect (S n) a
appendedSingletonAsSuccVect {a} {n} xs v = rewrite sym $ plusOneVectIsSuccVect {a=a} {n=n} in (xs++[v])

consAppendedSingleton : {xs : Vect n a} -> appendedSingletonAsSuccVect (x::xs) v = x::appendedSingletonAsSuccVect xs v
consAppendedSingleton {x} {xs} {v} {a} {n} = the ( appendedSingletonAsSuccVect (x::xs) v = x::appendedSingletonAsSuccVect xs v ) ?consAppendedSingleton_rhs

{-
-- Too many problems with this, rewriting the types to handle Nat addition.
lastInd : {xs : Vect n a} -> Data.Vect.index Data.Fin.last (rewrite sym $ plusOneVectIsSuccVect {a=a} {n=n} in (xs++[v])) = v
-}

-- Could this be done with the reversal isomorphism of each Fin?
lastInd : {xs : Vect n a} -> index Data.Fin.last $ appendedSingletonAsSuccVect xs v = v
lastInd {xs=[]} = Refl
lastInd {xs=x::xs} {v} = rewrite consAppendedSingleton {x=x} {xs=xs} {v=v} in (lastInd {xs=xs} {v=v})
{-

"ERROR ON INTROS" BUG, CASE, SOLUTION

--------

> lastInd {xs=x::xs} = ?lastInd_rhs_2

> :prove lastInd_rhs_2
lastInd_rhs_2> intro

Type mismatch between
        Vect k a = Vect k a
and
        Vect (S (S k)) a = Vect (S (plus k 1)) a

which I think means the type signature for (lastInd) is being reanalyzed in the presence of (x::xs), as if inlined, in such a way that the sucessor to rewrite is the one inside rather than outside, or something.

This works fine:

> lastInd {xs=x::xs} {v} = the ( (index Data.Fin.last $ appendedSingletonAsSuccVect (x::xs) v) = v ) ?lastInd_rhs_2

and spells out

> lastInd {xs=x::xs} {v} = the ( (index Data.Fin.last $ appendedSingletonAsSuccVect (x::xs) v) = v ) ( rewrite consAppendedSingleton {x=x} {xs=xs} {v=v} in lastInd {xs=xs} {v=v} )

-}

{-
Could this be done with the reversal isomorphism of each Fin and a proof that weaken becomes FS under it?
-}
total
weakenedInd : {xs : Vect n a} -> index (weaken k) $ appendedSingletonAsSuccVect xs v = index k xs
weakenedInd {xs=[]} {k} = absurd k
weakenedInd {xs=x::xs} {k=FZ} {v} = rewrite consAppendedSingleton {x=x} {xs=xs} {v=v} in Refl
weakenedInd {xs=x::xs} {k=FS j} {v} = rewrite consAppendedSingleton {x=x} {xs=xs} {v=v} in weakenedInd {xs=xs} {k=j} {v}



{-
BUG: Wrong type displayed given implicit argument in argument

Incorrect type displayed:

\a : Type => \p : ({m : Nat} -> Fin (S m) -> a -> Type) => p (weaken $ FZ {k=Z})
	: (a : Type) ->
	  Fin (S m) -> a -> Type ->
	  a -> Type

Correct type displayed:

\a : Type => \p : ((m : Nat) -> Fin (S m) -> a -> Type) => p 5 (weaken FZ)
	: (a : Type) ->
	  ((m : Nat) -> Fin (S m) -> a -> Type) ->
	  a -> Type

Note that these examples both actually have the correct type, they're just not displayed correctly.
-}



weakenThenProp : (p : {m : Nat} -> Fin (S m) -> a -> Type ) -> ({m : Nat} -> Fin m -> a -> Type)
weakenThenProp p = p . weaken

fai_regrwkn_liftdomain: { p : {m : Nat} -> Fin (S m) -> a -> Type }
	-> ( (i : Fin (S predn))
		-> ( w : a ** p (FS i) w )
		-> ( w' : a ** p (weaken i) w' ) )
	-> (i : Fin predn)
	-> ( w : a ** p (weaken $ FS i) w )
	-> ( w' : a ** p (weaken $ weaken i) w' )

fai_regrwkn_chty : { p : {m : Nat} -> Fin (S m) -> a -> Type }
	-> ( (i : Fin predn)
		-> ( w : a ** p (weaken $ FS i) w )
		-> ( w' : a ** p (weaken $ weaken i) w' ) )
	-> (i : Fin predn)
	-> ( w : a ** (weakenThenProp p) (FS i) w )
	-> ( w' : a ** (weakenThenProp p) (weaken i) w' )

{-
-- For some reason, it's not allowed to use (p . weaken) instead of (weakenThenProp p).
fai_regrwkn_chty : { p : {m : Nat} -> Fin (S m) -> a -> Type }
	-> ( (i : Fin predn)
		-> ( w : a ** p (weaken $ FS i) w )
		-> ( w' : a ** p (weaken $ weaken i) w' ) )
	-> (i : Fin predn)
	-> ( w : a ** (p . weaken) (FS i) w )
	-> ( w' : a ** (p . weaken) (weaken i) w' )
-}

fai_regrwkn : { p : {m : Nat} -> Fin (S m) -> a -> Type }
	-> ( (i : Fin (S predn))
		-> ( w : a ** p (FS i) w )
		-> ( w' : a ** p (weaken i) w' ) )
	-> (i : Fin predn)
	-> ( w : a ** (weakenThenProp p) (FS i) w )
	-> ( w' : a ** (weakenThenProp p) (weaken i) w' )
fai_regrwkn = ?fai_regrwkn_pr
{-

This isn't allowed

> fai_regrwkn {p} = (fai_regrwkn_chty {p=p}) . (fai_regrwkn_liftdomain {p=p})

because there are implicit arguments generated such that for example

	p i w

is of the form ((k : s) -> Type).

These are not implicit goals, so it is a failure of unification here. Perhaps we should use explicit (Sigma)s to overcome this failure of expression.

-}

fai_regrwkn_liftdomain2 : { p : {m : Nat} -> Fin (S m) -> a -> Type }
	-> ( (i : Fin (S predn))
		-> Sigma a (p $ FS i)
		-> Sigma a (p $ weaken i) )
	-> (i : Fin predn)
	-> Sigma a (p $ weaken $ FS i)
	-> Sigma a (p $ weaken $ weaken i)

{-
-- Can't do this for some reason
fai_regrwkn_chty2 : { p : {m : Nat} -> Fin (S m) -> a -> Type }
	-> ( (i : Fin predn)
		-> Sigma a (p $ weaken $ FS i)
		-> Sigma a (p $ weaken $ weaken i) )
	-> (i : Fin predn)
	-> Sigma a (weakenThenProp p $ FS i)
	-> Sigma a (weakenThenProp p $ weaken i)
-}

{-
-- In the REPL we can use a proof to force allowed use of (p . weaken).

> fai_regrwkn_chty2 : ?fai_regrwkn_chty2_ty
> fai_regrwkn_chty2_ty = proof
>   exact {a : Type} -> { p : {m : Nat} -> Fin (S m) -> a -> Type } -> {predn : Nat} -> _
>   exact _ -> _
>   exact (i : Fin predn) -> Sigma a (p $ weaken $ FS i) -> Sigma a (p $ weaken $ weaken i)
>   exact (i : Fin predn) -> Sigma a _ -> Sigma a _
>   exact (p . weaken) $ FS i
>   exact (p . weaken) $ weaken i

but loaded from module, we get this error:

Universe inconsistency.
        Working on: p10
        Old domain: (1,10)
        New domain: (1,0)
        Involved constraints: 
                ConstraintFC {uconstraint = p10 <= q10, ufc = ZZGaussianElimination.idr:151:22}
                ConstraintFC {uconstraint = o10 < p10, ufc = ZZGaussianElimination.idr:151:22}

We also get that error when we write the simply more elaborate proof

> fai_regrwkn_chty2 : ?fai_regrwkn_chty2_ty
> fai_regrwkn_chty2_ty = proof
>   exact {a : Type} -> _
>   exact { p : {m : Nat} -> Fin (S m) -> a -> Type } -> _
>   exact {predn : Nat} -> _
>   exact _ -> _
>   exact (i : Fin predn) -> _
>   unfocus
>   exact _ -> _
>   unfocus
>   exact Sigma a (p $ weaken $ FS i)
>   exact Sigma a (p $ weaken $ weaken i)
>   exact (j : Fin predn) -> _
>   exact _ -> _
>   exact Sigma a _
>   unfocus
>   exact ( p . weaken ) $ _
>   unfocus
>   unfocus
>   exact FS j
>   exact Sigma a _
>   exact (p . weaken) $ _
>   unfocus
>   exact weaken j

and even using weakenThenProp gives the error:

> fai_regrwkn_chty2 : ?fai_regrwkn_chty2_ty
> fai_regrwkn_chty2_ty = proof
>   exact {a : Type} -> { p : {m : Nat} -> Fin (S m) -> a -> Type } -> {predn : Nat} -> _
>   exact _ -> _
>   exact (i : Fin predn) -> Sigma a (p $ weaken $ FS i) -> Sigma a (p $ weaken $ weaken i)
>   exact (i : Fin predn) -> Sigma a _ -> Sigma a _
>   exact (weakenThenProp p) $ FS i
>   exact (weakenThenProp p) $ weaken i

This variant makes me suspect the problem is with having (p) take an implicit argument at all.

> fai_regrwkn_chty2 : ?fai_regrwkn_chty2_ty
> fai_regrwkn_chty2_ty = proof
>   exact {a : Type} -> { p : {m : Nat} -> Fin (S m) -> a -> Type } -> {predn : Nat} -> _
>   exact _ -> _
>   exact (i : Fin predn) -> Sigma a (p $ weaken $ FS i) -> Sigma a (p $ weaken $ weaken i)
>   exact (j : Fin predn) -> Sigma a _ -> Sigma a _
>   exact _ $ weaken $ FS j
>   exact _ $ weaken $ weaken j
>   intro j'
>   intro w
>   exact p j' w
>   intro j'
>   intro w
>   let comment1 = "You cannot write `exact p {m=S $ S $ predn} j' w` here - it won't let the implicit argument be specified."
>   let comment2 = "\"No such variable m\" from: let p' = \\mu => p {m=mu}"
>   exact p j' w
-}

{-
Sigma types also clarify what the failure is when processing (p . weaken).

> fai_regrwkn_chty2 : { p : {m : Nat} -> Fin (S m) -> a -> Type }
> 	-> ( (i : Fin predn)
> 		-> Sigma a (p $ weaken $ FS i)
> 		-> Sigma a (p $ weaken $ weaken i) )
> 	-> (i : Fin predn)
> 	-> Sigma a (((p {m=_}) . weaken) $ FS i)
> 	-> Sigma a (((p {m=_}) . weaken) $ weaken i)

When checking an application of function Prelude.Basics..:
        Type mismatch between
                {m : Prelude.Nat.Nat} -> Data.Fin.Fin (Prelude.Nat.S m) ->
                a -> Type (Type of p)
        and
                b -> a -> Type (Expected type)
        
        Specifically:
                Type mismatch between
                        a -> Type
                and
                        Type

> fai_regrwkn_chty2 : { p : {m : Nat} -> Fin (S m) -> a -> Type }
> 	-> ( (i : Fin predn)
> 		-> Sigma a (p $ weaken $ FS i)
> 		-> Sigma a (p $ weaken $ weaken i) )
> 	-> (i : Fin predn)
> 	-> Sigma a (((p {m=_}) . weaken) $ FS i)
> 	-> Sigma a (((p {m=_}) . weaken) $ weaken i)

When checking an application of function Prelude.Basics..:
        Type mismatch between
                a -> Type (Type of p m _)
        and
                b -> a -> Type (Expected type)
        
        Specifically:
                Type mismatch between
                        Type
                and
                        a -> Type

-}

fai_regrwkn_chty2 : { p : (m : Nat) -> Fin (S m) -> a -> Type }
	-> ( (i : Fin predn)
		-> Sigma a (p _ $ weaken $ FS i)
		-> Sigma a (p _ $ weaken $ weaken i) )
	-> (i : Fin predn)
	-> Sigma a (((p _) . weaken) $ FS i)
	-> Sigma a (((p _) . weaken) $ weaken i)

-- We won't compose through fai_regrwkn_chty2 and fai_regrwkn_liftdomain2 this time.
fai_regrwkn2 : ( p : (m : Nat) -> Fin (S m) -> a -> Type )
	-> ( (i : Fin (S predn))
		-> ( w : a ** p _ (FS i) w )
		-> ( w' : a ** p _ (weaken i) w' ) )
	-> (i : Fin predn)
	-> ( w : a ** ((p _) . weaken) (FS i) w )
	-> ( w' : a ** ((p _) . weaken) (weaken i) w' )
-- can't be written as `(fn . weaken) i`, nor can `i` be dropped as an argument.
fai_regrwkn2 p fn i = fn (weaken i)



||| A vector fold over suppressed indices
||| Best used with those `p` which are trivial for (last) and some (a).
foldAutoind : ( p : {m : Nat} -> Fin (S m) -> a -> Type )
	-> ( (i : Fin predn)
		-> ( w : a ** p (FS i) w )
		-> ( w' : a ** p (weaken i) w' ) )
	-> ( v : a ** p (last {n=predn}) v )
	-> ( xs : Vect (S predn) a ** (i : Fin (S predn)) -> p i (index i xs) )
{-
foldAutoind {predn=Z} p regr (v ** pv) = ( [v] ** \i => rewrite sym (the (FZ = i) $ sym $ FinSZAreFZ i) in pv )
foldAutoind {predn=S prededn} p regr (v ** pv) with (regr (last {n=prededn}) (v ** pv))
{-
Bizarrely, this interprets filling in the impl. arg to (p) as filling in its (Fin (S m)) arg.
-}
	| (v' ** pv') with ( foldAutoind {predn=prededn} (p . weaken) (fai_regrwkn2 (\mu => p {m=mu}) regr) (v' ** pv') )
-- 	| (v' ** pv') with ( foldAutoind {predn=prededn} (p . weaken) (fai_regrwkn {p=p} regr) (v' ** pv') )
-- 	| (v' ** pv') with ( foldAutoind {predn=prededn} (p . weaken) (regr' p regr) (v' ** pv') )
		| (xs ** fn) = ?faiNew
		-- | ( xs ** fn ) = ( xs++[v] ** ?foldAutoind_rhs_2 )

-- regr' = \i => \par => rewrite sym (commuteFSWeaken i) in (regr (weaken i) par)
-- : the ( (p . weaken) t s = p (weaken t) s ) Refl
-}

{-
regr_alter1 : (i : Fin prededn) -> ( w : a ** p (FS $ weaken i) w ) -> ( w' : a ** p (weaken $ weaken i) w' ) )
regr_alter1 = regr . weaken
regr_alter2 : (i : Fin prededn) -> ( w : a ** p (weaken $ FS i) w ) -> ( w' : a ** p (weaken $ weaken i) w' ) )
regr_alter2 i = rewrite sym (commuteFSWeaken i) in (regr_alter1 i)
regr_alter2' i = rewrite sym (commuteFSWeaken i) in (regr . weaken) i
-}

{-
faiNew = proof
  intros
  claim xsLong Vect (S (S prededn)) a
  rewrite sym (the (S (S prededn) = (S prededn) + 1) _)
  unfocus
  unfocus
  exact (xsLong ** _)
  compute
  refine cong
  exact trans _ $ plusSuccRightSucc prededn Z
  exact xs++[v]
  unfocus
  exact cong {f=S} $ sym $ plusZeroRightNeutral _
  intro
  claim extendPredDom {n : Nat} -> (q : Fin (S n) -> a -> Type) -> ((i : Fin n) -> ( v : a ** q (weaken i) v )) -> (v ** q last v) -> (j : Fin (S n)) -> (v ** q j v)
  unfocus
  let nearp = "extendPredDom (\fi : Fin (S (S prededn)) => p fi) _ (v ** pv) i14"
  let nearpFnGoal = "(i : Fin (S prededn)) -> (v1 : a ** p {m=S prededn} (weaken i) v1)"
  exact believe_me nearp
  intros
  exact believe_me "Didn't rename (v) in the codomain type, so this can't be implemented."
-}



||| A vector fold over suppressed indices
||| Best used with those `p` which are trivial for (last) and some (a).
foldAutoind2 : ( p : (m : Nat) -> Fin (S m) -> a -> Type )
	-> ( (i : Fin predn)
		-> ( w : a ** p _ (FS i) w )
		-> ( w' : a ** p _ (weaken i) w' ) )
	-> ( v : a ** p _ (last {n=predn}) v )
	-> ( xs : Vect (S predn) a ** (i : Fin (S predn)) -> p _ i (index i xs) )
foldAutoind2 {predn=Z} p regr (v ** pv) = ( [v] ** \i => rewrite sym (the (FZ = i) $ sym $ FinSZAreFZ i) in pv )
foldAutoind2 {predn=S prededn} p regr (v ** pv) with (regr (last {n=prededn}) (v ** pv))
	| (v' ** pv') with ( foldAutoind2 {predn=prededn} (\mu => (p $ S mu) . weaken) (fai_regrwkn2 p regr) (v' ** pv') )
		| (xs ** fn) = ?faiNew2
		-- | ( xs ** fn ) = ( xs++[v] ** _ )

faiNew2 = proof
  intros
  exact (appendedSingletonAsSuccVect xs v ** _)
  intro i
  claim ifLastThenProved (i=last) -> p (S prededn) i (index i $ appendedSingletonAsSuccVect xs v)
  unfocus
  claim ifWeakenedThenProved (j : Fin (S prededn) ** i = weaken j) -> p (S prededn) i (index i $ appendedSingletonAsSuccVect xs v)
  unfocus
  let iAsEither = splitFinS i
  exact either ifWeakenedThenProved ifLastThenProved iAsEither
  intro prIsLast
  rewrite sym prIsLast
  exact rewrite (lastInd {xs=xs} {v=v}) in pv
  intro parIsWeakened
  let prIsWeakened = getProof parIsWeakened
  rewrite sym prIsWeakened
  exact rewrite (weakenedInd {xs=xs} {v=v} {k=getWitness parIsWeakened}) in fn (getWitness parIsWeakened)



||| A vector fold over suppressed indices
||| The sequel to foldAutoind2
{-
(a : Nat -> Type) is not made implicit because Idris isn't likely to deduce it and will likely spend a long time trying anyway.
-}
foldAutoind3 : ( a : Nat -> Type )
	-> ( p : (m : Nat) -> Fin (S m) -> (a m) -> Type )
	-> ( (i : Fin predn)
		-> ( w : a predn ** p _ (FS i) w )
		-> ( w' : a predn ** p _ (weaken i) w' ) )
	-> ( v : a predn ** p _ (last {n=predn}) v )
	-> ( xs : Vect (S predn) (a predn) ** (i : Fin (S predn)) -> p _ i (index i xs) )



{-
Properties of vectors and matrices.
-}



downAndNotRightOfEntryImpliesZ : (xs : Matrix n m ZZ) -> (row : Fin n) -> (col : Fin m) -> Type
downAndNotRightOfEntryImpliesZ xs nel mel {n} {m} = {i : Fin n} -> {j : Fin m} -> (finToNat nel `LTRel` finToNat i) -> (finToNat j `LTERel` finToNat mel) -> indices i j xs = Pos Z
{-
Equivalent properties:
1) map (take mel) (drop nel xs) = neutral
2) (nel `LT` i) -> (j `LTE` mel) -> indices i j xs = Pos Z
	# In pseudocode, because we decided not to use direct LT and LTE of Fins.
-}

leadingNonzero : (v : Vect n ZZ) -> Type
leadingNonzero {n} v = Either
		(v = neutral)
		(nel : Fin n **
			( {i : Fin n}
			-> finToNat i `LTRel` finToNat nel
			-> index i v = Pos Z,
			Not (index nel v = Pos Z) )
		)

leadingNonzeroCalc : (v : Vect n ZZ) -> leadingNonzero v
leadingNonzeroCalc [] = Left Refl
leadingNonzeroCalc {n=S predn} (Pos Z::xs) with (leadingNonzeroCalc xs)
	| Left pr = Left $ cong {f=(::) $ Pos Z} pr
	| Right ( predel ** (l_fn, r_pr) ) = Right ( FS predel ** (l_fn', r_pr) )
		where
			l_fn_pr_skipup : index (FS i) (v::vs) = index i vs
			l_fn_pr_skipup = Refl
			l_fn' : {ii : Fin (S predn)}
				-> finToNat ii `LTRel` finToNat (FS predel)
				-> index ii (Pos Z::xs) = Pos Z
			l_fn' {ii=FZ} precondit = Refl
			l_fn' {ii=FS j} precondit = trans (l_fn_pr_skipup {v=Pos 0}) $ l_fn (fromLteSucc precondit)
leadingNonzeroCalc {n=S predn} (Pos (S k)::xs) = Right ( FZ ** ( void . succNotLTEzero, flip (replace {P=distinguish_Z_SZ}) () ) )
	where
		distinguish_Z_SZ : ZZ -> Type
		distinguish_Z_SZ (Pos Z) = Void
		distinguish_Z_SZ z = ()
leadingNonzeroCalc {n=S predn} (NegS k::xs) = Right ( FZ ** ( void . succNotLTEzero, flip (replace {P=distinguish_Z_SZ}) () ) )
	where
		distinguish_Z_SZ : ZZ -> Type
		distinguish_Z_SZ (Pos Z) = Void
		distinguish_Z_SZ z = ()



{-
There is a tricky part to matching on Left.

We might have this

> | Left _ = downAndNotRightOfEntryImpliesZ xs nel (last {n=predm})

but that only works if we guarantee `m` has a predecessor `predm`. Else we should use

> | Left _ = ()

So, we just simplify things and write

> | Left _ = {nelow : Fin n} -> (finToNat nel `LTRel` finToNat nelow) -> index nel xs = neutral
-}
rowEchelon : (xs : Matrix n m ZZ) -> Type
rowEchelon {n} {m} xs = (narg : Fin n) -> (ty narg)
	where
		ty : Fin n -> Type
		ty nel with (leadingNonzeroCalc $ index nel xs)
			| Right someNonZness with someNonZness
				| (leadeln ** _) = downAndNotRightOfEntryImpliesZ xs nel leadeln
			| Left _ = {nelow : Fin n} -> (finToNat nel `LTRel` finToNat nelow) -> index nel xs = neutral



{-
Intermediate or secondary algorithms
-}



-- Should be modified to account for (gcd x 0 = 0).
quotientOverZZ : ZZ -> ZZ -> Type
quotientOverZZ x y = ( d : ZZ ** d<.>y=x )

-- Making argument "k" implicit will not work.
gcdOfVectAlg : Type
gcdOfVectAlg = (k : Nat) -> (x : Vect k ZZ) -> ( v : Vect k ZZ ** ( i : Fin k ) -> (index i x) `quotientOverZZ` (v <:> x) )

-- Necessary because Idris won't unpack the definition of (gcdOfVectAlg) at occurrences.
runGCDOfVectAlg : ZZGaussianElimination.gcdOfVectAlg -> (k : Nat) -> (x : Vect k ZZ) -> ( v : Vect k ZZ ** ( i : Fin k ) -> (index i x) `quotientOverZZ` (v <:> x) )
runGCDOfVectAlg gcdalg = gcdalg

firstColZero : (xs : Matrix n m ZZ) -> Type
firstColZero [] {m} = ()	-- implicit {m} needed to match (invariantly in)/(for all) m
firstColZero ([]::xs) = ()
firstColZero ((xx::xxs)::xs) = (xx=neutral, firstColZero xs)

firstColZeroCalc : (xs : Matrix n m ZZ) -> Dec $ firstColZero xs
firstColZeroCalc [] = Yes ()
firstColZeroCalc ([]::xs) = Yes ()
firstColZeroCalc ((xx::xxs)::xs) with (firstColZeroCalc xs)
	| No pr = No ( pr . snd )
	| Yes pr with (decEq xx neutral)
		| Yes isneut = Yes (isneut, pr)
		| No nope = No ( nope . fst )

{-
elimFirstCol : (xs : Matrix n m ZZ) -> Reader ZZGaussianElimination.gcdOfVectAlg (gexs : Matrix (S n) m ZZ ** (gexs `spanslz` xs, xs `spanslz` gexs, firstColZero $ tail gexs))
{-
-- Template
elimFirstCol xs = do {
		gcdalg <- ask @{the (MonadReader gcdOfVectAlg _) %instance}
		return $ believe_me "shshs"
		-- return (?foo ** (?bar1,?bar2,?bar3))
	}
-}
-- A 0-row matrix becomes the one-neutral-row matrix
elimFirstCol [] {m} = return (row {n=m} neutral ** ( ([] ** Refl), ([neutral] ** Refl), the (firstColZero [] {m=m}) () ))
elimFirstCol ([]::xs) = ?elimFirstCol_widthZero
elimFirstCol mat {n=S predn} {m=S predm} = do {
-- elimFirstCol mat@((xx::xxs)::xs) {n=S predn} {m=S predm} = do {
		gcdalg <- ask @{the (MonadReader ZZGaussianElimination.gcdOfVectAlg _) %instance}

		{-
		Error:

		> elimFirstCol (x::xs) {m} = do {
		> 	gcdalg <- ask @{the (MonadReader gcdOfVectAlg _) %instance}
		> 	let (v ** fn) = gcdalg _ x
		>	-- which is a ( v : Vect _ ZZ ** ( i : Fin k ) -> (index i x) `quotientOverZZ` (v <:> x) )

			gcdalg does not have a function type (gcdOfVectAlg)
		-}

		-- (v ** fn) : ( v : Vect _ ZZ ** ( i : Fin _ ) -> (index i matcolZ) `quotientOverZZ` (v <:> matcolZ) )
		let (v ** fn) = runGCDOfVectAlg gcdalg _ (getCol FZ mat)

		{-
		* We want the first entry of (gexs) to be (v <:> (getCol FZ mat)), and to acquire the full vector as a linear combination of (mat) rows.
		* index FZ (r<\>m) = r<:>(index FZ $ transpose m) = r<:>(getCol FZ m)
		* to that end, we begin construction by appending (v<\>mat) to (mat).
		-}

		let bisWithGCD = the ((v<\>mat)::mat `spanslz` mat, mat `spanslz` (v<\>mat)::mat)
			(extendSpanningLZsByPreconcatTrivially {zs=[_]} spanslzrefl, mergeSpannedLZs spanslzRowTimesSelf spanslzrefl)

		{-
		* Use the properties of fn to construct mat', with bar1 and bar2 following by construction and divisibility
		-}

		{-
		This has to be commented out if you reduce mat@((xx::xxs)::xs) to mat.
		They say it's a type mismatch.

		> let mat' = mat <-> (map (\i => (v <:> (getCol FZ mat))<.>(Sigma.getWitness $ fn i) <#> (index i mat)) range)
		-}

		{-
		Typechecks, but we'll try the above for now

		> let mat' = Data.Vect.zipWith (\i => \xi => updateAt i (<-> (v <:> (getCol FZ mat))<.>(Sigma.getWitness $ fn i) <#> xi) mat) range mat
		-}

		{-
		We could just foldl with (mat ** spanslzrefl) the seed to the accumulator and accumulate by transforming the matrix to a new one and deriving a proof of its (mat) bispannability from the old proof composed with a proof the transformation preserves bispannability. Refining this fold, an accumulation of the evidence required to show that the first column becomes null below the top/gcd row of the matrix (which is invariant under the transformations).
		-}

		{-
		(foldl Iteration 1)

		This has poor qualities for applying transformations with known proofs of bispannability and composing those proofs, and it arbitrarily indirects the construction of (gexs) by accumulation through the accumulation of the tail of the (gexs) to be.

		> let foldSomefuncPreservingBispan = \f => foldl {t=Vect (S predn)} {elt=Fin (S predn)} {acc=( imat : Matrix (S predn) (S predm) ZZ ** ( (v <\> mat)::imat `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` (v <\> mat)::imat, (i : Fin (S predn) ** {j : Fin (S predn)} -> finToNat j `LTERel` finToNat i -> indices j FZ imat = Pos Z) ) )} f
		-}

		{-
		(foldl Iteration 2)

		A rough specification at least
		This has base case a once-updated version of mat,
		among other undesirable qualities.

		> let foldSomefuncPreservingBispan2 = \f => foldl {t=Vect (S predn)} {elt=Fin (S predn)} {acc=( imat : Matrix (S (S predn)) (S predm) ZZ ** ( imat `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` imat, (i : Fin (S predn) ** {j : Fin (S predn)} -> finToNat j `LTERel` finToNat i -> indices j FZ (tail imat) = Pos Z) ) )} f
		> 	( updateAt (FS FZ) (<->(?makesXXTheHeadMatHeadless<\>(deleteRow (FS FZ) (v<\>mat)::mat))) (v<\>mat)::mat ** (spanslzSubtractiveExchangeAt FS FZ,?howel,(FZ ** ?initTheFirstRowOfTailIsZero)) ) (map FS range)
		-}

		{-
		(foldl Iteration 3)
		-}

		let foldSomefuncPreservingBispan3 = \f => foldl {t=Vect (S predn)} {elt=Fin (S predn)} {acc=( imat : Matrix (S (S predn)) (S predm) ZZ ** ( imat `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` imat, (i : Fin (S (S predn)) ** (j : Fin (S predn)) -> finToNat (FS j) `LTERel` finToNat i -> indices (FS j) FZ imat = Pos Z) ) )} f
			( (v<\>mat)::mat ** (spanslzrefl,spanslzrefl,(FZ ** ?proveItAbs)) ) range
		-- proveItAbs is like \j => void . ( spawnNotLTE (finToNat (FS j)) (finToNat FZ)) )
		-- spawnNotLTE is an explicit (LTERel _ _ -> Void) to be proved, avoiding any (decLTE) (Yes/No)-case handling problems.
		-- f should take its argument (elt:=Fin (S predn)) to its successor so it can be used to index (imat), starting in its tail, and so that it will always be non-FZ and thus never using the same (Fin (S (S predn))) as the base case has.

		{-
		Can't deduce that the final bound on the known rows zero in the first column starting from the top row of (tail endmat) is actually the final row.

			"Can't match on case block in case block in elimFirstCol at [...]"

		This and the redundant information in the (range) argument suggests an even cleaner structure and closer intermediary to the goal.

		> let ( endmat ** ( endmatSpansMatandgcd, matandgcdSpansEndmat, (last {n=S predn} ** downImpliesZ) ) ) = foldSomefuncPreservingBispan3 fancy
		-}

		let ( endmat ** ( endmatSpansMatandgcd, matandgcdSpansEndmat, (finalind ** notUpImpliesZ) ) ) = foldSomefuncPreservingBispan3 fancy

		{-
		We need to show that for every row (i) of (mat), there is a vector (u) such that (u_(FS i)<\>(droprow (FS i) (v<\>mat)::mat) has the same value as row (i) of (mat) at column FZ). Especially that this property is preserved in each (imat).
		-}

		-- See comment to def of mat' for why this is commented
		-- let fstcolz_mat' = the (firstColZero mat') ?lemma_fstcolz_mat'

		-- let downImpliesZ' = ?determineFirstColZ downImpliesZ

		-- return ( (v <\> mat)::mat' ** (?bar1,?bar2,fstcolz_mat'))
		return ( endmat ** (spanslztrans endmatSpansMatandgcd $ fst bisWithGCD, spanslztrans (snd bisWithGCD) matandgcdSpansEndmat, ?downImpliesZ'))
	}
	where
		extendedFunc : {imat : Matrix (S (S predn)) (S predm) ZZ}
			-> (sfi : Fin (S (S predn)))
			-> ( (j : Fin (S predn)) -> finToNat (FS j) `LTERel` finToNat i -> indices (FS j) FZ imat = Pos Z )
			-> (j : Fin (S predn))
			-> finToNat (FS j) `LTERel` finToNat sfi
			-> indices (FS j) FZ imat = Pos Z
		fancy : {v : Vect (S predn) ZZ} -> ( imat : Matrix (S (S predn)) (S predm) ZZ ** ( imat `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` imat, (i : Fin (S (S predn)) ** (j : Fin (S predn)) -> finToNat (FS j) `LTERel` finToNat i -> indices (FS j) FZ imat = Pos Z) ) )
			-> (fi : Fin (S predn))
			-> ( imat' : Matrix (S (S predn)) (S predm) ZZ ** ( imat' `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` imat', (i' : Fin (S (S predn)) ** (j : Fin (S predn)) -> finToNat (FS j) `LTERel` finToNat i' -> indices (FS j) FZ imat' = Pos Z) ) )
		fancy ( imat ** (imatSpansMatandgcd, matandgcdSpansImat, (i ** downImpl)) ) fi = ( updateAt
				(FS fi)
				(<->(?makesXXTheHeadMatHeadless<\>(deleteRow (FS fi) imat)))
				imat
			** (spanslztrans (spanslzSubtractiveExchangeAt $ FS fi) imatSpansMatandgcd,
				spanslztrans matandgcdSpansImat (spanslzSubtractivePreservationAt $ FS fi),
				(FS fi ** extendedFunc (FS fi) downImpl)
			) )
-}



succImplWknProp : {omat : Matrix onnom (S predm) ZZ} -> (nu : Nat) -> (fi : Fin (S nu)) -> Matrix (S nu) (S predm) ZZ -> Type
succImplWknProp {omat} nu fi tmat = ( tmat `spanslz` omat, omat `spanslz` tmat, downAndNotRightOfEntryImpliesZ tmat fi FZ )
succImplWknPropSec3 : {omat : Matrix onnom (S predm) ZZ} -> (nu : Nat) -> (fi : Fin (S nu)) -> Matrix (S nu) (S predm) ZZ -> Type
succImplWknPropSec3 {omat} nu fi tmat = downAndNotRightOfEntryImpliesZ tmat fi FZ

{-
weakenTrivial : {omat : Matrix (S (S predn)) (S predm) ZZ} -> succImplWknPropSec3 {omat=omat} (S predn) (last {n=S predn}) omat
weakenTrivial = void . notSNatLastLTEAnything
-}

weakenTrivial : {omat : Matrix (S predn) (S predm) ZZ} -> succImplWknPropSec3 {omat=omat} predn (last {n=predn}) omat
weakenTrivial = void . notSNatLastLTEAnything

{-
Better to refine this to a type that depends on (m=S predm) so that the case (m=Z) may also be covered.

Shall start from the bottom of the matrix (last) and work up to row (FS FZ) using a traversal based on (weaken) and a binary map from index (Fin n) and oldvals to newvals.
-}

elimFirstCol2 : (xs : Matrix n (S predm) ZZ) -> Reader ZZGaussianElimination.gcdOfVectAlg (gexs : Matrix (S n) (S predm) ZZ ** (gexs `spanslz` xs, xs `spanslz` gexs, downAndNotRightOfEntryImpliesZ gexs FZ FZ))
{-
-- Template

elimFirstCol2 xs = do {
		gcdalg <- ask @{the (MonadReader ZZGaussianElimination.gcdOfVectAlg _) %instance}
		return $ believe_me "Weiell"
	}
-}

elimFirstCol2 [] {predm} = return ( row {n=S predm} $ neutral ** ( ([] ** Refl), ([neutral] ** Refl), nosuch ) )
	where
		nosuch : LTRel Z (finToNat i)
			-> LTERel (finToNat j) Z
			-> indices i j (row {n=S predm} Prelude.Algebra.neutral) = Pos 0
		nosuch {i=FZ} {j=FZ} _ = either (const Refl) (const Refl)
		nosuch {i=FS k} {j=FZ} _ = absurd k
		nosuch {j=FS k} _ = void . ( either succNotLTEzero SIsNotZ )
{-
elimFirstCol2 mat {n=S predn} {predm} = do {
		gcdalg <- ask @{the (MonadReader ZZGaussianElimination.gcdOfVectAlg _) %instance}

		-- (v ** fn) : ( v : Vect _ ZZ ** ( i : Fin _ ) -> (index i matcolZ) `quotientOverZZ` (v <:> matcolZ) )
		let (v ** fn) = runGCDOfVectAlg gcdalg _ (getCol FZ mat)

		let bisWithGCD = the ((v<\>mat)::mat `spanslz` mat, mat `spanslz` (v<\>mat)::mat)
			(extendSpanningLZsByPreconcatTrivially {zs=[_]} spanslzrefl, mergeSpannedLZs spanslzRowTimesSelf spanslzrefl)

		{-
		The error here is indecipherable from the message. See the form below for an improvement.
		---
		let ( endmat ** endmatPropFn ) = foldAutoind2 (succImplWknProp {omat=(v <\> mat)::mat}) (succImplWknStep {v=v}) ( (v<\>mat)::mat ** (spanslzrefl, spanslzrefl, the ( downAndNotRightOfEntryImpliesZ ((v<\>mat)::mat) (last {n=predn}) FZ ) $ void . notSNatLastLTEAnything) )
		
		---
		Here it's basically telling us it can't infer a function type for succImplWknProp _ _ _.
		---
		let ( endmat ** endmatPropFn ) = foldAutoind2 (succImplWknProp {omat=(v <\> mat)::mat}) (succImplWknStep {v=v}) ( (v<\>mat)::mat ** (spanslzrefl, spanslzrefl, the ( succImplWknProp {omat=(v<\>mat)::mat} (S predn) (last {n=predn}) ((v<\>mat)::mat) ) ( void . notSNatLastLTEAnything )) )
		
		---
		After much externalization for error isolation
		---
		let ( endmat ** endmatPropFn ) = foldAutoind2 (succImplWknProp {omat=(v <\> mat)::mat}) (succImplWknStep {v=v}) ( (v<\>mat)::mat ** (spanslzrefl, spanslzrefl, weakenTrivial {omat=(v <\> mat)::mat}) )
		-}

		let ( endmat ** endmatPropFn ) = foldedFully {v=v}

		let ( endmatSpansMatandgcd, matandgcdSpansEndmat, leftColZBelow ) = endmatPropFn FZ

		return ( index FZ endmat ** (spanslztrans endmatSpansMatandgcd $ fst bisWithGCD, spanslztrans (snd bisWithGCD) matandgcdSpansEndmat, leftColZBelow))
	}
	where
		succImplWknStep : {v : Vect (S predn) ZZ}
			-> (fi : Fin nu)
			-> ( imat : Matrix (S nu) (S predm) ZZ ** ( imat `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` imat, downAndNotRightOfEntryImpliesZ imat' (FS fi) FZ ) )
			-> ( imat' : Matrix (S nu) (S predm) ZZ ** ( imat' `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` imat', downAndNotRightOfEntryImpliesZ imat' (weaken fi) FZ ) )
		foldedFully : {v : Vect (S predn) ZZ} -> ( mats : Vect (S (S predn)) $ Matrix (S (S predn)) (S predm) ZZ ** (i : Fin (S (S predn))) -> succImplWknProp {omat=(v<\>mat)::mat} (S predn) i (index i mats) )
		-- foldedFully {v} = foldAutoind2 (succImplWknProp {omat=(v <\> mat)::mat}) (succImplWknStep {v=v}) ( (v<\>mat)::mat ** (spanslzrefl, spanslzrefl, weakenTrivial {omat=(v <\> mat)::mat}) )
-}
elimFirstCol2 mat {n=S predn} {predm} = do {
		gcdalg <- ask @{the (MonadReader ZZGaussianElimination.gcdOfVectAlg _) %instance}

		-- (v ** fn) : ( v : Vect _ ZZ ** ( i : Fin _ ) -> (index i matcolZ) `quotientOverZZ` (v <:> matcolZ) )
		let (v ** fn) = runGCDOfVectAlg gcdalg _ (getCol FZ mat)

		let bisWithGCD = the ((v<\>mat)::mat `spanslz` mat, mat `spanslz` (v<\>mat)::mat)
			(extendSpanningLZsByPreconcatTrivially {zs=[_]} spanslzrefl, mergeSpannedLZs spanslzRowTimesSelf spanslzrefl)

		{-
		The error here is indecipherable from the message. See the form below for an improvement.
		---
		let ( endmat ** endmatPropFn ) = foldAutoind2 (succImplWknProp {omat=(v <\> mat)::mat}) (succImplWknStep {v=v}) ( (v<\>mat)::mat ** (spanslzrefl, spanslzrefl, the ( downAndNotRightOfEntryImpliesZ ((v<\>mat)::mat) (last {n=predn}) FZ ) $ void . notSNatLastLTEAnything) )
		
		---
		Here it's basically telling us it can't infer a function type for succImplWknProp _ _ _.
		---
		let ( endmat ** endmatPropFn ) = foldAutoind2 (succImplWknProp {omat=(v <\> mat)::mat}) (succImplWknStep {v=v}) ( (v<\>mat)::mat ** (spanslzrefl, spanslzrefl, the ( succImplWknProp {omat=(v<\>mat)::mat} (S predn) (last {n=predn}) ((v<\>mat)::mat) ) ( void . notSNatLastLTEAnything )) )
		
		---
		After much externalization for error isolation
		---
		let ( endmat ** endmatPropFn ) = foldAutoind2 (succImplWknProp {omat=(v <\> mat)::mat}) (succImplWknStep {v=v}) ( (v<\>mat)::mat ** (spanslzrefl, spanslzrefl, weakenTrivial {omat=(v <\> mat)::mat}) )
		-}

		let ( endmat ** endmatPropFn ) = foldedFully {v=v}

		let ( endmatSpansMatandgcd, matandgcdSpansEndmat, leftColZBelow ) = endmatPropFn FZ

		return ( index FZ endmat ** (spanslztrans endmatSpansMatandgcd $ fst bisWithGCD, spanslztrans (snd bisWithGCD) matandgcdSpansEndmat, leftColZBelow))
	}
	where
		succImplWknStep : {v : Vect (S predn) ZZ}
			-> (fi : Fin (S predn))
			-> ( imat : Matrix (S (S predn)) (S predm) ZZ ** ( imat `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` imat, downAndNotRightOfEntryImpliesZ imat (FS fi) FZ ) )
			-> ( imat' : Matrix (S (S predn)) (S predm) ZZ ** ( imat' `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` imat', downAndNotRightOfEntryImpliesZ imat' (weaken fi) FZ ) )
		foldedFully : {v : Vect (S predn) ZZ} -> ( mats : Vect (S (S predn)) $ Matrix (S (S predn)) (S predm) ZZ ** (i : Fin (S (S predn))) -> succImplWknProp {omat=(v<\>mat)::mat} (S predn) i (index i mats) )
		{-
		Type mismatch between
		        Vect (S predn) ZZ (Type of v)
		and
		        Vect (S predm) ZZ (Expected type)

		Specifically:
		        Type mismatch between
		                predn
		        and
		                predm

		> foldedFully {v} = foldAutoind3 {predn=S predn} (\ne => Matrix (S ne) (S predm) ZZ) (succImplWknProp {omat=(v <\> mat)::mat}) (succImplWknStep {v=v}) ( (v<\>mat)::mat ** (spanslzrefl, spanslzrefl, weakenTrivial {omat=(v <\> mat)::mat}) )

		similarly for

		> foldedFully {v} with ( succImplWknStep {v=v} )
		> 	| fonc = ?foldedFully_pr

		or (what you'd actually have to write)

		> foldedFully {v} = let fonc = succImplWknStep {v=v} in ?foldedFully_pr

		but then we can change the error with

		foldedFully {v} with ( succImplWknStep )
			| fonc = ?foldedFully_pr

		to see the type of (mat) is mismatching an expected type the transpose.

		First error was here:
		
		> succImplWknStep : {v : Vect (S predn) ZZ}
		> 	-> (fi : Fin (S predn))
		> 	-> ( imat : Matrix (S (S predn)) (S predm) ZZ ** ( imat `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` imat, downAndNotRightOfEntryImpliesZ imat' (FS fi) FZ ) )
		> 	-> ( imat' : Matrix (S (S predn)) (S predm) ZZ ** ( imat' `spanslz` (v <\> mat)::mat, (v <\> mat)::mat `spanslz` imat', downAndNotRightOfEntryImpliesZ imat' (weaken fi) FZ ) )

		where on the third line at the very end, (imat') is referenced but doesn't exist yet.
		-}
		foldedFully {v} = foldAutoind3 {predn=S predn} (\ne => Matrix (S ne) (S predm) ZZ) (succImplWknProp {omat=(v <\> mat)::mat}) (succImplWknStep {v=v}) ( (v<\>mat)::mat ** (spanslzrefl, spanslzrefl, weakenTrivial {omat=(v <\> mat)::mat}) )

{-
Reference
-----
gcdOfVectAlg = (k : Nat) -> (x : Vect k ZZ) -> ( v : Vect k ZZ ** ( i : Fin k ) -> (index i x) `quotientOverZZ` (v <:> x) )
-}

gaussElimlzIfGCD : Reader gcdOfVectAlg ( (xs : Matrix n m ZZ) -> (gexs : Matrix n' m ZZ ** (gexs `spanslz` xs, xs `spanslz` gexs, rowEchelon gexs)) )
-- gaussElimlzIfGCD2 : (xs : Matrix n m ZZ) -> Reader gcdOfVectAlg (gexs : Matrix n' m ZZ ** (gexs `spanslz` xs, xs `spanslz` gexs, rowEchelon gexs))



{-
Background info
-}



gcdOfVectZZ : (x : Vect n ZZ) -> ( v : Vect n ZZ ** ( i : Fin n ) -> (index i x) `quotientOverZZ` (v <:> x) )



{-
Main algorithm
-}



gaussElimlz : (xs : Matrix n m ZZ) -> (gexs : Matrix n' m ZZ ** (gexs `spanslz` xs, xs `spanslz` gexs, rowEchelon gexs))
gaussElimlz = runIdentity $ runReaderT gaussElimlzIfGCD (\k => gcdOfVectZZ {n=k})
-- Why is this wrong, for if we put the argument inside the ReaderT gaussElimlzIfGCD?
-- gaussElimlz = runIdentity . ((flip runReaderT) $ (\k => gcdOfVectZZ {n=k})) . gaussElimlzIfGCD2
