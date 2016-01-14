module GaussianElimination

import Data.Vect

{-

NOTES



Though the assumptions seem so obvious you shouldn't have to prove them,
either they're wrong together or Idris is very broken, because we've
proven (6 = 2) by proving (a, b)===(0, 1) satisfies a*4+b*6 = gcd 4 6.
I suspect the error is `subtractionexchangepr` and subtraction of Nats
is broken, but it could also be `gcddef`, which shows up in the
expression for the proof of this fact a few times (and shows up
in the correct computations we've seen as well).

Further, the linear combination can't be right, because the only solutions
have negative coefficients in them.

Oh! No, it's clearly modeqpr that's wrong. It assumes (+k).(-k) = id.
But subtractionexchangepr might still be wrong for the same reason.

===========================================

TODO



Prove bezoutsIdentityNat rigorously and over ZZ. Find the contradiction

	> bezoutsIdentityNat 4 6

is false while

	> bezoutsIdentityNat 4 2

is true.

But we CAN'T just do it over ZZ, because `gcd` is not defined for it (what??).
We need to use Int or Integral or (Integral a, Quasigroup a) => a, but be warned
this algorithm will still fail if the number system has Integral instantiated but
it is not either one of those two or a Euclidean domain.

	Prelude.Nat.toIntNat : Nat -> Int
	Tail recursive cast Nat to Int Note that this can overflow

	Prelude.Nat.toIntegerNat : Nat -> Integer
	Convert a Nat to an Integer

So we want to use Integer instead of Int.

	Prelude.Nat.fromIntegerNat : Integer -> Nat
	Convert an Integer to a Nat, mapping negative numbers to 0

We can use this to build a nice `abs`.



Remove gcddef by proving this trivial lemma



Remove junk from lemma_gcdrecpr by inspecting the proof
See if it can't be done in a more uniform style
 style 1a) more letting things be the Refl ComputableThm
 style 1b) more claims of equalities combined combinatorially
 style 2) more functional, creating intermediate assumptions by applying
 	Clearly gluemap is the wrong kind of function.
 	On the other hand, we described how to express the proof maneuvers as plumbing.
 	Maybe we could extend the plumbing to where we don't need some of the proof hints,
 	say by replacing the value whose equal expression needs to be hinted at being
 	wrapped in a function definition with a relative derivation by some other function
 	that rewrite w/ cong will be happy to recognize, such as so factorizing the thm at claim.



Expressions of the plumbing being performed that are more generally are desired



Perhaps we should call what we're proving now the Euclidean division algorithm,
and call the witness-erased form, corresponding to the existential form of the
conclusion, the true Bezout's theorem.
> :apropos Exists



Refactor into modules based on independence of origins.

===========================================

IMPACT OF LANGUAGE GAPS ON CODE



Here's some semantics errors within rewrite, possibly due to misscoping.
This was found in lemma_gcdrecpr, right where ?subtractionexchange is made.

> rewrite sym ( ( the ( (a : Nat) -> (b : Nat) -> (c : Nat) -> (a-b)+c = a+(c-b) ) ?subtractionexchange ) $ ( a*d ) $ ( (b*(div (c-r) d))*d ) $ ( b*c ) )
	Error: Perhaps a is applied to too many arguments
> rewrite sym ( ( the ( (x : Nat) -> (y : Nat) -> (z : Nat) -> (x-y)+z = x+(z-y) ) ?subtractionexchange ) ( a*d ) ( (b*(div (c-r) d))*d ) ( b*c ) )
	Error: No such variable x



Some things can't be made private even though they shouldn't be used outside this module,
because doing so will change how things in this module that use them typecheck, creating
a bug which allows a using function's type to be checked but appears undeclared when called.
This was found by making gcdwzeroproof private and checking the type of bezoutsIdentityNat 1.

Making gcdwzeroproof private also prevents gcdnormally=?gcdnormallyproof from being able to access
all the variables from the environment that are involved.



It would be nice if we knew how to use a proof of equality of types to refine a goal.
Maybe it would use refine.
We need to prove the type of the goal matches what we have,
not that we have a value of the goal type.

Then we could replace (bezeqty c d nn) with
	let (a,b)=nn in a*c+b*d = gcd c d
or	(\(a,b) => a*c+b*d = gcd c d) nn

-}



gcdwzeroproof : (cc : Nat) -> plus (plus cc 0) 0 = cc
gcdwzeroproof = proof
	intro
	rewrite sym (plusCommutative cc 0)
	rewrite sym (plusCommutative cc 0)
	trivial

gcddef : (a : Nat) -> (b : Nat) -> ( gcd a b = assert_total (gcd b (modNat a b)) )
-- Type mismatch on the equality, even though the things are equal by def.
-- gcddef a b = Refl
gcddef a b = believe_me "by definition"

{-

Proof sketch
In this style, some of the arrows are tautological from prior knowledge
If the use of `r` for `modNat c d` til the conclusion were followed,
the actual proof would be easier to follow and more elegantly written.

lemma_gcdrec : (c : Nat) -> (d : Nat) -> (r : Nat) -> (a : Nat) -> (b : Nat)
	-> (r = modNat c d)
	-> (a*d+b*r = gcd d r)
	-> ( gcd d r = gcd c d ) --by def of gcd
	-> ( a*d + b*r = gcd c d ) -- by subst b-n previous two

	-> ( r+(div (c-r) d)d = c ) -- Solution exists by lifting r over multiples of d to c. Namely, d | c-r.
	-> ( r = c-(div (c-r) d)d ) -- by cong on subtraction
	-> ( (a*d + b*(c-(div (c-r) d)*d)) = gcd c d ) -- by subst b-n prev 3
	-> ( ((a-b*(div (c-r) d))*d + b*c) = gcd c d ) -- by distrib then assoc then distrib

-}



lemma_gcdrec : (c : Nat) -> (d : Nat) -> (a : Nat) -> (b : Nat)
	-> ( gcdformknown : a*d+b*(modNat c d) = gcd d (modNat c d))
	-> ( ((a-b*(div (c-(modNat c d)) d))*d + b*c) = gcd c d )
lemma_gcdrec = ?lemma_gcdrecpr

-- A bunch of this is junk. If we try again, we can cut that out.
lemma_gcdrecpr = proof
  intros
  claim lincombformknown ( a*d+b*(modNat c d) = gcd c d )
  unfocus
  claim modeq ( modNat c d = c-(div (c-(modNat c d)) d)*d )
  unfocus
  claim substform ( ((a-b*(div (c-(modNat c d)) d))*d + b*c) = gcd c d )
  unfocus
  rewrite sym ( multDistributesOverMinusLeft a (b*(div (c-(modNat c d)) d)) d )
  claim subtractionexchange (x : Nat) -> (y : Nat) -> (z : Nat) -> plus (minus x y) z = plus x (minus z y)
  unfocus
  rewrite sym ( subtractionexchange (a*d) ( (b*(div (c-(modNat c d)) d))*d ) ( b*c ) )
  rewrite sym (sym $ multAssociative b (div (c-(modNat c d)) d) d)
  rewrite sym (sym $ multDistributesOverMinusRight b c ((div (c-(modNat c d)) d)*d))
  claim substform' ( (a*d + b*(c-(div (c-(modNat c d)) d)*d)) = gcd c d )
  unfocus
  exact substform'
  rewrite sym (gcddef c d)
  exact gcdformknown
  unfocus
  exact (believe_me "Rm this junk")
  exact ?subtractionexchangepr
  rewrite sym (gcddef c d)
  -- rewrite sym (sym modeq) is no-opping, but should solve the main thm
  --    REDO: Maybe we just need to use compute to normalize the goal terms beforehand?
  -- So, we have to add hints, namely factoring through what we call
  -- reachfortheglue and applying cong and trans.
  -- The type of such a maneuver is roughly {a : A} -> {b : A} -> {c : B} -> (a = b) -> { f : A -> B } -> ( f b = c ) -> ( f a = c )
  -- This gluemap map is junk we recreate later.
  claim gluemap ( gf : plus (mult a d) (mult b (modNat c d)) = gcd d (modNat c d) ) -> ( me : modNat c d = c - div (c - modNat c d) d * d ) -> a * d + b * (c - div (c - modNat c d) d * d) = gcd d (modNat c d)
  intros
  let reachfortheglue = \v => plus (mult a d) (mult b v)
  let rftgv = cong {f=reachfortheglue} me
  let fv = the ( reachfortheglue ( c - div (c - modNat c d) d * d ) = plus (mult a d) (mult b $ c - div (c - modNat c d) d * d) ) Refl
  let t_rftgv_fv = trans rftgv fv
  let t_trftgvfg_gf = trans (sym t_rftgv_fv) gf
  exact t_trftgvfg_gf
  let reachfortheglue = \v => plus (mult a d) (mult b v)
  let rftgv = cong {f=reachfortheglue} modeq
  let fv = the ( reachfortheglue ( c - div (c - modNat c d) d * d ) = plus (mult a d) (mult b $ c - div (c - modNat c d) d * d) ) Refl
  let t_rftgv_fv = trans rftgv fv
  let t_trftgvfg_gf = trans (sym t_rftgv_fv) gcdformknown
  exact t_trftgvfg_gf
  exact (?modeqpr c d)



total
bezeqty : Nat -> Nat -> (Nat,Nat) -> Type
bezeqty c d (a,b) = a*c+b*d = gcd c d

lemma_gcdrecdepparout : (c : Nat) -> (d : Nat) -> (a : Nat) -> (b : Nat)
	-> ( gcdformknown : bezeqty d (modNat c d) (a,b))
	-> ( nn:(Nat,Nat) ** bezeqty c d nn )
lemma_gcdrecdepparout = ?lemma_gcdrecdepparoutpr

lemma_gcdrecdepparoutpr = proof
  intros
  claim imedeq ( b*c + (a-b*(div (c-(modNat c d)) d))*d = gcd c d )
  unfocus
  exact ( (b, (a - b * div (c - modNat c d) d)) ** imedeq )
  -- here we see the sum in the conclusion of lemma_gcdrec
  -- differs in term order from that needed
  rewrite sym (sym $ lemma_gcdrec c d a b gcdformknown)
  compute
  rewrite sym ( plusCommutative (mult b c) (mult (minus a (mult b (div (minus c (modNat c d)) d))) d) )
  exact Refl



bezoutsIdentityNat : (c:Nat) -> (d:Nat)
	-> ( nn : (Nat,Nat) ** bezeqty c d nn )
bezoutsIdentityNat c Z = ((1,0) ** gcdwzero)
	where
		gcdwzero = gcdwzeroproof c
bezoutsIdentityNat c d with (bezoutsIdentityNat d (modNat c d))
	| ((a,b) ** oldpr) = lemma_gcdrecdepparout c d a b oldpr
