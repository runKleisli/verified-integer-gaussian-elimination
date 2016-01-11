module GaussianElimination

import Data.Vect

{-

NOTES



===========================================

TODO

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

-}



{-
-- No lambda will do in the type of bezoutsIdentityNat
-- However, since we must still inline this calculation
-- to keep any name private, we can't use what's below.

private
smallLinCombo : Nat -> Nat -> (Nat,Nat) -> Nat
smallLinCombo x y (a,b) = x*a+y*b

-- At first, we had

bezoutsIdentityNat : (c:Nat) -> (d:Nat)
	-> ( nn : (Nat,Nat) ** (smallLinCombo c d nn = gcd c d) )

-- Originally, with that smallLinCombo function &
-- bezoutsIdentityNat type signature, we had
-- a different theorem to prove.

-- This is a sketch from that theorem.
-- You can leave these 2 proof holes (mz, mz2) and do this:

private
gcdwzeroproof : (c : Nat) -> plus (mult c 1) 0 = c
gcdwzeroproof = proof
	intro cc
	rewrite sym (the (plus (mult cc 1) 0 = mult cc 1) ?mz)
	rewrite sym (the (mult cc 1 = cc) ?mz2)
	exact Refl

-- which doesn't save you from having to apply (rewrite sym plusCommutative), but shows `the` off.

-- The actual proof of the theorem that we used is as follows

private
gcdwzeroproof : (c : Nat) -> plus (mult c 1) 0 = c
gcdwzeroproof = proof
	intro
	rewrite sym (plusCommutative (mult c 1) 0)
	rewrite sym (multCommutative c 1)
	rewrite sym (plusCommutative c 0)
	trivial
-}

{-
private
--
For some reason making this private makes bezoutsIdentityNat uncallable.
It also prevents gcdnormally=?gcdnormallyproof from being able to access
all the variables from the environment that are involved.
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

-- claim lincombformknown ( a*d+b*(modNat c d) = gcd c d )
-- rewrite sym (gcddef c d)
-- claim substform ( ((a-b*(div (c-(modNat c d)) d))*d + b*c) = gcd c d )
-- rewrite sym ( ( the ( (a : Nat) -> (b : Nat) -> (c : Nat) -> (a-b)+c = a+(c-b) ) ?subtractionexchange ) $ ( a*d ) $ ( (b*(div (c-r) d))*d ) $ ( b*c ) )
-- rewrite sym ( ( the ( (x : Nat) -> (y : Nat) -> (z : Nat) -> (x-y)+z = x+(z-y) ) ?subtractionexchange ) ( a*d ) ( (b*(div (c-r) d))*d ) ( b*c ) )
-- 	Error: No such variable x

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

%reflection
bezoutsIdentityNat : (c:Nat) -> (d:Nat)
	-> ( nn : (Nat,Nat) ** (let (a,b)=nn in a*c+b*d = gcd c d) )
bezoutsIdentityNat c Z = ((1,0) ** gcdwzero)
	where
		gcdwzero = gcdwzeroproof c
{-
bezoutsIdentityNat c d = let r = c `modNat` d in
		gcdnormally
		--gcdnormally r (bezoutsIdentityNat c r) (div (c-r) d)
	where
		gcdnormally = ?gcdnormallyproof
-}
bezoutsIdentityNat c d = ?gcdnormallyproof
