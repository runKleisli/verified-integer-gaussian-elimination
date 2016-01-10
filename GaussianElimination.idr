module GaussianElimination

import Data.Vect

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
