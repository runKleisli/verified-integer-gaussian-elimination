> module LinCombHeadtailsEq

> import Data.Matrix.LinearCombinations
> import ZZModuleSpan

> import Control.Algebra
> import Control.Algebra.VectorSpace -- definition of module
> import Classes.Verified -- definition of verified algebras other than modules
> import Data.Matrix
> import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20

> import Data.ZZ



# Contents
* Introduction
* vecSingletonReplicateEq
* reduceMultUnderHeadTo1D
* rewriteZipWithUnderTail
* References



# Introduction

Suppose we have

< vecHeadtailsEq : {xs,ys : Vect _ _} -> ( headeq : x = y ) -> ( taileq : xs = ys ) -> x::xs = y::ys

Then we can replace efforts in proofs with this expression.

These are proofs of equality of two Vects expressed in (x::xs) form, mainly inductive proofs:

< vecSingletonReplicateEq : ((u : a) -> v=u) -> (xs : Vect n a) -> (xs = replicate n v)

< reduceMultUnderHeadTo1D : {xxs : Matrix n (S m) ZZ} -> map Data.Vect.head (zipWith (<#>) (vv::vvs) (xx::xxs)) = zipWith (the (ZZ -> ZZ -> ZZ) (*)) (vv::vvs) (map Data.Vect.head (xx::xxs))
< reduceMultUnderHeadTo1D_triv
< reduceMultUnderHeadTo1D'

< rewriteZipWithUnderTail : {scals : Vect n ZZ} -> {vects : Matrix n (S predw) ZZ} -> map Data.Vect.tail $ Data.Vect.zipWith (<#>) scals vects = Data.Vect.zipWith (<#>) scals (map Data.Vect.tail vects)
< rewriteZipWithUnderTail'

# vecSingletonReplicateEq

Out of these, `vecSingletonReplicateEq` is the simplest to analyze the replacement.

Let us write

> vecSingletonReplicateEq_2 : ((u : a) -> v=u) -> (xs : Vect n a) -> (xs = replicate n v)
> vecSingletonReplicateEq_2 f [] = Refl
> vecSingletonReplicateEq_2 f (x::xs) = vecHeadtailsEq (sym $ f x) (vecSingletonReplicateEq_2 f xs)

this improves the clarity of

< vecSingletonReplicateEq : ((u : a) -> v=u) -> (xs : Vect n a) -> (xs = replicate n v)
< vecSingletonReplicateEq f [] = Refl
< vecSingletonReplicateEq f (x::xs) {v} = rewrite sym (f x) in cong {f=(v::)} (vecSingletonReplicateEq f xs)

# reduceMultUnderHeadTo1D

The ones in `reduceMultUnderHeadTo1D` are most aggregious. Let us write

> reduceMultUnderHeadTo1D_2 : {xxs : Matrix n (S m) ZZ} -> map Data.Vect.head (zipWith (<#>) (vv::vvs) (xx::xxs)) = zipWith (the (ZZ -> ZZ -> ZZ) (*)) (vv::vvs) (map Data.Vect.head (xx::xxs))
> reduceMultUnderHeadTo1D_2 {n=Z} {xxs=[]} {vvs=[]} = vecHeadtailsEq headMapChariz Refl
> reduceMultUnderHeadTo1D_2 {n=S predn} {xxs=xxx::xxxs} {vvs=vvv::vvvs} = vecHeadtailsEq headMapChariz reduceMultUnderHeadTo1D_2
> 

Note the greater improvement of the proof for the case {n=Z} by pattern matching on the variables `xxs` and `vvs` rather than applying `zeroVecEq` to prove they're both [].

Further, the corresponding finer-grained pattern matching in the longer-tailed cases eliminates the need for the second `vecHeadtailsEq` argument to be given by the proof

< mapheads_eq_zipwith = proof
<   intros
<   rewrite sym $ headtails vvs
<   rewrite sym $ headtails xxs
<   exact reduceMultUnderHeadTo1D_2 {vv=head vvs} {vvs=tail vvs} {xx=head xxs} {xxs=tail xxs}

as in

< reduceMultUnderHeadTo1D_2 {n=S predn} {vv} {xx} = vecHeadtailsEq headMapChariz ?mapheads_eq_zipwith

The original, however, is comparatively illegible

< reduceMultUnderHeadTo1D : {xxs : Matrix n (S m) ZZ} -> map Data.Vect.head (zipWith (<#>) (vv::vvs) (xx::xxs)) = zipWith (the (ZZ -> ZZ -> ZZ) (*)) (vv::vvs) (map Data.Vect.head (xx::xxs))
< reduceMultUnderHeadTo1D {n=Z} {vv} {xx} = ?reduceMultUnderHeadTo1D_triv
< reduceMultUnderHeadTo1D {n=S predn} {vv} {xx} = ?reduceMultUnderHeadTo1D'
< 
< reduceMultUnderHeadTo1D_triv = proof
<   intros
<   rewrite sym (the (xxs = []) zeroVecEq)
<   rewrite sym (the (vvs = []) zeroVecEq)
<   compute
<   exact cong {f=(::[])} _
<   exact headMapChariz {xs=xx}
< 
< reduceMultUnderHeadTo1D' = proof
<   intros
<   -- Not required in the REPL: {f=multZ vv}
<   exact trans (cong {f=(::(map head $ zipWith (<#>) vvs xxs))} $ headMapChariz {f=multZ vv} {xs=xx}) _
<   compute
<   exact cong {f=(::) (multZ vv (head xx))} _
<   rewrite sym $ headtails vvs
<   rewrite sym $ headtails xxs
<   exact reduceMultUnderHeadTo1D {vv=head vvs} {vvs=tail vvs} {xx=head xxs} {xxs=tail xxs}

# rewriteZipWithUnderTail

Finally, `rewriteZipWithUnderTail` plays a full mind game with Idris to discuss one of these problems. We may write

> rewriteZipWithUnderTail_2 : {scals : Vect n ZZ} -> {vects : Matrix n (S predw) ZZ} -> map Data.Vect.tail $ Data.Vect.zipWith (<#>) scals vects = Data.Vect.zipWith (<#>) scals (map Data.Vect.tail vects)
> rewriteZipWithUnderTail_2 {scals=[]} {vects=[]} = Refl
> rewriteZipWithUnderTail_2 {scals=z::zs} {vects=v::vs} = vecHeadtailsEq (rewrite sym $ sym $ headtails v in Refl) rewriteZipWithUnderTail_2

whereas originally we had to write

< rewriteZipWithUnderTail {scals=z::zs} {vects=v::vs} = ?rewriteZipWithUnderTail'
< 
< rewriteZipWithUnderTail' = proof
<   intros
<   let headv = map (z <.>) (tail v)
<   exact trans _ (cong {f=(headv::)} $ rewriteZipWithUnderTail {scals=zs} {vects=vs})
<   claim headeq tail (map (z<.>) v) = headv
<   compute -- reduce the headv in the proposition to its value for prepping substitution
<   unfocus
<   rewrite sym headeq
<   compute -- apply the (\x => headv::x) from the earlier cong
<   exact Refl
<   rewrite sym $ headtails v
<   exact Refl



# References

* Idris 0.9.20 src: /test/regex007/A.lidr

Notes

* Idris 0.9.20 src: /samples/misc/reflection.idr
* modules.rst
