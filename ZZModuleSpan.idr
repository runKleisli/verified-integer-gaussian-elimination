module ZZModuleSpan

import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module
import Classes.Verified -- definition of verified algebras other than modules
import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20

import Data.ZZ
import Control.Algebra.NumericInstances



monoidsum : (Foldable t, Monoid a) => t a -> a
{-
-- Idris version 0.9.18
monoidsum = Control.Algebra.sum
-}
-- Idris version 0.9.20
monoidsum = sum'
--



{-
Trivial theorems
-}

-- Eta conversion: https://github.com/idris-lang/Idris-dev/issues/2071
eta : (f : a -> b) -> f = (\c => f c)
eta f = sym Refl

etaBinary : (f : a -> b -> c) -> f = (\c => \d => f c d)



total
zeroVecEq : {a : Vect 0 r} -> {b : Vect 0 r} -> a = b
zeroVecEq {a=[]} {b=[]} = Refl



total
vecSingletonReplicateEq : ((u : a) -> v=u) -> (xs : Vect n a) -> (xs = replicate n v)
vecSingletonReplicateEq f [] = Refl
vecSingletonReplicateEq f (x::xs) {v} = rewrite sym (f x) in cong {f=(v::)} (vecSingletonReplicateEq f xs)



total
zeroVecVecId : (xs : Vect n (Vect 0 a)) -> (xs = replicate n [])
zeroVecVecId = vecSingletonReplicateEq (\b => zeroVecEq {a=[]} {b=b})



total
headMapChariz : {xs : Vect (S n) _} -> head $ map f xs = f $ head xs
headMapChariz {xs=x::xs} = Refl

mapheadrec : with Data.Vect ( map head (v::vs) = (head v) :: (map head vs) )
mapheadrec = Refl

headtails : (v : Vect (S predk) _) -> v = (head v) :: (tail v)
headtails (vv::vvs) = Refl



-- The theorem below this one should not be a necessary weakening, since the functions have equivalent definitions.
-- indexFZIshead : index FZ = Data.Vect.head

total
indexFZIsheadValued : index FZ xs = head xs
indexFZIsheadValued {xs=x :: xs} = Refl



lemma_VectAddHead : (v, w : Vect (S n) ZZ) -> head(v<+>w) = (head v)<+>(head w)
lemma_VectAddHead (vv::vvs) (ww::wws) = Refl

lemma_VectAddEntrywise : .{n : Nat} -> (ni : Fin n) -> (v, w : Vect n ZZ) -> index ni (v<+>w) = (index ni v)<+>(index ni w)
{-
-- -- This proof follows the structure of `index`'s definition
--
-- without ni arg: (.) void FinZAbsurd; >> No such variable __pi_arg7; seems a silly failure of type inference
lemma_VectAddEntrywise {n=Z} ni = void $ FinZAbsurd ni
lemma_VectAddEntrywise FZ = ?lemma_VectAddEntrywise_rhs_1
lemma_VectAddEntrywise (FS npredi) = ?lemma_VectAddEntrywise_rhs_2
lemma_VectAddEntrywise_rhs_1 = proof
  intros
  rewrite sym (indexFZIsheadValued {xs=v})
  rewrite sym (indexFZIsheadValued {xs=w})
  exact (rewrite (indexFZIsheadValued {xs=v<+>w}) in (lemma_VectAddHead v w))
lemma_VectAddEntrywise_rhs_2 = proof
	intros
	claim indpred ( (r : ZZ) -> (rs : Vect k ZZ) -> index (FS npredi) (r::rs) = index npredi rs )
	-- ^ trivial
	unfocus
	{-
	-- No-opping stuff demonstrating the problem how the thm fails
	rewrite sym ( indpred (head $ v<+>w) (tail $ v<+>w) )
	rewrite sym ( indpred (head v) (tail v) )
	rewrite sym ( indpred (head w) (tail w) )
	-}
	rewrite sym ( the (v = (head v)::(tail v)) Refl )
	>> When checking argument value to function Prelude.Basics.the:
        Unifying v and head v :: tail v would lead to infinite value
-}
-- -- Alternative proof (>points):
lemma_VectAddEntrywise {n=Z} ni v w = void $ FinZAbsurd ni
lemma_VectAddEntrywise FZ (vv::vvs) (ww::wws) = Refl
lemma_VectAddEntrywise (FS npredi) (vv::vvs) (ww::wws) = lemma_VectAddEntrywise npredi vvs wws



monoidrec1D : {v : ZZ} -> {vs : Vect n ZZ} -> monoidsum (v::vs) = v <+> monoidsum vs

-- the foldr needs to be converted to a foldl
monoidrec2D : {v : Vect m ZZ} -> {vs : Vect n (Vect m ZZ)} -> monoidsum (v::vs) = v <+> (monoidsum vs)
monoidrec2D {v} {vs=[]} = Refl
-- monoidrec {v} {vs=(vsv::vss)} = rewrite (the ( foldrImpl (<+>) neutral (v::vs) = foldrImpl (<+>) (neutral . (v <+>)) vs ) Refl) in (monoidrec {v=vsv} {vs=vss})
monoidrec2D {v} {vs=(vsv::vss)} = ?monoidrec'

total
headOfSumIsSumOfHeadsArg : ((v : Vect (S n) ZZ) ->
                    (w : Vect (S n) ZZ) -> head (v <+> w) = head v <+> head w) -> (xs : Vect (S m) (Vect (S n) ZZ)) -> head (monoidsum xs) = monoidsum (map head xs)
headOfSumIsSumOfHeadsArg {n} pr (v::[]) = rewrite sym (pr v (replicate (S n) (Pos 0))) in Refl
headOfSumIsSumOfHeadsArg {m = S m'} {n} pr (v::(vsv::vss)) = conclusion3
	where
		vs : Vect (S m') (Vect (S n) ZZ)
		vs = vsv::vss
		imedform0: monoidsum (map head (v::vs)) = monoidsum ( (head v) :: (map head vs) )
		imedform0 = cong {f=monoidsum} (mapheadrec {v=v} {vs=vs})
		recappl : monoidsum (map head (v::vs)) = head v <+> monoidsum (map head vs)
		recappl = trans imedform0 (the (monoidsum ( (head v) :: (map head vs) ) = (head v) <+> monoidsum (map head vs) ) monoidrec1D)
		imedform1 : head (monoidsum (v::vs)) = head ( v <+> monoidsum vs )
		{-
		original: imedform1 = cong {f=head} monoidrec2D
		Spurious type mismatch error results. monoidrec2D is assumed the wrong implicit args, perhaps, or else one of the foldrImpl gets one recursion rewrite instead of none.
		-}
		imedform1 = cong {f=head} (monoidrec2D {v=v} {vs=vs})
		homomorphismapply : head (monoidsum (v::vs)) = head v <+> (head (monoidsum vs))
		homomorphismapply = trans imedform1 (lemma_VectAddHead v (monoidsum vs))
		conclusion0 : (head (monoidsum (v::vs)) = head v <+> (head (monoidsum vs)), head v <+> monoidsum (map head vs) = monoidsum (map head (v::vs)))
		conclusion0 = (homomorphismapply, sym recappl)
		conclusion1 : head (monoidsum vs) = monoidsum (map head vs) -> (head (monoidsum (v::vs)) = head v <+> monoidsum (map head vs), head v <+> monoidsum (map head vs) = monoidsum (map head (v::vs)))
		conclusion1 pr = (rewrite sym pr in homomorphismapply, sym recappl)
		conclusion2 : head (monoidsum vs) = monoidsum (map head vs) -> head (monoidsum (v::vs)) = monoidsum (map head (v::vs))
		conclusion2 pr = uncurry trans (conclusion1 pr)
		-- bizarrely, this does not work
		-- conclusion2 pr = trans (rewrite sym pr in homomorphismapply) (sym recappl)
		proof0 : head (monoidsum vs) = monoidsum (map head vs)
		proof0 = headOfSumIsSumOfHeadsArg pr vs
		conclusion3 : head (monoidsum (v::vs)) = monoidsum (map head (v::vs))
		conclusion3 = conclusion2 proof0

total
headOfSumIsSumOfHeads : (xs : Vect m (Vect (S n) ZZ)) -> head (monoidsum xs) = monoidsum (map head xs)
headOfSumIsSumOfHeads {m=Z} [] = Refl
headOfSumIsSumOfHeads {m=S m} xs = headOfSumIsSumOfHeadsArg lemma_VectAddHead xs
{-
-- This should work but is picky.
headOfSumIsSumOfHeads {m=Z} xs = trans zveqpr (sym $ trans bandy bundy)
	where
		bandy : (the (Vect Z ZZ -> ZZ) monoidsum) (map head xs) = monoidsum (map head Data.Vect.Nil)
		-- bandy = trans ( sym $ trans ( cong {f=monoidsum . (map head)} (the ([]=xs) zeroVecEq) ) ( the ((monoidsum . (map head)) $ xs = monoidsum (map head xs)) Refl ) ) (the ((monoidsum . map head) [] = monoidsum (map Data.Vect.head Data.Vect.Nil)) Refl)
		bundy : monoidsum (map Data.Vect.head Data.Vect.Nil) = Pos Z
		bundy = Refl
		zveqpr : Data.Vect.head $ monoidsum xs = monoidsum (map Data.Vect.head xs)
		zveqpr = ?zveqpr'
		zveqpr' = proof
			rewrite sym (the (xs=[]) zeroVecEq)
			trivial
-}
{-
-- Works in REPL
headOfSumIsSumOfHeads {m=Z} = ?headOfSumIsSumOfHeads_Z_pr
headOfSumIsSumOfHeads_Z_pr = proof
  intros
  let bandy = trans ( sym $ trans ( cong {f=monoidsum . (map head)} (the ([]=xs) zeroVecEq) ) ( the ((monoidsum . (map head)) $ xs = monoidsum (map head xs)) Refl ) ) (the ((monoidsum . map head) [] = monoidsum (map Data.Vect.head Data.Vect.Nil)) Refl)
  unfocus
  unfocus
  unfocus
  unfocus
  unfocus
  search
  search
  search
  let bundy = the (monoidsum (map Data.Vect.head Data.Vect.Nil) = Pos Z) $ Refl
  exact trans _ (sym $ trans bandy bundy)
  unfocus
  unfocus
  rewrite sym (the (xs=[]) zeroVecEq)
  trivial
  exact n
  exact n
-}

-- Note that tailOfSumIsSumOfTails and monoidsumOverTailChariz depend on each other recursively.
-- Note the hole ?etaCon_tailsumMonrecStepExpr2' is not filled.
mutual
	tailOfSumIsSumOfTails : {vs : Matrix n (S predw) ZZ} -> tail (monoidsum vs) = monoidsum (map tail vs)
	tailOfSumIsSumOfTails {vs=[]} = Refl
-- 	tailOfSumIsSumOfTails {vs=v::vs} = ?tailOfSumIsSumOfTails'
	tailOfSumIsSumOfTails {vs=v::vs} {predw} ?= trans (cong {f=Data.Vect.tail} monoidrec2D) (tailsumMonrecStep {v=v} {vs=vs})

	{-
	-- Works in REPL but complains on loading, as usual
	tailOfSumIsSumOfTails {vs=v::vs} = ?tailOfSumIsSumOfTails'
	tailOfSumIsSumOfTails' = proof
	  intros
	  exact trans (cong {f=Data.Vect.tail} monoidrec2D) _
	  rewrite sym (headtails v)
	  rewrite sym (headtails $ monoidsum vs)
	  exact monoidsumOverTailChariz
	-}

	-- Junk from eta reductions done in REPL but not in normal type checking.
	-- Type check fails in a etaCon_tailsumMonrecStepExpr1-lvl mismatch b-n alpha-equivalent expressions.
	etaCon_tailsumMonrecStepExpr1 : {vs : Matrix n (S predw) ZZ} -> monoidsum (map tail (v :: vs)) = foldrImpl (Data.Vect.zipWith Data.ZZ.plusZ) (replicate predw (Pos 0)) (zipWith Data.ZZ.plusZ (tail v)) (map tail vs)
	etaCon_tailsumMonrecStepExpr1 {v} {vs} {predw} = trans lem2 (trans ?alphaCon_tailsumMonrecStepExpr1 lem3)
	-- etaCon_tailsumMonrecStepExpr1 {v} {vs} {predw} = ?etaCon_tailsumMonrecStepExpr1'
		where
			f0 : (Vect predw ZZ -> Vect predw ZZ -> Vect predw ZZ) -> Vect predw ZZ
			f0 x = foldrImpl x (replicate predw (Pos 0)) (\y => zipWith (\meth1 => \meth2 => plusZ meth1 meth2) (tail v) y) (map tail vs)
			f1 : (Vect predw ZZ -> Vect predw ZZ) -> Vect predw ZZ
			f1 x = foldrImpl (zipWith plusZ) (replicate predw (Pos 0)) x (map tail vs)
			lem0 : (\meth1 => \meth2 => Data.Vect.zipWith {n=predw} (\meth3 => \meth4 => plusZ meth3 meth4) meth1 meth2) = Data.Vect.zipWith plusZ
			lem0 = trans ( trans ( cong {f=\x => \meth1 => \meth2 => Data.Vect.zipWith {n=predw} x meth1 meth2} (sym $ etaBinary plusZ) ) (eta _) ) ( sym $ etaBinary (Data.Vect.zipWith {n=predw} plusZ) )
			lem1 : (\x => Data.Vect.zipWith {n=predw} (\meth1 => \meth2 => plusZ meth1 meth2) (tail v) x) = Data.Vect.zipWith {n=predw} plusZ (tail v)
			lem1 = trans ( sym $ eta $ Data.Vect.zipWith {n=predw} (\meth1 => \meth2 => plusZ meth1 meth2) (tail v) ) ( trans ( eta _ ) ( cong {f=\x => Data.Vect.zipWith {n=predw} x (tail v)} (sym $ etaBinary plusZ) ) )
			lem2 : foldrImpl (\meth1 => \meth2 => Data.Vect.zipWith {n=predw} (\meth3 => \meth4 => plusZ meth3 meth4) meth1 meth2) (replicate predw (Pos 0)) (\y => zipWith (\meth1 => \meth2 => plusZ meth1 meth2) (tail v) y) (map tail vs) = foldrImpl (Data.Vect.zipWith plusZ) (replicate predw (Pos 0)) (\y => zipWith (\meth1 => \meth2 => plusZ meth1 meth2) (tail v) y) (map tail vs)
			lem2 ?= cong {f=f0} lem0
			lem3 : foldrImpl (zipWith plusZ) (replicate predw (Pos 0)) (\x => Data.Vect.zipWith {n=predw} (\meth1 => \meth2 => plusZ meth1 meth2) (tail v) x) (map tail vs) = foldrImpl (zipWith plusZ) (replicate predw (Pos 0)) (Data.Vect.zipWith {n=predw} plusZ (tail v)) (map tail vs)
			lem3 ?= cong {f=f1} lem1

	-- Junk from eta reductions done in REPL but not in normal type checking.
	etaCon_tailsumMonrecStepExpr2 : {vs : Matrix n (S predw) ZZ} -> Data.Vect.zipWith (\meth1 => \meth2 => plusZ meth1 meth2) (Data.Vect.tail v) (Data.Vect.tail (monoidsum vs)) = Data.Vect.zipWith (+) (Data.Vect.tail v) (Data.Vect.tail (monoidsum vs))
	etaCon_tailsumMonrecStepExpr2 {v} {vs} {predw} ?= cong {f=f} $ trans (sym $ eta (\meth => plusZ meth)) (sym $ eta plusZ)
		where
			f : (ZZ -> ZZ -> ZZ) -> Vect predw ZZ
			f x = Data.Vect.zipWith x (Data.Vect.tail v) (Data.Vect.tail (monoidsum vs))

	tailsumMonrecStep : {v : Vect (S predw) ZZ} -> Data.Vect.tail $ zipWith (+) v $ monoidsum vs = foldrImpl (zipWith Data.ZZ.plusZ) (replicate predw (Pos 0)) (zipWith Data.ZZ.plusZ (tail v)) (map tail vs)
	tailsumMonrecStep {v} {vs} {predw} = ?tailsumMonrecStep'
	tailsumMonrecStep' = proof
		intros
		rewrite sym (headtails v)
		rewrite sym (headtails $ monoidsum vs)
		compute
		-- This plus eta reductions: exact monoidsumOverTailChariz {v=v} {vs=vs}
		exact trans ( trans (etaCon_tailsumMonrecStepExpr2 {v=v} {vs=vs}) (monoidsumOverTailChariz {v=v} {vs=vs}) ) (etaCon_tailsumMonrecStepExpr1 {v=v} {vs=vs})

	monoidsumOverTailChariz : {vs : Matrix predn (S predw) ZZ} -> zipWith (+) (tail v) (tail $ monoidsum vs) = monoidsum (map tail (v::vs))
	monoidsumOverTailChariz {v} {vs} = trans ( cong {f=zipWith (+) (tail v)} $ tailOfSumIsSumOfTails {vs=vs} ) $
			sym $ monoidrec2D {v=Data.Vect.tail v} {vs=map Data.Vect.tail vs}

	{-
	-- Works in REPL, but complains on loading, as usual.
	monoidsumOverTailChariz = ?monoidsumOverTailChariz'
	monoidsumOverTailChariz' = proof
	  intros
	  exact trans _ $ sym $ monoidrec2D {v=Data.Vect.tail v} {vs=map Data.Vect.tail vs}
	  exact cong {f=zipWith (+) (tail v)} _
	  claim newbrec tail (monoidsum vs) = monoidsum (map tail vs)
	  unfocus
	  exact newbrec
	  exact ?newbrec'
	-}



transposeNHead: with Data.Vect ( head $ transpose xs = map head xs )

transposeNTail : with Data.Vect ( transpose $ tail $ transpose xs = map tail xs )

transposeIsInvolution : with Data.Vect ( transpose $ transpose xs = xs )



total
dotproductRewrite : {v : Vect _ ZZ} -> v <:> w = monoidsum (zipWith (<.>) v w)
dotproductRewrite = Refl



{-
Definitions:
* Verified module
* Verified vector space

Ripped from comments of Classes.Verified, commenting out there coincides with definition of module being in the separate module Control.Algebra.VectorSpace from Control.Algebra.
-}



class (VerifiedRingWithUnity a, VerifiedAbelianGroup b, Module a b) => VerifiedModule a b where
  total moduleScalarMultiplyComposition : (x,y : a) -> (v : b) -> x <#> (y <#> v) = (x <.> y) <#> v
  total moduleScalarUnityIsUnity : (v : b) -> unity {a} <#> v = v
  total moduleScalarMultDistributiveWRTVectorAddition : (s : a) -> (v, w : b) -> s <#> (v <+> w) = (s <#> v) <+> (s <#> w)
  total moduleScalarMultDistributiveWRTModuleAddition : (s, t : a) -> (v : b) -> (s <+> t) <#> v = (s <#> v) <+> (t <#> v)

--class (VerifiedField a, VerifiedModule a b) => VerifiedVectorSpace a b where {}

-- As desired in Data.Matrix.Algebraic
instance [vectModule] Module a b => Module a (Vect n b) where
	(<#>) r = map (r <#>)



{-
ZZ is a VerifiedRing.
-}



{-
"Spans" relation
-}



{-
When checking right hand side of ZZModuleSpan.spans, scaleBy:
Can't resolve type class Module ZZ a

> spans : VerifiedModule ZZ a => (a : Type) -> (P : a -> Type) -> (Q : a -> Type) -> Type
> spans a pprop qprop = (x : a) -> qprop x -> ( scal : List (Subset a pprop,ZZ) ** (Control.Algebra.sum (map scaleBy scal) = x) )
> 	where
> 		scaleBy : (Subset a pprop,ZZ) -> a
> 		scaleBy (Element v _, r) = r <#> v

----------              Other goals:              ----------
{hole4},{hole3},{hole2},{hole1},{hole0}
----------              Assumptions:              ----------
 a : Type
 constrarg : VerifiedModule ZZ a
 a2 : Type
 P : a2 -> Type
 Q : a2 -> Type
----------                 Goal:                  ----------
{hole5} : Type

> spans : VerifiedModule ZZ a => (a : Type) -> (P : a -> Type) -> (Q : a -> Type) -> Type
> spans = ?pr_spans

So it's the term splitting problem encountered in ClassDataExpers. Solution should be to make class constraint argument a normal argument.
-}

spans : {auto a : Type} -> {auto p : VerifiedModule ZZ a} -> (P : a -> Type) -> (Q : a -> Type) -> Type
spans {a} pprop qprop = (x : a) -> qprop x -> ( scal : List (Subset a pprop,ZZ) ** (monoidsum (map scaleBy scal) = x) )
	where
		scaleBy : (Subset a pprop,ZZ) -> a
		scaleBy (Element v _, r) = r <#> v



{-
Same as above, but for lists of vectors
-}



spansl : VerifiedModule ZZ a => Vect n a -> Vect n' a -> Type
spansl = ?spanslpr
{-
spansl xs ys = (vs : [[ZZ]] ** zipWithShort (<:> xs) vs = ys)
	where zipWithShort f as bs = let len = minimum (length as length bs) in Data.VectType.Vect.zipWith f (take len as) (take len bs)
-}

zippyScale : Matrix n' n ZZ -> Matrix n w ZZ -> Matrix n' w ZZ
zippyScale = (<>)

-- Goal here : show that (<>) satisfies the property that the first argument scales the vectors of the second argument in n' various ways.
-- This proof is only a hint at our reason for using (<>) to implement linear combination.
-- Thus, it is a proof for the humans that the definition of linear combination as matrix multiplication is satisfactory, not for the computers.
-- We could have some sort of `because`:=`const` to annotate, though it adds overhead.
zippyIntermed : Vect n ZZ -> Matrix n w ZZ -> Vect w ZZ
zippyIntermed = (<\>)

timesMatMatAsMultipleLinearCombos_EntryChariz : (vs : Matrix (S n') n ZZ) -> (xs : Matrix n w ZZ) -> Data.Vect.head (vs <> xs) = (Data.Vect.head vs) <\> xs

total
zippyLemA : (the (Vect 0 ZZ) []) <\> (the (Matrix 0 w ZZ) []) = replicate w (Pos 0)
zippyLemA {w = Z} = Refl
zippyLemA {w = S n} = cong (zippyLemA {w=n})

total
zippyLemB : replicate w (Pos 0) = monoidsum (zipWith (<#>) (the (Vect 0 ZZ) []) (the (Matrix 0 w ZZ) []))
zippyLemB {w = Z} = Refl
zippyLemB {w = S n} = cong (zippyLemB {w=n})



timesVectMatAsLinearCombo_EntryCharizLeft : (v : Vect n ZZ) -> (xs : Matrix n (S predw) ZZ) -> head (v <\> xs) = monoidsum $ zipWith (*) v (map head xs)
timesVectMatAsLinearCombo_EntryCharizLeft = ?timesVectMatAsLinearCombo_EntryCharizLeft'

-- Reduce addition over (Vect n ZZ) to entrywise addition over ZZ to change (head.monoidsum) into (monoidsum.(map head)).
timesVectMatAsLinearCombo_EntryCharizRight : (v : Vect n ZZ) -> (xs : Matrix n (S predw) ZZ) -> monoidsum $ zipWith (*) v (map head xs) = head $ monoidsum (zipWith (<#>) v xs)
timesVectMatAsLinearCombo_EntryCharizRight [] [] = Refl
timesVectMatAsLinearCombo_EntryCharizRight (vv::vvs) (xx::xxs) = ?timesVectMatAsLinearCombo_EntryCharizRight'
{-
Writing the proof as direct processing of equalities, rather than in the shell, resulted in tragedy.

timesVectMatAsLinearCombo_EntryCharizRight (vv::vvs) (xx::xxs) = sym $ reductComposition putHeadInside reduceMultUnderHeadTo1D
	where
		putHeadInside : Data.Vect.head (monoidsum (zipWith (<#>) (vv::vvs) (xx::xxs))) = monoidsum (map head (zipWith (<#>) (vv::vvs) (xx::xxs)))
		putHeadInside = headOfSumIsSumOfHeads (zipWith (<#>) (vv::vvs) (xx::xxs))
		reduceMultUnderHeadTo1D : map head (zipWith (<#>) (vv::vvs) (xx::xxs)) = zipWith (*) (vv::vvs) (map head (xx::xxs))
		reduceMultUnderHeadTo1D = ?reduceMultUnderHeadTo1D'
		reductComposition : head (monoidsum (zipWith (<#>) (vv::vvs) (xx::xxs))) = monoidsum (map head (zipWith (<#>) (vv::vvs) (xx::xxs))) -> map head (zipWith (<#>) (vv::vvs) (xx::xxs)) = zipWith (*) (vv::vvs) (map head (xx::xxs)) -> head (monoidsum (zipWith (<#>) (vv::vvs) (xx::xxs))) = monoidsum (zipWith (*) (vv::vvs) (map head (xx::xxs)))
		reductComposition pr0 pr1 = ?reductComposition'
		{-
		For some reason, trying any of these proofs makes Idris claim (vv) is expected to be a (Nat).

		composeReducts = rewrite sym reduceMultUnderHeadTo1D in putHeadInside
		composeReducts = trans putHeadInside (cong {f=monoidsum} reduceMultUnderHeadTo1D)
		-}
		-- composeReducts : head (monoidsum (zipWith (<#>) (vv::vvs) (xx::xxs))) = monoidsum (zipWith (*) (vv::vvs) (map head (xx::xxs)))
		-- composeReducts = reductComposition putHeadInside reduceMultUnderHeadTo1D
-}

reduceMultUnderHeadTo1D : {xxs : Matrix n (S m) ZZ} -> map Data.Vect.head (zipWith (<#>) (vv::vvs) (xx::xxs)) = zipWith (the (ZZ -> ZZ -> ZZ) (*)) (vv::vvs) (map Data.Vect.head (xx::xxs))
reduceMultUnderHeadTo1D {n=Z} {vv} {xx} = ?reduceMultUnderHeadTo1D_triv
reduceMultUnderHeadTo1D {n=S predn} {vv} {xx} = ?reduceMultUnderHeadTo1D'
-- reduceMultUnderHeadTo1D {n=S predn} {vv} {xx} = trans (cong $ headMapChariz {xs=xx}) $ (cong {f=(Data.Vect.(::) $ multZ vv (head xx))} reduceMultUnderHeadTo1D)

reduceMultUnderHeadTo1D_triv = proof
  intros
  rewrite sym (the (xxs = []) zeroVecEq)
  rewrite sym (the (vvs = []) zeroVecEq)
  compute
  exact cong {f=(::[])} _
  exact headMapChariz {xs=xx}

reduceMultUnderHeadTo1D' = proof
  intros
  -- Not required in the REPL: {f=multZ vv}
  exact trans (cong {f=(::(map head $ zipWith (<#>) vvs xxs))} $ headMapChariz {f=multZ vv} {xs=xx}) _
  compute
  exact cong {f=(::) (multZ vv (head xx))} _
  rewrite sym $ headtails vvs
  rewrite sym $ headtails xxs
  exact reduceMultUnderHeadTo1D {vv=head vvs} {vvs=tail vvs} {xx=head xxs} {xxs=tail xxs}

timesVectMatAsLinearCombo_EntryCharizRight' = proof
  intros
  claim putHeadInside head (monoidsum (zipWith (<#>) (vv::vvs) (xx::xxs))) = monoidsum (map head (zipWith (<#>) (vv::vvs) (xx::xxs)))
  unfocus
  exact sym $ trans putHeadInside (cong {f=monoidsum} $ reduceMultUnderHeadTo1D {vv=vv} {xx=xx})
  exact headOfSumIsSumOfHeads (zipWith (<#>) (vv::vvs) (xx::xxs))

timesVectMatAsLinearCombo_EntryChariz : (v : Vect n ZZ) -> (xs : Matrix n (S predw) ZZ) -> head (v <\> xs) = head $ monoidsum (zipWith (<#>) v xs)
timesVectMatAsLinearCombo_EntryChariz v xs = trans (timesVectMatAsLinearCombo_EntryCharizLeft v xs) (timesVectMatAsLinearCombo_EntryCharizRight v xs)



transParaphraseGeneral0 : (vs : Matrix n (S predw) ZZ) -> transpose vs = (head $ transpose vs) :: (tail $ transpose vs)
transParaphraseGeneral0 vs = headtails (transpose vs)

transposeNTail2 : {xs : Matrix n (S predw) ZZ} -> tail $ transpose xs = transpose $ map tail xs
transposeNTail2 = ?transposeNTail2'
transposeNTail2' = proof
  intros
  rewrite sym (sym $ transposeIsInvolution {xs=tail (transpose xs)})
  exact cong {f=transpose} transposeNTail

transParaphraseGeneral1 : (vs : Matrix n (S predw) ZZ) -> transpose vs = (map Data.Vect.head vs) :: ( transpose $ map Data.Vect.tail vs )
transParaphraseGeneral1 {n} {predw} vs = ?transParaphraseGeneral1'

transParaphraseGeneral1' = proof
  intros
  rewrite sym (transParaphraseGeneral0 vs)
  rewrite sym (transposeNTail2 {xs=vs})
  rewrite sym (transposeNHead {xs=vs})
  exact Refl

observationTransposeFormInMult0 : {vects : Matrix n (S predw) ZZ} -> scals <\> vects = map (\ARG => scals <:> ARG) ( (map Data.Vect.head vects) :: ( transpose $ map Data.Vect.tail vects ) )
observationTransposeFormInMult0 {scals} {vects} = cong {f=map (\ARG => scals <:> ARG)} (transParaphraseGeneral1 vects)

observationTransposeFormInMult1 : {vects : Matrix n (S predw) ZZ} -> scals <\> vects = ( scals <:> (map Data.Vect.head vects) ) :: map (\ARG => scals <:> ARG) ( transpose $ map Data.Vect.tail vects )
observationTransposeFormInMult1 = observationTransposeFormInMult0

{-
Recurses over the inner dimension of the matrix.
Hence, reduces (timesVectMatAsLinearCombo scals vects) to the cases ( timesVectMatAsLinearCombo (_::_) ([] :: _) )
-}
timesVectMatAsHeadTail_ByTransposeElimination : {vects : Matrix n (S predw) ZZ} -> scals <\> vects = (scals <:> map Data.Vect.head vects) :: ( scals <\> map Data.Vect.tail vects )
timesVectMatAsHeadTail_ByTransposeElimination = observationTransposeFormInMult1



compressMonoidsum_lem1 : {vects : Matrix n (S predw) ZZ} -> monoidsum ( zipWith (<.>) scals (map Data.Vect.head vects) ) :: monoidsum ( zipWith (<#>) scals (map Data.Vect.tail vects) ) = ( head $ monoidsum ( zipWith (<#>) scals vects ) ) :: monoidsum ( zipWith (<#>) scals (map Data.Vect.tail vects) )
compressMonoidsum_lem1 {scals} {vects} = cong {f=(:: monoidsum ( zipWith (<#>) scals (map Data.Vect.tail vects) ) )} (timesVectMatAsLinearCombo_EntryCharizRight scals vects)

compressMonoidsum_lem2 : {n : Nat} -> {scals : Vect n ZZ} -> {predw : Nat} -> {vects : Vect n (Vect (S predw) ZZ)} -> Data.Vect.(::) (Data.Vect.head $ monoidsum ( zipWith (<#>) scals vects )) ( monoidsum ( zipWith (<#>) scals (map Data.Vect.tail vects) ) ) = monoidsum ( zipWith (<#>) scals vects )
compressMonoidsum_lem2 = ?compressMonoidsum_lem2'

rewriteZipWithUnderTail : {scals : Vect n ZZ} -> {vects : Matrix n (S predw) ZZ} -> map Data.Vect.tail $ Data.Vect.zipWith (<#>) scals vects = Data.Vect.zipWith (<#>) scals (map Data.Vect.tail vects)

compressMonoidsum_lem3 : {n : Nat} -> {scals : Vect n ZZ} -> {predw : Nat} -> {vects : Vect n (Vect (S predw) ZZ)} -> monoidsum ( zipWith (<#>) scals (map Data.Vect.tail vects) ) = tail $ monoidsum ( zipWith (<#>) scals vects )
compressMonoidsum_lem3 {predw=Z} {n} = zeroVecEq
compressMonoidsum_lem3 {predw=S predpredw} {n=Z} = ?compressMonoidsum_lem3_rhs_majZ
compressMonoidsum_lem3 {predw=S predpredw} {n=S predn} {scals} {vects} = trans (cong {f=monoidsum} $ sym rewriteZipWithUnderTail) (sym tailOfSumIsSumOfTails)
{-
compressMonoidsum_lem3_rhs_majSminArb = proof
  intros
  exact trans (cong {f=monoidsum} $ sym $ rewriteZipWithUnderTail {scals=scals} {vects=vects}) _
  exact believe_me "assas
-}

compressMonoidsum_lem3_rhs_majZ = proof
  intros
  rewrite sym $ the (scals=[]) zeroVecEq
  rewrite sym $ the (vects=[]) zeroVecEq
  trivial

compressMonoidsum_lem2' = proof
	intros
	rewrite sym (headtails $ monoidsum ( zipWith (<#>) scals vects ))
	exact (vectConsCong ( head (monoidsum (zipWith (<#>) scals vects)) ) _ _ compressMonoidsum_lem3)

compressMonoidsum : {vects : Matrix n (S predw) ZZ} -> monoidsum ( zipWith (<.>) scals (map Data.Vect.head vects) ) :: monoidsum ( zipWith (<#>) scals (map Data.Vect.tail vects) ) = monoidsum ( zipWith (<#>) scals vects )
compressMonoidsum = ?compressMonoidsum'

compressMonoidsum' = proof
	intros
	exact trans (compressMonoidsum_lem1 {scals=scals} {vects=vects}) compressMonoidsum_lem2



timesVectMatAsLinearCombo : (v : Vect n ZZ) -> (xs : Matrix n w ZZ) -> ( v <\> xs = monoidsum (zipWith (<#>) v xs) )
timesVectMatAsLinearCombo [] [] = trans zippyLemA zippyLemB
timesVectMatAsLinearCombo (z::zs) ([] :: xs) = zeroVecEq
timesVectMatAsLinearCombo (z::zs) ((xx::xxs)::xs) = ?timesVectMatAsLinearCombo'

timesVectMatAsLinearCombo_analysis0 : {scals : Vect (S predn) ZZ} -> {vects : Matrix (S predn) (S predw) ZZ} -> (scals <:> map Data.Vect.head vects) :: ( scals <\> map Data.Vect.tail vects ) = monoidsum (zipWith (<#>) scals vects)
timesVectMatAsLinearCombo_analysis0 = ?timesVectMatAsLinearCombo_analysis0'

timesVectMatAsLinearCombo_analysis1 : {scals : Vect (S predn) ZZ} -> {vects : Matrix (S predn) (S predw) ZZ} -> (scals <:> map Data.Vect.head vects) :: ( scals <\> map Data.Vect.tail vects ) = monoidsum ( zipWith (<.>) scals (map Data.Vect.head vects) ) :: monoidsum ( zipWith (<#>) scals (map Data.Vect.tail vects) )
timesVectMatAsLinearCombo_analysis1 = ?timesVectMatAsLinearCombo_analysis1'

timesVectMatAsLinearCombo_analysis1' = proof
  intros
  claim headequality ( (scals <:> map Data.Vect.head vects) = monoidsum (zipWith (<.>) scals (map Data.Vect.head vects)) )
  unfocus
  exact trans (cong {f=(flip Data.Vect.(::)) _} headequality) _
  exact dotproductRewrite
  compute
  exact (vectConsCong (monoidsum (zipWith (<.>) scals (map head vects))) _ _ (timesVectMatAsLinearCombo scals (map Data.Vect.tail vects)))

timesVectMatAsLinearCombo_analysis0' = proof
  intros
  exact trans timesVectMatAsLinearCombo_analysis1 (compressMonoidsum {scals=scals} {vects=vects})

timesVectMatAsLinearCombo' = proof
  intros
  exact ( trans (timesVectMatAsHeadTail_ByTransposeElimination {scals=(z::zs)} {vects=((xx::xxs)::xs)}) (timesVectMatAsLinearCombo_analysis0 {scals=(z::zs)} {vects=((xx::xxs)::xs)}) )



{-
Labels (xs, ys) aren't depended on for values, they're just hints, used cause

	%name Matrix xs, ys

doesn't work.

Type must be given by a proof, because

	spanslz : {n : Nat} -> {n' : Nat} -> (xs : Matrix n w ZZ) -> (ys : Matrix n' w ZZ) -> Type
	spanslz {n} {n'} xs ys = (vs : Matrix n' n ZZ ** vs `zippyScale` xs = ys)

alone will just split the (n, n') in the declaration / theorem stmt from some n'1 in the definition / proof.
-}
spanslz : (xs : Matrix n w ZZ) -> (ys : Matrix n' w ZZ) -> Type
spanslz = ?spanslz'
spanslz' = proof
	intros
	exact (vs : Matrix n' n ZZ ** vs `zippyScale` xs = ys)
{- spanslz {n} {n'} xs ys = (vs : Matrix n' n ZZ ** vs `zippyScale` xs = ys) -}



{-
Proof of relational properties of span

i.e.,
Relational: equivalence relation axioms
Algebraic: gcd and lcm divisibility relationships via Bezout's identity
-}



{-
When checking type of ZZModuleSpan.spansTrans:
INTERNAL ERROR: Not an attackable hole
This is probably a bug, or a missing error message.
Please consider reporting at https://github.com/idris-lang/Idris-dev/issues

> spansTrans : spans p q -> spans q r -> spans p r

or

> spansTrans : spans p q -> spans q r -> spans p r
-- with rule / dependent pattern matching
> spansTrans par_orAllxsNrs_prsum par_orAllysNss_prsum = ?prSpansTrans

same applies when the type argument to (spans) is made explicit, not an auto implicit. Should try making the class instance explicit too. On the other hand, it may be because of the missing proof of VerifiedRing for ZZ.
-}

-- spansTrans : spans p q -> spans q r -> spans p r
-- with rule / dependent pattern matching
-- spansTrans par_orAllxsNrs_prsum par_orAllysNss_prsum = ?prSpansTrans



{-
spansltrans : spansl xs ys -> spansl ys zs -> spansl xs zs
spansltrans xs ys
-}

{-
spanslztrans : {n : Nat} -> {n' : Nat} -> {xs : Matrix n m ZZ} -> {ys : Matrix n' m ZZ} -> spanslz xs ys -> spanslz ys zs -> spanslz xs zs
-- spanslztrans (vsx ** prvsx) (vsy ** prvsy) = ?spanslztransPr
spanslztrans {n} {n'} {xs} {ys} (vsx ** prvsx) (vsy ** prvsy) = ( the (Vect n' (Vect n ZZ)) _ ** rewrite sym prvsx in prvsy )
-}
