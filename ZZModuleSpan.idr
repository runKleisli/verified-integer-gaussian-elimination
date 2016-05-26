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



mapheadrec : with Data.Vect ( map head (v::vs) = (head v) :: (map head vs) )
mapheadrec = Refl

headtails : (v : Vect (S predk) _) -> v = (head v) :: (tail v)
headtails (vv::vvs) = Refl



-- The theorem below this one should not be a necessary weakening, since the functions have equivalent definitions.
indexFZIshead : index FZ = Data.Vect.head

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

headOfSumIsSumOfHeads : (xs : Vect (S m) (Vect (S n) ZZ)) -> head (monoidsum xs) = monoidsum (map head xs)
headOfSumIsSumOfHeads = headOfSumIsSumOfHeadsArg lemma_VectAddHead



transposeNHead: with Data.Vect ( head $ transpose xs = map head xs )

transposeNTail : with Data.Vect ( transpose $ tail $ transpose xs = map tail xs )

transposeIsInvolution : with Data.Vect ( transpose $ transpose xs = xs )



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

zippyThm1 : (vs : Matrix (S n') n ZZ) -> (xs : Matrix n w ZZ) -> Data.Vect.head (vs <> xs) = (Data.Vect.head vs) <\> xs

zippyLemA : (the (Vect 0 ZZ) []) <\> (the (Matrix 0 w ZZ) []) = replicate w (Pos 0)
zippyLemA {w = Z} = Refl
zippyLemA {w = S n} = ?zippyLemA_induct
zippyLemA_induct = proof
	intro
	exact (cong zippyLemA)
zippyLemB : replicate w (Pos 0) = monoidsum (zipWith (<#>) (the (Vect 0 ZZ) []) (the (Matrix 0 w ZZ) []))
zippyLemB {w = Z} = Refl
zippyLemB {w = S n} = ?zippyLemB_induct
zippyLemB_induct = proof
	intro
	exact (cong zippyLemB)

{-
-- The following proofs are a matter of making a readable train of thought behind the proof details. That is, they explain why one expects the illegible final goal to be solved in the efficient way that it is.

zippyLemC : {predw : Nat} -> (z::[]) <\> ((x0::x0s) :: []) = map (\ARG => ((z::[]) <:> ARG)) $ zipWith (::) ( the (Vect (S predw) ZZ) (x0::x0s) ) (replicate (S predw) [])
zippyLemC = Refl

zippyLemD : map (\ARG => ((z::[]) <:> ARG)) $ zipWith (::) ( the (Vect (S predw) ZZ) (x0::x0s) ) (replicate (S predw) []) = ?zippyLemD_recurse
zippyLemD = Refl

zippyLemD_recurse = proof
  intros
  let headterm = head $ zipWith (Data.Vect.(::)) ( the (Vect (S predw) ZZ) (x0::x0s) ) (replicate (S predw) [])
  let tailterm = tail $ zipWith (Data.Vect.(::)) ( the (Vect (S predw) ZZ) (x0::x0s) ) (replicate (S predw) [])
  exact ( ((z::[])<:>headterm) :: map (\ARG => ( (z::[]) <:> ARG )) tailterm )

zippyLemE : map (\ARG => ((z::[]) <:> ARG)) $ zipWith (::) ( the (Vect (S predw) ZZ) (x0::x0s) ) (replicate (S predw) []) = ?zippyLemE_recurse
zippyLemE = Refl

-- Same as zippyLemD_recurse, but expanding the head and tail of the list made with (zipWith (::))
zippyLemE_recurse = proof
  intros
  let headterm = Data.Vect.(::) x0 []
  let tailterm = zipWith (Data.Vect.(::)) ( the (Vect predw ZZ) x0s ) (replicate predw [])
  exact ( ((z::[])<:>headterm) :: map (\ARG => ( (z::[]) <:> ARG )) tailterm )

zippyLemFnHalf : (z::[]) <:> (Data.Vect.(::) (the ZZ x0) []) = z*x0
zippyLemFnHalf {z} {x0} = plusZeroRightNeutralZ (multZ z x0)

zippyLemF : map (\ARG => ((z::[]) <:> ARG)) $ zipWith (::) ( the (Vect (S predw) ZZ) (x0::x0s) ) (replicate (S predw) []) = z*x0 :: ( map (\ARG => ( (z::[]) <:> ARG )) $ zipWith (::) ( the (Vect predw ZZ) x0s ) (replicate predw []) )
zippyLemF = ?zippyLemF'

zippyLemF' = proof
  intros
  rewrite sym zippyLemE
  -- Might be simplifiable using Data.Vect.vectConsCong
  exact cong {f=(:: ( map (\ARG => ( (z::[]) <:> ARG )) $ zipWith (::) ( the (Vect predw ZZ) x0s ) (replicate predw []) ))} zippyLemFnHalf
  -- Junk holes that were generated by the interactive prover
  -- Errors are like "Can't infer argument predw to S, Can't infer argument z to zippyLemE". w.r.t. "Can't infer argument predw to zipWith", this may explain why the (Data.Vect) namespace must be explicitly stated for zipWith.
  exact Z
  exact []
  exact (Pos 0)
  exact (Pos 0)

zippyLemG : {z : ZZ} -> (z::[]) <\> ((x0::x0s) :: []) = z*x0 :: ( (z::[]) <\> (x0s::[]) )
zippyLemG = zippyLemF

zippyLemG_nullcaseforH : {z : ZZ} -> (z::[]) <\> ([] :: []) = []
zippyLemG_nullcaseforH = Refl
-}

{-
	zippyLemG {z=z} {x0=x0} {x0s=x0s}

and

	the (map (z*) (x0::x0s) = z*x0::(x0::x0s)) Refl

were not needed at all for zippyLemH.
-}

-- See comment atop zippyLemA through zippyLemG
zippyLemH : {z : ZZ} -> (xs : Vect w ZZ) -> (z::[]) <\> (the (Matrix 1 w ZZ) (xs :: [])) = map (z*) xs
zippyLemH [] = Refl
zippyLemH {z} (x0::x0s) = ?zippyLemH'
zippyLemH' = proof
  intros
  rewrite sym (plusZeroRightNeutralZ (multZ z x0))
  exact (cong (zippyLemH x0s))

-- See comment atop zippyLemA through zippyLemG
-- Proof is of the same form as zippyLemH, and suggested by its success.
zippyLemI : {z : ZZ} -> (xs : Vect w ZZ) -> map (z*) xs = monoidsum (Data.Vect.zipWith (<#>) (z::[]) (xs::[]))
zippyLemI [] = Refl
zippyLemI {z} (x0::x0s) = ?zippyLemI'
zippyLemI' = proof
  intros
  rewrite sym (plusZeroRightNeutralZ (multZ z x0))
  exact (cong (zippyLemI x0s))

zippyLemJ : {z : ZZ} -> (xs : Vect w ZZ) -> (z::[]) <\> (the (Matrix 1 w ZZ) (xs :: [])) =  monoidsum (Data.Vect.zipWith (<#>) (z::[]) (xs::[]))
zippyLemJ xs = trans (zippyLemH xs) (zippyLemI xs)

-- Modeled after zippyLemH
{-
zippyLemK : {z : ZZ} -> {predn : Nat} -> (xs : Vect w ZZ) -> (z::zs) <\> (the (Matrix (S predn) w ZZ) (xs :: xss)) = ?lemKTy -- ?lemKfunc (map (z*) xs) ((z::zs) <\> xss)
-}

{-
-- !!!!~~~ THIS zippyLemL IS ALL BROKEN OKAY ~~~!!!!!!!

-- Used to figure out how to prove zippyLemL, of which this is a special case.
zippyLemL_Mini : {z : ZZ} -> (xs : Vect 1 ZZ) -> (map (z*) xs)::( monoidsum (Data.Vect.zipWith (<#>) zs xss) ) = monoidsum (Data.Vect.zipWith (<#>) (z::zs) (xs::xss))
zippyLemL_Mini (x::[]) = ?zippyLemMini_rhs

-- Modeled after zippyLemI
-- Raises a type error if you set w to 1.
zippyLemL : {z : ZZ} -> (xs : Vect w ZZ) -> (map (z*) xs)++( monoidsum (Data.Vect.zipWith (<#>) zs xss) ) = monoidsum (Data.Vect.zipWith (<#>) (z::zs) (xs::xss))
zippyLemL [] = ?zippyLemL_rhs_1

-- This claimed proof doesn't have to be valid. In particular, it's probably not, but it shows you what the theorem should degenerate to in the case (xs=[]).

zippyLemL_rhs_1 = proof
  intros
  rewrite (zeroVecVecId xss)
  claim lem_unfunction ( (\x => Data.Vect.zipWith (\meth1 => \meth2 => plusZ meth1 meth2) [] x) = id )
  unfocus
  rewrite sym lem_unfunction
  exact Refl
  exact ?lem_unfunction_tbContd

zippyLemL (x0::x0s) = ?zippyLemL_rhs_2
-}

zippyThm_EntryCharizLeft : (v : Vect n ZZ) -> (xs : Matrix n (S predw) ZZ) -> head (v <\> xs) = monoidsum $ zipWith (*) v (map head xs)
zippyThm_EntryCharizLeft = ?zippyThm_EntryCharizLeft'

-- Reduce addition over (Vect n ZZ) to entrywise addition over ZZ to change (head.monoidsum) into (monoidsum.(map head)).
zippyThm_EntryCharizRight : (v : Vect n ZZ) -> (xs : Matrix n (S predw) ZZ) -> monoidsum $ zipWith (*) v (map head xs) = head $ monoidsum (zipWith (<#>) v xs)
zippyThm_EntryCharizRight [] [] = Refl
zippyThm_EntryCharizRight (vv::vvs) (xx::xxs) = ?zippyThm_EntryCharizRight'
{-
Writing the proof as direct processing of equalities, rather than in the shell, resulted in tragedy.

zippyThm_EntryCharizRight (vv::vvs) (xx::xxs) = sym $ reductComposition putHeadInside reduceMultUnderHeadTo1D
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

zippyThm_EntryCharizRight' = proof
  intros
  claim putHeadInside head (monoidsum (zipWith (<#>) (vv::vvs) (xx::xxs))) = monoidsum (map head (zipWith (<#>) (vv::vvs) (xx::xxs)))
  unfocus
  claim reduceMultUnderHeadTo1D (map head (zipWith (<#>) (vv::vvs) (xx::xxs)) = zipWith (*) (vv::vvs) (map head (xx::xxs)))
  unfocus
  exact sym $ trans putHeadInside (cong {f=monoidsum} reduceMultUnderHeadTo1D)
  exact headOfSumIsSumOfHeads (zipWith (<#>) (vv::vvs) (xx::xxs))
  exact ?reduceMultUnderHeadTo1D'

zippyThm_EntryChariz : (v : Vect n ZZ) -> (xs : Matrix n (S predw) ZZ) -> head (v <\> xs) = head $ monoidsum (zipWith (<#>) v xs)
zippyThm_EntryChariz v xs = trans (zippyThm_EntryCharizLeft v xs) (zippyThm_EntryCharizRight v xs)



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
Hence, reduces (zippyThm2 scals vects) to the cases ( zippyThm2 (_::_) ([] :: _) )
-}
timesVectMatAsHeadTail_ByTransposeElimination : {vects : Matrix n (S predw) ZZ} -> scals <\> vects = (scals <:> map Data.Vect.head vects) :: ( scals <\> map Data.Vect.tail vects )
timesVectMatAsHeadTail_ByTransposeElimination = observationTransposeFormInMult1



compressMonoidsum_lem1 : {vects : Matrix n (S predw) ZZ} -> monoidsum ( zipWith (<.>) scals (map Data.Vect.head vects) ) :: monoidsum ( zipWith (<#>) scals (map Data.Vect.tail vects) ) = ( head $ monoidsum ( zipWith (<#>) scals vects ) ) :: monoidsum ( zipWith (<#>) scals (map Data.Vect.tail vects) )
compressMonoidsum_lem1 {scals} {vects} = cong {f=(:: monoidsum ( zipWith (<#>) scals (map Data.Vect.tail vects) ) )} (zippyThm_EntryCharizRight scals vects)

compressMonoidsum_lem2 : {n : Nat} -> {scals : Vect n ZZ} -> {predw : Nat} -> {vects : Vect n (Vect (S predw) ZZ)} -> Data.Vect.(::) (Data.Vect.head $ monoidsum ( zipWith (<#>) scals vects )) ( monoidsum ( zipWith (<#>) scals (map Data.Vect.tail vects) ) ) = monoidsum ( zipWith (<#>) scals vects )
compressMonoidsum_lem2 = ?compressMonoidsum_lem2'

compressMonoidsum_lem3 : {n : Nat} -> {scals : Vect n ZZ} -> {predw : Nat} -> {vects : Vect n (Vect (S predw) ZZ)} -> monoidsum ( zipWith (<#>) scals (map Data.Vect.tail vects) ) = tail $ monoidsum ( zipWith (<#>) scals vects )

compressMonoidsum_lem2' = proof
	intros
	rewrite sym (headtails $ monoidsum ( zipWith (<#>) scals vects ))
	exact (vectConsCong ( head (monoidsum (zipWith (<#>) scals vects)) ) _ _ compressMonoidsum_lem3)

compressMonoidsum : {vects : Matrix n (S predw) ZZ} -> monoidsum ( zipWith (<.>) scals (map Data.Vect.head vects) ) :: monoidsum ( zipWith (<#>) scals (map Data.Vect.tail vects) ) = monoidsum ( zipWith (<#>) scals vects )
compressMonoidsum = ?compressMonoidsum'

compressMonoidsum' = proof
	intros
	exact trans (compressMonoidsum_lem1 {scals=scals} {vects=vects}) compressMonoidsum_lem2



{-
Evidence for zippyThm2:

chiefly: zippyThm_EntryChariz

sum' = foldr (<+>) neutral
(w <:> v) = foldr (<+>) neutral (zipWith (<.>) w v)
(r <\> m) = map (\ARG => (r <:> ARG)) (transpose m)
-}
zippyThm2 : (v : Vect n ZZ) -> (xs : Matrix n w ZZ) -> ( v <\> xs = monoidsum (zipWith (<#>) v xs) )
zippyThm2 [] [] = trans zippyLemA zippyLemB
-- zippyThm2 (z::zs) (x::xs) = ?zippyThm2_rhs_1
zippyThm2 (z::zs) ([] :: xs) = zeroVecEq
zippyThm2 (z::zs) ((xx::xxs)::xs) = ?zippyThm2_rhs_2

zippyThm2_analysis0 : {scals : Vect (S predn) ZZ} -> {vects : Matrix (S predn) (S predw) ZZ} -> (scals <:> map Data.Vect.head vects) :: ( scals <\> map Data.Vect.tail vects ) = monoidsum (zipWith (<#>) scals vects)
zippyThm2_analysis0 = ?zippyThm2_analysis0'

zippyThm2_analysis1 : {scals : Vect (S predn) ZZ} -> {vects : Matrix (S predn) (S predw) ZZ} -> (scals <:> map Data.Vect.head vects) :: ( scals <\> map Data.Vect.tail vects ) = monoidsum ( zipWith (<.>) scals (map Data.Vect.head vects) ) :: monoidsum ( zipWith (<#>) scals (map Data.Vect.tail vects) )
zippyThm2_analysis1 = ?zippyThm2_analysis1'

{-
zippyThm2_analysis1' = proof
	intros
	claim headequality ( (scals <:> map Data.Vect.head vects) = monoidsum (zipWith (<.>) scals (map Data.Vect.head vects)) )
	unfocus
	rewrite sym headequality
	exact (vectConsCong ( monoidsum (zipWith (<.>) scals (map Data.Vect.head vects)) ) _ _ (zippyThm2 scals (map Data.Vect.tail vects)) )
-}

zippyThm2_analysis0' = proof
  intros
  exact trans zippyThm2_analysis1 (compressMonoidsum {scals=scals} {vects=vects})

zippyThm2_rhs_2 = proof
  intros
  exact ( trans (timesVectMatAsHeadTail_ByTransposeElimination {scals=(z::zs)} {vects=((xx::xxs)::xs)}) (zippyThm2_analysis0 {scals=(z::zs)} {vects=((xx::xxs)::xs)}) )

{-
The proof I want:

zippyThm2_rhs_2 = proof
  intros
  exact ( trans (timesVectMatAsHeadTail_ByTransposeElimination {scals=(z::zs)} {vects=((xx::xxs)::xs)}) _ )
  rewrite sym (cong $ zippyThm2 (z::zs) ( map tail ((xx::xxs)::xs) ))
  rewrite sym (cong dotproductRewrite)
  exact compressMonoidsum
-}

{-
zippyThm2 (z::[]) (xs :: []) = zippyLemJ xs
zippyThm2 {n=S (S n')} {w=S w'} (z::zs) ((xx::xxs)::(xsx::xss)) = ?zippyThm2' -- trans recursionStep1 compressionStep -- replace with shell-based proof, as with previous problems
	where
		xs : Matrix (S n') (S w') ZZ
		xs = xsx::xss
		recursionStep0 : (z::zs) <\> ((xx::xxs)::xs) = ( (z::zs) <:> map head ((xx::xxs)::xs) ) :: monoidsum ( zipWith (<#>) (z::zs) ( map tail ((xx::xxs)::xs) ) )
		recursionStep0 = ?recursionStep0'
		-- recursionStep0 = rewrite sym ( zippyThm2 (z::zs) (map tail ((xx::xxs)::xs)) ) in (timesVectMatAsHeadTail_ByTransposeElimination {scals=z::zs} {vects=(xx::xxs)::xs})
		recursionStep1 : (z::zs) <\> ((xx::xxs)::xs) = monoidsum ( zipWith (<.>) (z::zs) ( map head ((xx::xxs)::xs) ) ) :: ( monoidsum (zipWith (<#>) (z::zs) ( map tail ((xx::xxs)::xs) )) )
		-- recursionStep1 = rewrite sym dotproductRewrite in recursionStep0
		compressionStep : monoidsum ( zipWith (<.>) (z::zs) (map Data.Vect.head ((xx::xxs)::xs)) ) :: monoidsum ( zipWith (<#>) (z::zs) (map Data.Vect.tail ((xx::xxs)::xs)) ) = monoidsum ( zipWith (<#>) (z::zs) ((xx::xxs)::xs) )
		compressionStep = compressMonoidsum {scals=z::zs} {vects=(xx::xxs)::xs}
-}
{-
Have to reduce this to an intermediate theorem inductive in x@(x0::x0s), reducing to describing the effect of multiplying by z.

Actually, showing each side reduces to what's basically (z*) would be proof enough.
-}
-- !!!PROPOSED!!! zippyThm2 (z :: (zt::zts)) ((x0::x0s) :: (xt::xts)) = ?zippyThm2_rhs_2
{-
Beginnings of a substitution proof... abandoned cause nontrivial to look at.
Should probably just use induction, splitting the cases automatically.

zippyThm2 = ?zippyThm2Pr
	where
		eq1 : v <\> xs = map (\ARG => (v <:> ARG)) (transpose xs)
		eq2 : ( \v => \xs => map (\ARG => (v <:> ARG)) (transpose xs) ) = ( \v => \xs => map (\ARG => (v (foldr (<+>) neutral (zipWith (<.>) w v)) ARG)) (transpose xs) )
		eq2 = cong {f=\k => \v => \xs => map (\ARG => (v `k` ARG)) (transpose xs)} Refl
		eq3 : map (\ARG => (v (foldr (<+>) neutral (zipWith (<.>) w v)) ARG)) (transpose xs) = map (\ARG => (v (monoidsum (zipWith (<.>) w v)) ARG)) (transpose xs)
-}

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
