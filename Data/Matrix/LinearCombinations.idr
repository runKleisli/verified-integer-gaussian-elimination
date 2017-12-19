module Data.Matrix.LinearCombinations

import Control.Algebra
import Control.Algebra.VectorSpace -- definition of module
import Classes.Verified -- definition of verified algebras other than modules
import Control.Algebra.DiamondInstances
import Data.Matrix
import Data.Matrix.Algebraic -- module instances; from Idris 0.9.20

import Data.Vect.Structural
import Data.Matrix.Structural

import Data.ZZ

import Control.Algebra.ZZVerifiedInstances
import Data.Matrix.AlgebraicVerified



monoidsum : (Foldable t, Monoid a) => t a -> a
{-
-- Idris version 0.9.18
monoidsum = Control.Algebra.sum
-}
-- Idris version 0.9.20
monoidsum = sum'
--



{-
Basic theorems regarding
* Abelian groups
* Vect _ _
* Matrix _ _ _
* Vect _ ZZ
	ideally generalized from ZZ to other verified rings
* Matrix _ _ ZZ
	ideally generalized from ZZ to other verified rings
-}



doubleSumInnerSwap : VerifiedAbelianGroup t => (a, b, c, d : t) -> (a<+>b)<+>(c<+>d) = (a<+>c)<+>(b<+>d)
doubleSumInnerSwap a b c d = trans (sym $ semigroupOpIsAssociative a b (c<+>d))
	$ trans ( cong {f=(a<+>)} $ trans (semigroupOpIsAssociative b c d)
		$ trans (cong {f=(<+>d)} $ abelianGroupOpIsCommutative b c)
		$ sym $ semigroupOpIsAssociative c b d)
	$ semigroupOpIsAssociative a c (b<+>d)

doubleSumInnerSwap_Vect : VerifiedRingWithUnity t => (a, b, c, d : Vect n t)
	-> (a<+>b)<+>(c<+>d) = (a<+>c)<+>(b<+>d)
doubleSumInnerSwap_Vect a b c d = trans (sym $ semigroupOpIsAssociative_Vect a b (c<+>d))
	$ trans ( cong {f=(a<+>)} $ trans (semigroupOpIsAssociative_Vect b c d)
		$ trans (cong {f=(<+>d)} $ abelianGroupOpIsCommutative_Vect b c)
		$ sym $ semigroupOpIsAssociative_Vect c b d)
	$ semigroupOpIsAssociative_Vect a c (b<+>d)



total
lemma_VectAddHead : (v, w : Vect (S n) ZZ) -> head(v<+>w) = (head v)<+>(head w)
lemma_VectAddHead (vv::vvs) (ww::wws) = Refl

total
matrixAddHead : (x, y : Matrix (S predn) m ZZ) -> Vect.head (x<+>y) = (Vect.head x)<+>(Vect.head y)
matrixAddHead (x::xs) (y::ys) = Refl

total
lemma_VectAddTail : (x, y : Vect (S predn) ZZ) -> Vect.tail (x<+>y) = (Vect.tail x)<+>(Vect.tail y)
lemma_VectAddTail (x::xs) (y::ys) = Refl

total
matrixAddTail : (x, y : Matrix (S predn) m ZZ) -> Vect.tail (x<+>y) = (Vect.tail x)<+>(Vect.tail y)
matrixAddTail (x::xs) (y::ys) = Refl

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
monoidrec1D = monoidrec _ _

monoidrec2D : {v : Vect m ZZ} -> {vs : Vect n (Vect m ZZ)} -> monoidsum (v::vs) = v <+> (monoidsum vs)
monoidrec2D = monoidrec _ _

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

tailOfSumIsSumOfTails :
	{vs : Matrix n (S predw) ZZ}
	-> tail (monoidsum vs) = monoidsum (map tail vs)
tailOfSumIsSumOfTails {vs=[]} = Refl
tailOfSumIsSumOfTails {vs=v::vs} =
	trans ( cong {f=tail} monoidrec2D )
	$ trans ( lemma_VectAddTail _ _ )
	$ trans ( cong {f=(<+>) (tail v)} $ tailOfSumIsSumOfTails {vs=vs} )
	$ sym $ monoidrec2D



total
dotproductRewrite : {v : Vect _ ZZ} -> v <:> w = monoidsum (zipWith (<.>) v w)
dotproductRewrite = Refl



{-
Central theorems:
* timesVectMatAsLinearCombo
* timesMatMatAsMultipleLinearCombos
-}



timesMatMatAsTVecMat_EntryChariz : (vs : Matrix (S n') n ZZ) -> (xs : Matrix n w ZZ) -> Data.Vect.head (vs <> xs) = (Data.Vect.head vs) <\> xs
timesMatMatAsTVecMat_EntryChariz vs [] = ?timesMatMatAsTVecMat_EntryCharizTriv
timesMatMatAsTVecMat_EntryChariz vs (xx::xxs) = ?timesMatMatAsTVecMat_EntryChariz'

timesMatMatAsTVecMat_EntryCharizTriv = proof
  intros
  rewrite sym $ headtails vs
  rewrite sym $ zeroVecVecId vs
  exact Refl

timesMatMatAsTVecMat_EntryChariz' = proof
  intros
  rewrite sym $ headtails vs
  exact Refl



total
zippyLemA : (the (Vect 0 ZZ) []) <\> (the (Matrix 0 w ZZ) []) = replicate w (Pos 0)
zippyLemA {w = Z} = Refl
zippyLemA {w = S n} = cong (zippyLemA {w=n})

total
zippyLemB : replicate w (Pos 0) = monoidsum (zipWith (<#>) (the (Vect 0 ZZ) []) (the (Matrix 0 w ZZ) []))
zippyLemB {w = Z} = Refl
zippyLemB {w = S n} = cong (zippyLemB {w=n})



timesVectMatAsLinearCombo_EntryCharizLeft : (v : Vect n ZZ) -> (xs : Matrix n (S predw) ZZ) -> head (v <\> xs) = monoidsum $ zipWith (*) v (map head xs)
timesVectMatAsLinearCombo_EntryCharizLeft [] [] = Refl
-- Order of definitions issue - below line should be uncommented, line below it eliminated along with proof, and this whole section moved below the definition of timesVectMatAsHeadTail_ByTransposeElimination, requiring many declarations to move.
-- timesVectMatAsLinearCombo_EntryCharizLeft (vv::vvs) (xx::xxs) = cong {f=head} $ timesVectMatAsHeadTail_ByTransposeElimination {scals=(vv::vvs)} {vects=(xx::xxs)}
timesVectMatAsLinearCombo_EntryCharizLeft (vv::vvs) (xx::xxs) = ?timesVectMatAsLinearCombo_EntryCharizLeft'

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
reduceMultUnderHeadTo1D {n=Z} {vv} {xx}
	= vecHeadtailsEq (headMapChariz {xs=xx}) zeroVecEq
reduceMultUnderHeadTo1D {n=S predn} {vv} {xx} {vvs} {xxs}
	= vecHeadtailsEq (headMapChariz {f=multZ vv} {xs=xx})
	$ rewrite headtails vvs in rewrite headtails xxs in
	reduceMultUnderHeadTo1D {vv=head vvs} {vvs=tail vvs} {xx=head xxs} {xxs=tail xxs}

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
rewriteZipWithUnderTail {scals=[]} {vects=[]} = Refl
rewriteZipWithUnderTail {scals=z::zs} {vects=v::vs}
	= vecHeadtailsEq
		(rewrite headtails v in Refl)
	$ rewriteZipWithUnderTail {scals=zs} {vects=vs}

compressMonoidsum_lem3 : {n : Nat} -> {scals : Vect n ZZ} -> {predw : Nat} -> {vects : Vect n (Vect (S predw) ZZ)} -> monoidsum ( zipWith (<#>) scals (map Data.Vect.tail vects) ) = tail $ monoidsum ( zipWith (<#>) scals vects )
compressMonoidsum_lem3 {predw=Z} {n} = zeroVecEq
compressMonoidsum_lem3 {predw=S predpredw} {n=Z} = ?compressMonoidsum_lem3_rhs_majZ
compressMonoidsum_lem3 {predw=S predpredw} {n=S predn} {scals} {vects} = trans (cong {f=monoidsum} $ sym rewriteZipWithUnderTail) (sym tailOfSumIsSumOfTails)

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



timesVectMatAsLinearCombo_EntryCharizLeft' = proof
  intros
  exact cong {f=head} $ timesVectMatAsHeadTail_ByTransposeElimination {scals=(vv::vvs)} {vects=(xx::xxs)}



timesVectMatAsLinearCombo :
	(v : Vect n ZZ) -> (xs : Matrix n w ZZ)
	-> ( v <\> xs = monoidsum (zipWith (<#>) v xs) )
timesVectMatAsLinearCombo [] [] = trans zippyLemA zippyLemB
timesVectMatAsLinearCombo zs xs {n=S predn} {w=Z} = zeroVecEq
timesVectMatAsLinearCombo zs xs {n=S predn} {w=S predw}
	= flip trans (compressMonoidsum {scals=zs} {vects=xs})
	$ trans (timesVectMatAsHeadTail_ByTransposeElimination {scals=zs} {vects=xs})
	$ vecHeadtailsEq dotproductRewrite
	$ timesVectMatAsLinearCombo zs (map Data.Vect.tail xs)



timesMatMatAsMultipleLinearCombos_EntryChariz : (vs : Matrix (S n') n ZZ) -> (xs : Matrix n w ZZ) -> Data.Vect.head (vs <> xs) = monoidsum $ zipWith (<#>) (Data.Vect.head vs) xs
timesMatMatAsMultipleLinearCombos_EntryChariz vs xs = rewrite sym (timesVectMatAsLinearCombo (head vs) xs) in (timesMatMatAsTVecMat_EntryChariz vs xs)

timesMatMatAsMultipleLinearCombos : (vs : Matrix n' n ZZ) -> (xs : Matrix n w ZZ) -> vs <> xs = map (\zs => monoidsum $ zipWith (<#>) zs xs) vs
timesMatMatAsMultipleLinearCombos [] xs = Refl
timesMatMatAsMultipleLinearCombos (v::vs) xs
	= trans ( headtails $ (v::vs)<>xs )
	$ vecHeadtailsEq ( timesMatMatAsMultipleLinearCombos_EntryChariz (v::vs) xs )
	$ timesMatMatAsMultipleLinearCombos vs xs



{-
* Prove the dot product is a bilinear map from (ZZ)-(Vect)s to (ZZ) (or at least, up to symmetry in the arguments).
* Prove ZZ matrices form an algebra. Should work for ring. Proof it's a ring follows from associativity of matrix multiplication for a commutative ground ring.
* Distributivities of matrix-matrix, vector-matrix, and matrix-vector multiplication over matrix addition and vector addition.
* Prove transposition is an antiendomorphism of multiplication for ZZ matrices, and an endomorphism of addition, hence an antiendomorphism of the matrix ring.
* Some Algebra.neutral is a zero element proofs.
* Prove scalar multiplication of the left factor in a vector- or matrix-matrix product
is the same as multiplying the product by the same scalar. (Note rel. to bilinearity)
-}



-- This & the mirrored statement form the theorem that the dot product is a bilinear map from vects to the scalar ring.
-- This would be better with binary cong / leibniz equality on the (<+>)s.
dotProductRightDistributesOverVectorPlus : (l, c, r : Vect n ZZ) -> (l<+>c)<:>r = (l<:>r)<+>(c<:>r)
dotProductRightDistributesOverVectorPlus [] [] [] = Refl
dotProductRightDistributesOverVectorPlus (l::ls) (c::cs) (r::rs) = trans monoidrec1D $
	trans (cong {f=(((l<+>c)<.>r) <+>)} $ dotProductRightDistributesOverVectorPlus ls cs rs)
	$ trans (cong {f=(<+>((ls<:>rs)<+>(cs<:>rs)))} $ ringOpIsDistributiveR_ZZ l c r)
	$ trans (doubleSumInnerSwap (l<.>r) (c<.>r) (ls<:>rs) (cs<:>rs))
	$ rewrite monoidrec1D {v=l<.>r} {vs=zipWith (<.>) ls rs} in rewrite monoidrec1D {v=c<.>r} {vs=zipWith (<.>) cs rs} in Refl

dotProductLeftDistributesOverVectorPlus : (l, c, r : Vect n ZZ) -> l<:>(c<+>r) = (l<:>c)<+>(l<:>r)
dotProductLeftDistributesOverVectorPlus [] [] [] = Refl
dotProductLeftDistributesOverVectorPlus (l::ls) (c::cs) (r::rs) = trans monoidrec1D $
	trans (cong {f=((l<.>(c<+>r)) <+>)} $ dotProductLeftDistributesOverVectorPlus ls cs rs)
	$ trans (cong {f=(<+>((ls<:>cs)<+>(ls<:>rs)))} $ ringOpIsDistributiveL_ZZ l c r)
	$ trans (doubleSumInnerSwap (l<.>c) (l<.>r) (ls<:>cs) (ls<:>rs))
	$ rewrite monoidrec1D {v=l<.>r} {vs=zipWith (<.>) ls rs} in rewrite monoidrec1D {v=l<.>c} {vs=zipWith (<.>) ls cs} in Refl

matrixMultLeftDistributesOverVectorPlus : (l : Matrix n m ZZ) -> (c, r : Vect m ZZ) -> l</>(c<+>r) = (l</>c)<+>(l</>r)
matrixMultLeftDistributesOverVectorPlus [] c r = Refl
matrixMultLeftDistributesOverVectorPlus (x::xs) c r = vecHeadtailsEq (dotProductRightDistributesOverVectorPlus c r x) $ matrixMultLeftDistributesOverVectorPlus xs c r

matrixMultRightDistributesOverVectorPlus : (l, c : Vect n ZZ) -> (r : Matrix n m ZZ) -> (l<+>c)<\>r = (l<\>r)<+>(c<\>r)
matrixMultRightDistributesOverVectorPlus l c r = matrixMultLeftDistributesOverVectorPlus (transpose r) l c

matrixAddEntrywise : (x, y : Matrix n m ZZ)
	-> (i : Fin n) -> (j : Fin m)
	-> indices i j (x<+>y) = (indices i j x)<+>(indices i j y)
matrixAddEntrywise [] [] i j = FinZElim i
matrixAddEntrywise (x::xs) (y::ys) FZ j = lemma_VectAddEntrywise j x y
matrixAddEntrywise (x::xs) (y::ys) (FS preli) j = matrixAddEntrywise xs ys preli j

{-
DISPLACED TO BE DEPENDED ON SOONER:

* lemma_VectAddHead
* matrixAddHead
* lemma_VectAddTail
* matrixAddTail

Related:
* headOfSumIsSumOfHeads
* tailOfSumIsSumOfTails
-}

matrixAddMapHead : (x, y : Matrix n (S predm) ZZ) -> map Vect.head $ x<+>y = (map Vect.head x)<+>(map Vect.head y)
matrixAddMapHead [] [] = Refl
matrixAddMapHead (x::xs) (y::ys) = vecHeadtailsEq (lemma_VectAddHead x y) $ matrixAddMapHead xs ys

matrixAddMapTail : (x, y : Matrix n (S predm) ZZ) -> map Vect.tail $ x<+>y = (map Vect.tail x)<+>(map Vect.tail y)
matrixAddMapTail [] [] = Refl
matrixAddMapTail (x::xs) (y::ys) = vecHeadtailsEq (lemma_VectAddTail x y) $ matrixAddMapTail xs ys

matrixTransposeEndoMatrixPlus : (x, y : Matrix n m ZZ) -> transpose (x<+>y) = (transpose x)<+>(transpose y)
matrixTransposeEndoMatrixPlus x y = vecIndexwiseEq
	$ \i => vecIndexwiseEq
		$ \j => trans (transposeIndicesChariz j i)
			$ trans (matrixAddEntrywise x y j i)
			$ trans (cong {f=(<+>(indices j i y))}
				$ sym $ transposeIndicesChariz j i)
			$ trans (cong {f=((indices i j $ transpose x)<+>)}
				$ sym $ transposeIndicesChariz j i)
			$ sym $ matrixAddEntrywise (transpose x) (transpose y) i j

vectorTimesLeftDistributesOverMatrixPlus : (l : Vect n ZZ) -> (c, r : Matrix n m ZZ)
	-> l<\>(c<+>r) = (l<\>c)<+>(l<\>r)
vectorTimesLeftDistributesOverMatrixPlus {m=Z} l c r = zeroVecEq
vectorTimesLeftDistributesOverMatrixPlus {m=S predm} l c r =
	trans (timesVectMatAsHeadTail_ByTransposeElimination {scals=l} {vects=c<+>r})
	$ trans (vecHeadtailsEq (cong {f=(l<:>)} $ matrixAddMapHead c r) $ cong {f=(l<\>)} $ matrixAddMapTail c r)
	$ trans (vecHeadtailsEq (dotProductLeftDistributesOverVectorPlus l (map head c) (map head r)) $ vectorTimesLeftDistributesOverMatrixPlus l (map tail c) (map tail r))
	$ trans (cong $ sym $ timesVectMatAsHeadTail_ByTransposeElimination {scals=l} {vects=r})
	$ cong {f=(<+>(l<\>r))} $ sym $ timesVectMatAsHeadTail_ByTransposeElimination {scals=l} {vects=c}

{-
-- Equational reasoning vrsn
	l<\>(c<+>r)    ={ timesVectMatAsHeadTail_ByTransposeElimination {scals=l} {vects=c<+>r} }=
	(l <:> map head (c<+>r))::(l<\>map tail (c<+>r)) ={ vecHeadtailsEq (cong {f=(l<:>)} $ matrixAddMapHead c r) (cong {f=(l<\>)} $ matrixAddMapTail c r) }=
	(l <:> ((map head c)<+>(map head r)))::(l<\>((map tail c)<+>(map tail r))) ={ vecHeadtailsEq (dotProductLeftDistributesOverVectorPlus l (map head c) ( map head r)) $ vectorTimesLeftDistributesOverMatrixPlus l (map tail c) (map tail r) }=
	( (l<:>(map head c))::(l<\>(map tail c)) ) <+> ( (l<:>(map head r)) :: (l<\>(map tail r)) )    ={ cong $ sym $ timesVectMatAsHeadTail_ByTransposeElimination {scals=l} {vects=r} }=
	( (l<:>(map head c))::(l<\>(map tail c)) ) <+> ( l<\>r )    ={ cong {f=(<+>(l<\>r))} $ sym $ timesVectMatAsHeadTail_ByTransposeElimination {scals=l} {vects=c} }=
	(l<\>c)<+>(l<\>r)
	qed
-}

matrixMultRightDistributesOverMatrixPlus : (l, c : Matrix n k ZZ) -> (r : Matrix k m ZZ) -> (l<+>c)<>r = (l<>r)<+>(c<>r)
matrixMultRightDistributesOverMatrixPlus [] [] r = zeroVecEq
matrixMultRightDistributesOverMatrixPlus (l::ls) (c::cs) r = vecHeadtailsEq
	(matrixMultRightDistributesOverVectorPlus l c r)
	$ matrixMultRightDistributesOverMatrixPlus ls cs r

{-
Could use (matrixTransposeAntiendoMatrixMult) to avoid repeating the proof, but
that assumes the ring is commutative, so that prevents future full generality.
-}
matrixMultLeftDistributesOverMatrixPlus : (l : Matrix n k ZZ) -> (c, r : Matrix k m ZZ) -> l<>(c<+>r) = (l<>c)<+>(l<>r)
matrixMultLeftDistributesOverMatrixPlus [] c r = Refl
matrixMultLeftDistributesOverMatrixPlus (l::ls) c r = vecHeadtailsEq (vectorTimesLeftDistributesOverMatrixPlus l c r) $ matrixMultLeftDistributesOverMatrixPlus ls c r



-- Further interactions with the transpose
-- The below are true if and only if the ring is commutative.

dotProductCommutative : (x, y : Vect n ZZ) -> x<:>y = y<:>x
dotProductCommutative [] [] = Refl
dotProductCommutative (x::xs) (y::ys) = trans monoidrec1D
	$ trans (cong {f=(<+>(xs<:>ys))} $ ringOpIsCommutative_ZZ x y)
	$ trans (cong {f=((y<.>x)<+>)} $ dotProductCommutative xs ys)
	$ sym $ monoidrec1D

matrixTransposeAntiendoMatrixMult : (x : Matrix n k ZZ) -> (y : Matrix k m ZZ) -> transpose (x<>y) = (transpose y)<>(transpose x)
matrixTransposeAntiendoMatrixMult x y = vecIndexwiseEq
	$ \i => vecIndexwiseEq
		$ \j => trans (transposeIndicesChariz j i)
			$ trans (cong {f=index i} $ indexMapChariz {k=j} {xs=x} {f=((transpose y)</>)})
			$ trans indexMapChariz
			$ trans (dotProductCommutative _ _)
			$ trans (sym $ indexMapChariz {k=j} {f=((index i (transpose y))<:>)} {xs=x})
			$ trans (cong {f=index j} $ matVecMultIsVecTransposeMult (index i $ transpose y) x)
			$ cong {f=index j} $ sym $ indexMapChariz {k=i} {f=(<\>(transpose x))} {xs=transpose y}

{-
-- Equational reasoning vrsn (not formatted in the syntax for that, though)
matrixTransposeAntiendoMatrixMult x y = vecIndexwiseEq
	$ \i => vecIndexwiseEq
		$ \j => trans (transposeIndicesChariz j i)
			$ trans (cong {f=index i} indexMapChariz) -- ((x!j)<\>y)!i
				-- === ((transpose y)</>(x!j))!i
			$ trans indexMapChariz
				-- (index j x)<:>(index i $ transpose y)
			$ trans (dotProductCommutative _ _)
				-- (index i $ transpose y)<:>(index j x)
			$ trans (sym $ indexMapChariz {k=j} {f=((index i $ transpose y)<:>)} {xs=x})
				-- index j $ map ((index i $ transpose y)<:>) x
				-- === index j $ x</>(index i $ transpose y)
			$ trans (cong {f=index j} $ matVecMultIsVecTransposeMult (index i $ transpose y) x)
				-- index j $ (index i $ transpose y)<\>(transpose x)
			$ trans (cong {f=index j} $ sym $ indexMapChariz {k=i} {f=(<\>(transpose x))} {xs=transpose y})
				-- index j $ index i $ map (<\> (transpose x)) (transpose y)
-}



{-
dotCancelsHeadWithLeadingZeroL : VerifiedRing a => (x, y : Vect n a) -> (Algebra.neutral::x)<:>(r::y) = x<:>y
dotCancelsHeadWithLeadingZeroL x y {r} = trans (monoidrec (Algebra.neutral<.>r) $ zipWith (<.>) x y)
	$ trans (cong {f=((Algebra.neutral<.>r)<+>)} ?dotcancelsLpatch) -- something like dotproductRewrite, up to sym
	$ trans (cong {f=(<+> (x<:>y))} $ ringNeutralIsMultZeroL r)
	$ monoidNeutralIsNeutralR $ x<:>y

dotCancelsHeadWithLeadingZeroR : VerifiedRing a => (x, y : Vect n a) -> (r::x)<:>(Algebra.neutral::y) = x<:>y
-}

dotCancelsHeadWithLeadingZeroL : (x, y : Vect n ZZ) -> (Algebra.neutral::x)<:>(r::y) = x<:>y
dotCancelsHeadWithLeadingZeroL x y {r} = trans monoidrec1D
	$ trans (cong {f=(<+> (x<:>y))} $ ringNeutralIsMultZeroL r)
	$ monoidNeutralIsNeutralR $ x<:>y

dotCancelsHeadWithLeadingZeroR : (x, y : Vect n ZZ) -> (r::x)<:>(Algebra.neutral::y) = x<:>y
dotCancelsHeadWithLeadingZeroR x y {r} = trans monoidrec1D
	$ trans (cong {f=(<+> (x<:>y))} $ ringNeutralIsMultZeroR r)
	$ monoidNeutralIsNeutralR $ x<:>y

neutralVectIsDotProductZero_L : (x : Vect nu ZZ) -> Algebra.neutral <:> x = Algebra.neutral
neutralVectIsDotProductZero_L [] = Refl
neutralVectIsDotProductZero_L (x::xs) = trans (dotCancelsHeadWithLeadingZeroL Algebra.neutral xs) $ neutralVectIsDotProductZero_L xs

{-
-- Mixture of instance problems and problem generalizing (dotCancelsHeadWithLeadingZeroR).

neutralVectIsDotProductZero_R : VerifiedRing a => (x : Vect n a) -> x<:>Algebra.neutral = Algebra.neutral {a=a}
neutralVectIsDotProductZero_R [] = ?neutralVectIsDotProductZero_R_ReflCase
neutralVectIsDotProductZero_R (x::xs) = trans (dotCancelsHeadWithLeadingZeroR xs Algebra.neutral) $ neutralVectIsDotProductZero_R xs
-}

neutralVectIsDotProductZero_R : (x : Vect nu ZZ) -> x <:> Algebra.neutral = Algebra.neutral
neutralVectIsDotProductZero_R [] = Refl
neutralVectIsDotProductZero_R (x::xs) = trans (dotCancelsHeadWithLeadingZeroR xs Algebra.neutral) $ neutralVectIsDotProductZero_R xs

neutralVectIsVectTimesZero : (x : Matrix nu mu ZZ) -> Algebra.neutral <\> x = Algebra.neutral
neutralVectIsVectTimesZero xs {mu=Z} = zeroVecEq
neutralVectIsVectTimesZero xs {mu=S predmu} = trans timesVectMatAsHeadTail_ByTransposeElimination
	$ vecHeadtailsEq
		(neutralVectIsDotProductZero_L $ map head xs)
		$ neutralVectIsVectTimesZero $ map tail xs

emptyVectIsTimesVectZero : (x : Matrix nu Z ZZ) -> x</>[] = Algebra.neutral
emptyVectIsTimesVectZero [] = Refl
emptyVectIsTimesVectZero (x::xs) = vecHeadtailsEq (neutralVectIsDotProductZero_L x)
	$ emptyVectIsTimesVectZero xs

neutralMatIsMultZeroL : (x : Matrix nu mu ZZ) -> Algebra.neutral <> x = Algebra.neutral
neutralMatIsMultZeroL x = vecIndexwiseEq $ \i => trans indexMapChariz $ trans (cong {f=(<\>x)} indexReplicateChariz) $ trans (neutralVectIsVectTimesZero x) $ sym $ indexReplicateChariz

matMultCancelsHeadWithZeroColExtensionL : (map ((Pos 0)::) xs)<>(z::ys) = xs<>ys
matMultCancelsHeadWithZeroColExtensionL {xs} {ys} {z} = vecIndexwiseEq
	$ \i => vecIndexwiseEq
		$ \j => trans (matMultIndicesChariz {l=map ((Pos 0)::) xs} {r=z::ys})
			$ trans (cong {f=(<:>(getCol j $ z::ys))} indexMapChariz)
			$ trans (dotCancelsHeadWithLeadingZeroL {r=index j z} (index i xs) (getCol j ys))
			$ sym $ matMultIndicesChariz {l=xs} {r=ys}

timesPreservesLeadingZeroExtensionR : xs<>(map ((Pos 0)::) ys) = map ((Pos 0)::) $ xs<>ys
timesPreservesLeadingZeroExtensionR {xs} {ys} = vecIndexwiseEq $ \i => vecIndexwiseEq $ \j => filmy i j
	where
		filmy : (i : _) -> (j : _) -> indices i j $ xs<>(map ((Pos 0)::) ys) = indices i j $ map ((Pos 0)::) $ xs<>ys
		filmy i FZ = trans matMultIndicesChariz
			$ trans (cong {f=((index i xs)<:>)} $ leadingElemExtensionFirstColReplicate $ Pos 0)
			$ trans (neutralVectIsDotProductZero_R $ index i xs)
			$ sym $ cong {f=index FZ} $ indexMapChariz {f=((Pos 0)::)}
		filmy i (FS prelj) = trans matMultIndicesChariz
			$ trans (cong {f=((index i xs)<:>)} leadingElemExtensionColFSId)
			$ trans (sym $ matMultIndicesChariz)
			$ sym $ cong {f=index $ FS prelj} $ indexMapChariz {f=((Pos 0)::)}



{-
-- Type mismatch due to instance mismatch b-n
--   (<.>) {{(@@constructor of Classes.Verified.VerifiedRing#Ring a) constrarg}}
-- and
--   (<.>) {{(@@constructor of Control.Algebra.RingWithUnity#Ring a) constrarg1}}
-- Also tried (VerifiedRingWithUnity a =>)
scaledNeutralIsNeutral : (VerifiedRing a, RingWithUnity a) =>
	{m : Nat}
	-> (z : a)
	-> z<#>(the (Vect m a) Algebra.neutral) = Algebra.neutral
scaledNeutralIsNeutral _ {m=Z} = Refl
scaledNeutralIsNeutral z {m=S predm} = vecHeadtailsEq (ringNeutralIsMultZeroR z)
	$ scaledNeutralIsNeutral z {m=predm}
-}

scaledNeutralIsNeutral_zz : {m : Nat}
	-> (z : ZZ)
	-> z<#>(the (Vect m ZZ) Algebra.neutral) = Algebra.neutral
scaledNeutralIsNeutral_zz _ {m=Z} = Refl
scaledNeutralIsNeutral_zz z {m=S predm} = vecHeadtailsEq (ringNeutralIsMultZeroR z)
	$ scaledNeutralIsNeutral_zz z {m=predm}

vectVectLScalingCompatibility : {z : ZZ} -> (z<#>l)<:>r = z<.>(l<:>r)
vectVectLScalingCompatibility {z} {l=[]} {r=[]} = sym $ ringNeutralIsMultZeroR z
vectVectLScalingCompatibility {z} {l=l::ls} {r=r::rs} =
	trans (dotproductRewrite {v=z<#>(l::ls)} {w=r::rs})
	$ trans (cong {f=monoidsum} $ vecHeadtailsEq (sym $ ringOpIsAssociative z l r) Refl)
	$ trans monoidrec1D
	$ trans (cong {f=((z<.>(l<.>r))<+>)}
		$ trans (sym $ dotproductRewrite {v=z<#>ls} {w=rs})
		$ (vectVectLScalingCompatibility {z=z} {l=ls} {r=rs}))
	$ trans (sym $ ringOpIsDistributiveL z (l<.>r) (ls<:>rs))
	-- z<.>(l<.>r <+> ls<:>rs)
	$ cong {f=(z<.>)}
	$ trans (cong {f=((l<.>r)<+>)} $ dotproductRewrite {v=ls} {w=rs})
	-- (l<.>r)<+>(monoidsum $ zipWith (<.>) ls rs)
	$ trans (sym monoidrec1D)
	$ sym $ dotproductRewrite {v=l::ls} {w=r::rs}

-- Note the relationship to bilinearity of matrix multiplication
vectMatLScalingCompatibility : {z : ZZ} -> {rs : Matrix k m ZZ} -> (z <#> la) <\> rs = z <#> (la <\> rs)
vectMatLScalingCompatibility {z} {la=[]} {rs=[]} =
	trans zippyLemA
	$ sym $ trans (cong {f=(z<#>)} zippyLemA)
	$ scaledNeutralIsNeutral_zz z
vectMatLScalingCompatibility {z} {la=l::la} {rs=r::rs} {m=Z} = zeroVecEq
-- vectMatLScalingCompatibility {z} {la=l::la} {rs=r::rs} {m=S predm} = ?vMLSC_rhs_2
vectMatLScalingCompatibility {z} {la=l::la} {rs=r::rs} {m=S predm} =
	trans (timesVectMatAsHeadTail_ByTransposeElimination
		{scals=z<#>(l::la)} {vects=r::rs})
	$ trans ( vecHeadtailsEq
			(vectVectLScalingCompatibility {z=z} {l=l::la} {r=map head $ r::rs})
			$ vectMatLScalingCompatibility {z=z}
				{la=l::la} {rs=map tail $ r::rs} )
	$ sym $ cong {f=(z<#>)} $ timesVectMatAsHeadTail_ByTransposeElimination
		{scals=l::la} {vects=r::rs}

matMatLScalingCompatibility :
	(scal : ZZ)
	-> (xs : Matrix n k ZZ)
	-> (ys : Matrix k m ZZ)
	-> (scal <#> xs) <> ys = scal <#> (xs <> ys)
matMatLScalingCompatibility _ [] _ = zeroVecEq
matMatLScalingCompatibility scal (x::xs) ys = vecHeadtailsEq
	vectMatLScalingCompatibility
	$ matMatLScalingCompatibility scal xs ys



{-
Type mismatch between

	(<.>) {{(@@constructor of Classes.Verified.VerifiedRing#Ring a)
		(@@constructor of Classes.Verified.VerifiedRingWithUnity#VerifiedRing a)}}
		neutral
		x =
	neutral (Type of ringNeutralIsMultZeroL x)

and

	(<.>) {{(@@constructor of Control.Algebra.RingWithUnity#Ring a)
		(@@constructor of Classes.Verified.VerifiedRingWithUnity#RingWithUnity a)}}
		neutral
		x =
	neutral (Expected type)

---

neutralScalarIsScalarMultNeutral_Vect : VerifiedRingWithUnity a => (xs : Vect n a)
	-> (the a Algebra.neutral)<#>xs = Algebra.neutral
neutralScalarIsScalarMultNeutral_Vect [] = Refl
neutralScalarIsScalarMultNeutral_Vect (x::xs) = vecHeadtailsEq
	(ringNeutralIsMultZeroL x)
	$ neutralScalarIsScalarMultNeutral_Vect xs
-}

neutralScalarIsScalarMultNeutral_zzVect : (xs : Vect n ZZ)
	-> (the ZZ Algebra.neutral)<#>xs = Algebra.neutral
neutralScalarIsScalarMultNeutral_zzVect [] = Refl
neutralScalarIsScalarMultNeutral_zzVect (x::xs) = vecHeadtailsEq
	(ringNeutralIsMultZeroL x)
	$ neutralScalarIsScalarMultNeutral_zzVect xs

-- Can prove for arbitrary module by showing the LHS is its own double by distributivity
-- groupElemOwnDoubleImpliesNeut
neutralScalarIsScalarMultNeutral_zzMat : (xs : Matrix n m ZZ)
	-> (the ZZ Algebra.neutral)<#>xs = Algebra.neutral
neutralScalarIsScalarMultNeutral_zzMat [] = Refl
neutralScalarIsScalarMultNeutral_zzMat (x::xs) = vecHeadtailsEq
	(neutralScalarIsScalarMultNeutral_zzVect x)
	$ neutralScalarIsScalarMultNeutral_zzMat xs

vectTimesNegOneIsNeg_zz : (xs : Vect n ZZ)
	-> (Algebra.inverse $ the ZZ $ Algebra.unity) <#> xs = Algebra.inverse xs
vectTimesNegOneIsNeg_zz xs = groupOpIsCancellativeR_Vect _ _ xs
	$ trans (cong {f=(((Algebra.inverse $ Algebra.unity {a=ZZ}) <#> xs)<+>)}
		$ sym $ moduleScalarUnityIsUnity_Vect {ok=Refl} xs)
	$ trans (sym $ moduleScalarMultDistributiveWRTModuleAddition_Vect {ok=Refl}
		(Algebra.inverse $ Algebra.unity {a=ZZ}) (Algebra.unity {a=ZZ}) xs)
	$ trans (cong {f=(<#>xs)} $ groupInverseIsInverseR $ Algebra.unity {a=ZZ})
	$ trans (neutralScalarIsScalarMultNeutral_zzVect xs)
	$ sym $ groupInverseIsInverseR_Vect xs

matTimesNegOneIsNeg_zz : (xs : Matrix n m ZZ)
	-> (Algebra.inverse $ the ZZ $ Algebra.unity) <#> xs = Algebra.inverse xs
matTimesNegOneIsNeg_zz xs = groupOpIsCancellativeR _ _ xs
	$ trans (cong {f=(((Algebra.inverse $ Algebra.unity {a=ZZ}) <#> xs)<+>)}
		$ sym $ moduleScalarUnityIsUnity_Mat {a=ZZ} xs)
	$ trans (sym $ moduleScalarMultDistributiveWRTModuleAddition_Mat
		(Algebra.inverse $ Algebra.unity {a=ZZ}) (Algebra.unity {a=ZZ}) xs)
	$ trans (cong {f=(<#>xs)} $ groupInverseIsInverseR $ Algebra.unity {a=ZZ})
	$ trans (neutralScalarIsScalarMultNeutral_zzMat xs)
	$ sym $ groupInverseIsInverseR xs

{-
When checking type of ZZModuleSpan.negScalarToScaledNeg:
When checking an application of function Control.Algebra.VectorSpace.<#>:
        Can't resolve type class Group r

---

negScalarToScaledNeg : (VerifiedRingWithUnity r, VerifiedModule r a) -> (s : r) -> (x : a) -> (inverse s) <#> x = s <#> (inverse x)

-----

We require generalizations to other rings for:

	neutralScalarIsScalarMultNeutral_zzVect
	neutralScalarIsScalarMultNeutral_zzMat

	vectTimesNegOneIsNeg_zz
	matTimesNegOneIsNeg_zz

---

negScalarToScaledNegVect : VerifiedRingWithUnity r => (s : r) -> (x : Vect _ r) -> (inverse s) <#> x = s <#> (inverse x)

negScalarToScaledNegMat : VerifiedRingWithUnity r => (s : r) -> (x : Matrix _ _ r) -> (inverse s) <#> x = s <#> (inverse x)
-}

negScalarToScaledNegVect_zz : (s : ZZ)
	-> (x : Vect _ ZZ)
	-> (inverse s) <#> x = s <#> (inverse x)
negScalarToScaledNegVect_zz s x =
	trans (cong {f=(<#>x)}
		$ trans (negativeIsNegOneTimesRight s) $ ringOpIsCommutative_ZZ _ s)
	$ trans (sym $ moduleScalarMultiplyComposition_Vect s _ x)
	$ cong {f=(s<#>)} $ vectTimesNegOneIsNeg_zz x

negScalarToScaledNegMat_zz : (s : ZZ)
	-> (x : Matrix _ _ ZZ)
	-> (inverse s) <#> x = s <#> (inverse x)
negScalarToScaledNegMat_zz s x =
	trans (cong {f=(<#>x)}
		$ trans (negativeIsNegOneTimesRight s) $ ringOpIsCommutative_ZZ _ s)
	$ trans (sym $ moduleScalarMultiplyComposition_Mat s _ x)
	$ cong {f=(s<#>)} $ matTimesNegOneIsNeg_zz x
