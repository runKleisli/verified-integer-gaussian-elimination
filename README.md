# verified-integer-gaussian-elimination

[![bountysource](https://img.shields.io/bountysource/team/verified-integer-gaussian-elimination/activity.svg "bountysource (salt)")](https://www.bountysource.com/teams/verified-integer-gaussian-elimination) Funded through [Bountysource (salt)](https://salt.bountysource.com/teams/verified-integer-gaussian-elimination) by [viewers like you](../master/Backers.md).

Written in Idris 0.9.20

Idris package looking to define, implement, and verify naiive Gaussian elimination over the integers in some system of linear algebra.

Ignore these files:
* BezoutsIdentity.idr
* IntegerArith.idr
* IntegerGroupTheory.idr
* IntegerOrdering.idr

These show what other kind of theorems are needed, but about the wrong objects to be correct or to fit the system of linear algebra used in this package.

__All proofs mentioned below are up to Issue #24 on GitHub being solved__

## ZZGaussianEliminationRedo

Main elimination algorithms.

Mostly complete:
Expressed in terms of an unimplemented "GCD of vector" algorithm to be implemented in terms of a verified GCD.
Some cases are still missing.
Some theorems it depends on are unproved, things like basic facts about finite sets and Issue #24.
Mostly total, where implemented, but for a mutual recursion in proofs regarding the properties of linear combination.

Index:
* Template & usage for do notation pattern matching technique
* elimFirstCol
* gaussElimlzIfGCD3
* Appendix Elim.General.Meta

Replaces (ZZGaussianElimination), under conjunction with satellite modules.

Satellite modules are:
* ZZGaussianEliminationLemmas
* RowEchelon
* ZZDivisors
* ZZGaussianEliminationRedoNoMonad
  Implementation of (elimFirstCol) without using the do notation dependent pattern matching technique.

## ZZGaussianEliminationLemmas

Table of Contents:
* The induction algorithm used to verify first-column elimination
* Nice things for elimination algorithms to talk about
* Preliminary arguments to (elimFirstCol)

Guide:
Structure of (elimFirstCol):
succImplWknStep_Qfunclemma => succImplWknStep_stepQfunc => succImplWknStep_unplumbed => succImplWknStep => foldedFully
(mkQfunc, foldedFully) => elimFirstCol (after some work)

## RowEchelon

A library for making inferences about when the row echelon property holds for a matrix.

`rowEchelon xs`, equal to `forall i. echTy xs i`, is what corresponds to the real life row echelon property of the matrix `xs`. However, this is not the suitable form for verifying it recursively, and instead `toRowEchelon` is used to prove it from a `rowEchelonPre xs`, which is a `forall i. echPreTy xs i`.

Table of contents:
* ZZ proofs
* Fin proofs
* Vect/Matrix proofs
* The leading nonzero of a vector
* DANRZ property
* Corollary bispannability property
* Row echelon properties

## ZZDivisors

* An integer divisibility relation `quotientOverZZ` & its properties
* Interactions between integer divisibility and linear combinations

## ZZGaussianElimination

__ DEPRECATED : See ZZGaussianEliminationRedo __

Contents:
* Declaration of gaussian elimination as an algorithm which converts a matrix into one in row echelon form which spans it. `gaussElimlz : (xs : Matrix n m ZZ) -> (n' : Nat ** (gexs : Matrix n' m ZZ ** (rowEchelon gexs, bispanslz gexs xs)))`
	* Actual implementation ```gaussElimlzIfGCD2 : (xs : Matrix n (S predm) ZZ)
	-> Reader ZZGaussianElimination.gcdOfVectAlg
		( n' : Nat ** (gexs : Matrix n' (S predm) ZZ
			** (rowEchelon gexs, gexs `bispanslz` xs)) )``` for matrices with at least one column. Note that a `Reader a b` is just a wrapped `a -> b`. __Proof calculated depends on__ `echelonHeadnonzerovecExtension`__, which is false.__ The suggested modification to that proposition is compatible w/ the current algorithm's structure.
	* First-column elimination, `elimFirstCol`, in particular.
* `rowEchelon`, the first property. (the other is from ZZModuleSpan)
* Inference rules for `rowEchelon`
	* Implemented: `echelonFromDanrzLast` w/c says that a matrix w/c is zero off the top row is row echelon.
	* Declared: `echelonNullcolExtension : rowEchelon xs -> rowEchelon $ map ((Pos 0)::) xs`. Note that `map ((Pos 0)::)` appends the integer 0 to the start of each row of a matrix.
	* Declared __(FALSE)__: `echelonHeadnonzerovecExtension` w/c says that a row-echelon matrix can have a new row added with first entry nonzero to get a row-echelon matrix. __The new row should be appended to the null-column-appended original matrix.__
* `downAndNotRightOfEntryImpliesZ` (referred to as _danrz_), the property of a matrix and a pair of indices to it of the matrix being zero on the submatrix w/ topright corner just below the entry given by the indices. The row-echelon property is built of from many of these w/ the indices generally being to the leading (first) nonzero entries of each row.
* Inference rules for _danrz_
	* `danrzLastcolImpliesAllcol` — If _danrz_ holds for the topright corner, it holds for any entry on the top row.
	* `danrzLastcolImpliesTailNeutral` — If _danrz_ holds for the topright corner, then the matrix is zero below the top row.
		* `danrzTailHasLeadingZeros` — If _danrz_ holds for the topright corner, then the matrix is zero in the first column of the submatrix w/out the top row.
* `leadingNonzeroCalc`, which takes a `Vect n ZZ` to its first index to a nonzero entry or a proof that all entries are zero. (See also: `leadingNonzeroIsFZIfNonzero`)
	* `danrzLeadingZeroAlt` — If _danrz_ holds for the topright corner, then the first column of the matrix is zero or the topleft corner is the leading nonzero entry of the top row.
* ```bispansNulltailcolExtension : downAndNotRightOfEntryImpliesZ (x::xs) FZ FZ
	-> ys `bispanslz` map Vect.tail xs
	-> map ((Pos Z)::) ys `bispanslz` xs```
* `foldAutoind` - A vector fold over suppressed indices. Extends one witness for some predicate `p : (m : Nat) -> Fin (S m) -> a -> Type` to a `Vect` of them.
* `foldAutoind2` - Same strength of result as `foldAutoind`, but applies where the predicate `p : (m : Nat) -> Fin (S m) -> (a m) -> Type` isn't naturally expressed or proved without affecting the type of the witnesses dealt with by this process.

Further contents concerning divisibility:
* `quotientOverZZ : ZZ -> ZZ -> Type`. ```x `quotientOverZZ` y``` reads "_x_ is a quotient of _y_". The opposite relation to "_a_ divides _b_". For those unfamiliar w/ type theory, an inhabitant of the type is a proof of the statement.
	* `quotientOverZZrefl`, `quotientOverZZreflFromEq`, `quotientOverZZtrans` for reflexivity and transitivity of the relation.
	* `divisorByDistrib`, `zipWithHeadsQuotientRelation`, `linearComboQuotientRelation`, `linearComboQuotientRelation_corrollary`
* `gcdOfVectAlg : Type` — any algorithm w/c produces a common divisor for a sequence of integers and a method of expressing the divisor as a linear combination of the entries in the sequence. When the divisor is their GCD, the existence of one proves `ZZ` is a Bézout domain.

...And foundations:
* `bileibniz : (f : a -> b -> c) -> (x1=x2) -> (y1=y2) -> f x1 y1 = f x2 y2` — indiscernability of identicals in two variables.
* `zzZOrOrPosNeg` — An integer is either zero (`= Pos 0`), positive (`= Pos (S k)`), or negative (`= NegS k`).
* `FinSZAreFZ : (x : Fin 1) -> x=FZ`
* `commuteFSWeaken : (i : Fin n) -> (FS $ weaken i = weaken $ FS i)`
* `notSNatLastLTEAnything`
* `finToNatWeaken : {k : Fin n} -> finToNat k = finToNat (weaken k)`
* `partitionNatWknLT` — For _p_ in \{1, ..., _n_\}, _k_ in \{1, ..., n+1\}, if `weaken` _p_ < _k_ then `FS` _p_ ≤ _k_.
* `splitFinS` : `last` and `weaken`ings of lower-order `Fin`s are the only `Fin`s.
* Other nonsense.

## ZZModuleSpan

Contents:

* Definition of the *linearly spans* relation `spanslz` between two `Vect`s of `Vect`s of integers (where integers means inhabitants of Data.ZZ).
	* Its maximal symmetric subrelation `bispanslz xs ys = (spanslz xs ys, spanslz ys xs)`.
* Def. `zippyScale`, shorthand for a form of linear combination of the rows of a matrix over multiple vectors, as proved extensionally equal to matrix multiplication by `timesMatMatAsMultipleLinearCombos` in Data.Matrix.LinearCombinations.
* `spans` and `spansl`, which reflect that the original scope of the project was to cover Gaussian elimination (or a similar basis-normalization procedure) for more general ZZ-modules, but will be deleted.

Proofs of relational properties of span:
* Proof of transitivity and reflexivity of `spanslz`: `spanslzrefl`, `spanslzreflFromEq : (xs=ys) -> xs `spanslz` ys`, `spanslztrans`.
	* Their analogues for `bispanslz`, plus proof `bispanslzsym` it's symmetric, and hence an equivalence relation.

Proofs of algebraic properties of span — elementary row operations of row-addition and row-multiplication, and properties of adding a multiple of one row to another row in particular:
* `spanScalelz : (z : ZZ) -> spanslz xs ys -> spanslz xs (z<#>ys)`
* `spanAdd : spanslz xs ys -> spanslz xs zs -> spanslz xs (ys <+> zs)`
	* `spanSub : spanslz xs ys -> spanslz xs zs -> spanslz xs (ys <-> zs)`
* `spanslzAdditiveExchange : spanslz ((y<+>(z<\>xs))::xs) (y::xs)`
	* `spanslzSubtractiveExchange : spanslz ((y<->(z<\>xs))::xs) (y::xs)`
* `spanslzAdditivePreservation : spanslz (y::xs) ((y<+>(z<\>xs))::xs)`
	* `spanslzSubtractivePreservation : spanslz (y::xs) ((y<->(z<\>xs))::xs)`
* `spanRowScalelz : (z : ZZ) -> (updi : Fin n') -> spanslz xs ys -> spanslz xs (updateAt updi (z<#>) ys)`, which applies `updateAtEquality` to `vectMatLScalingCompatibility : {z : ZZ} -> {rs : Matrix k m ZZ} -> (z <#> la) <\> rs = z <#> (la <\> rs)`.
* `bispanslzAdditiveExchangeAt : (nel : Fin (S predn)) -> bispanslz (updateAt nel (<+>(z<\>(deleteRow nel xs))) xs) xs`, which applies `headOpPreservesSpanslzImpliesUpdateAtDoes` and `headOpPreservesSpannedbylzImpliesUpdateAtDoes` to `spanslzAdditiveExchange` and `spanslzAdditivePreservation` respectively.
	* `bispanslzSubtractiveExchangeAt : (nel : Fin (S predn)) -> bispanslz (updateAt nel (<->(z<\>(deleteRow nel xs))) xs) xs`

Proofs of reordering/permutational properties — elementary row operation of row-switching:
* ```permPreservesSpanslz : (sigma : Iso (Fin n) (Fin n))
	-> {xs : Matrix n m ZZ}
	-> spanslz (vectPermTo sigma xs) xs``` — A permutation of a `Vect` of `Vect`s does not change its span.
* ```permPreservesSpannedbylz : (sigma : Iso (Fin n) (Fin n)) -> spanslz xs (vectPermTo sigma xs)``` — A permutation of a `Vect` of `Vect`s does not change its span.
* ```concatSpanslzFlipConcat : {xs : Matrix n k ZZ} -> {ys : Matrix m k ZZ}
	-> spanslz (xs++ys) (ys++xs)```
* ```updateAtEquality : {ls : Matrix n k ZZ} -> {rs : Matrix k m ZZ} -> (updi : Fin n)
	-> (f : (i : Nat) -> Vect i ZZ -> Vect i ZZ)
	-> ( (la : Vect k ZZ) -> (f k la) <\> rs = f m $ la <\> rs )
	-> zippyScale (updateAt updi (f k) ls) rs = updateAt updi (f m) (zippyScale ls rs)``` — reexpresses a product w/ an updated matrix as an update to the product w/ the un-updated matrix when a similar re-expression is valid for applying the updating function to an arbitrary vector under multiplication by the original non-updating matrix.
* `headOpPreservesSpanslzImpliesUpdateAtDoes` — if an operation `f` can be applied to the head of any matrix and not change what it spans, it can be applied to any row of any matrix and not change what it spans.
* `headOpPreservesSpannedbylzImpliesUpdateAtDoes` — if an operation `f` can be applied to the head of any matrix and not change what spans it, it can be applied to any row of any matrix and not change what spans it.

Proofs of mixed properties, such as those to do w/ the underlying `Vect` (list) structure's meaning in terms of subspaces:
* `spanslzNeutral : {xs : Matrix n w ZZ} -> spanslz xs Algebra.neutral` — every set of vectors spans the zero subspace (Zero matrix as terminal object P1)
	* ```spanslzHeadCatNeutral : x::xs `spanslz` x::Algebra.neutral```
	* `spanslzNullRowExtension : spanslz xs (Algebra.neutral::xs)`
* `spannedlzByZeroId : {xs : Matrix n m ZZ} -> spanslz [] xs -> xs=neutral` — the span of the zero matrix is the zero subspace (Zero matrix as terminal object P2)
	* ```spansImpliesSameFirstColNeutrality : xs `spanslz` ys -> getCol FZ xs = Algebra.neutral -> getCol FZ ys = Algebra.neutral```
* `spanslzRowTimesSelf : spanslz xs [v<\>xs]` — row-vector multiples of matrix are, as a 1-vector `Vect`, spanned by the matrix as a `Vect` of `Vect`s. Put another way, the value of a linear map at a vector is in the span of the image of the basis under the linear map.
	* ```spanslzHeadRow : (z : _) -> (zs : _) -> (z::zs) `spanslz` [z]```
* `spanslzTail : {xs : Matrix n w ZZ} -> {ys : Matrix (S predn') w ZZ} -> spanslz xs ys -> spanslz xs (Data.Vect.tail ys)`
* `extendSpanningLZsByPreconcatTrivially : spanslz xs ys -> spanslz (zs++xs) ys`
	* `preserveSpanningLZByCons : spanslz xs ys -> spanslz (z::xs) ys`
* `extendSpanningLZsByPostconcatTrivially : spanslz xs ys -> spanslz (xs++zs) ys`
* `mergeSpannedLZs : spanslz xs ys -> spanslz xs zs -> spanslz xs (ys++zs)`
* `concatSpansRellz : spanslz xs zs -> spanslz ys ws -> spanslz (xs++ys) (zs++ws)`
* ```bispansSamevecExtension : xs `bispanslz` ys -> (v : Vect _ ZZ) -> (v::xs) `bispanslz` (v::ys)```
* ```bispansNullcolExtension : (getCol FZ xs=Algebra.neutral)
	-> ys `bispanslz` map Vect.tail xs
	-> map ((Pos Z)::) ys `bispanslz` xs```

Foundational - algebraic:
* `zippyScaleIsAssociative`/`timesMatMatIsAssociative` — Proofs of `zippyScale` associativity and the equivalent matrix multiplication `(<>)` associativity.
	* ```vecMatVecRebracketing : {l : Vect n ZZ}
	-> {c : Matrix n m ZZ}
	-> {r : Vect m ZZ}
	-> l <:> (c</>r) = (l<\>c) <:> r``` — _RowVect_ \* (_Mat_ \* _Colvect_) = (_Rowvect_ \* _Mat_) \* _Colvect_; the two matrix actions involved in vector-matrix-vector multiplication are compatible.
		* Informal proof using a custom notation for transcribing the relevant transformations and pieces of the matrix, and the interactions between them, when working w/ sums over matrix indices in the manner required to replicate the traditional proof w/out a general subsequencewise additive associativity law.
* `dotBasisLIsIndex : (v : Vect d ZZ) -> basis i <:> v = index i v`/...`R`... — a vector's _i_th coordinate is the vector's dot product with the basis vector for the _i_th generator/axis.
* `multIdLeftNeutral : (a : Matrix _ _ ZZ) -> Id <> a = a`/...`Right`... — the identity matrix's namesake.
* `idMatSelfTranspose`
* ```zipWithTimesIsDistributiveL : (l, c, r : Vect n ZZ)
	-> zipWith (<.>) l $ c<+>r = zipWith (<.>) l c <+> zipWith (<.>) l r``` — pointwise vector multiplication is left-distributive over vector addition.
* ```zipWithTimesIsRecDistributiveL : (l : Vect n ZZ)
	-> (rs : Matrix m n ZZ)
	-> zipWith (<.>) l $ monoidsum rs = monoidsum $ map (zipWith (<.>) l) rs``` — pointwise vector multiplication left-distibutes over a sum over a `Vect` of vectors.
* `monoidsumNeutralIsNeutral1D`/...`2D` — The sum over the zero vector is zero, the sum over the zero matrix is the zero vector.
* `sumTransposeMapRelation : (xs : Matrix n m ZZ) -> monoidsum $ transpose xs = map monoidsum xs` — view summing the transpose's row vectors together pointwise as replacing each of the original matrix's rows with their sum.
* ```orderOfSummationExchange : (xs : Matrix n m ZZ)
	-> monoidsum $ monoidsum xs = monoidsum $ monoidsum $ transpose xs``` — exchanging/interchanging the order of summation / of two iterated sums / of a double sum. Statement for iterated sums of the generalized associativity-commutativity law (_x_ \+ _y_) \+ (_z_ \+ _w_)=(_x_ \+ _z_) \+ (_y_ \+ _w_). See: `doubleSumInnerSwap`.
	* ```sumSumAsSumMapSum : (xs : Matrix n m ZZ)
	-> monoidsum $ map monoidsum xs = monoidsum $ monoidsum xs``` — equivalent to the above.

Foundational - permutations:
* `vectPermTo : Iso (Fin n) (Fin n) -> Vect n a -> Vect n a`
	* `vectPermToIndexChariz : index i $ vectPermTo sigma xs = index (runIso sigma i) xs`
* `vectPermToRefl : vectPermTo Isomorphism.isoRefl xs = xs`
* `vectPermToTrans : vectPermTo (isoTrans sigma tau) xs = vectPermTo sigma $ vectPermTo tau xs`
* `vectPermToSym1 : vectPermTo (isoTrans sigma $ isoSym sigma) xs = xs`/`vectPermToSym2 : vectPermTo (isoTrans (isoSym sigma) sigma) xs = xs`
* ```permMatrixId : (sigma : Iso (Fin n) (Fin n))
	-> {xs : Matrix n m ZZ}
	-> (vectPermTo sigma Id)<>xs = vectPermTo sigma xs``` — Permutation matrices perform permutations on matrices when multiplied with them.
* ```permDoesntFixAValueNotFixed : (sigma : Iso (Fin n) (Fin n))
	-> (nel1, nel2 : Fin n)
	-> (runIso sigma nel1 = nel2)
	-> Either (Not (runIso sigma nel2 = nel2)) (nel1 = nel2)```
* ```permDoesntFix_corrolary : (sigma : Iso (Fin (S n)) (Fin (S n)))
	-> (snel : Fin (S n))
	-> Not (snel = FZ)
	-> (runIso sigma snel = FZ)
	-> Not (runIso sigma FZ = FZ)```
* `weakenIsoByValFZ : Iso (Fin (S n)) (Fin (S n)) -> Iso (Fin n) (Fin n)`
* ```rotateAt : (nel : Fin (S predn)) -> (sigma : Iso (Fin (S predn)) (Fin (S predn))
		* (a : Type)
		-> (xs : Vect (S predn) a)
		-> vectPermTo sigma xs = index nel xs :: deleteAt nel xs)``` — The permutation w/c takes the first some elements of a `Vect` and cycles them to one position later.
	* ex: ```> \xs => (getProof $ rotateAt $ 3 `shift` (FZ {k=5})) Char $ ['a','b','c']++xs```
* Discusses a failed-to-implement system for permuting `xs++ys` to `ys++xs` (where `xs` is a `Vect _ a` for arbitrary `a`).
* Considers `swapFZPerm`, the permutation which swaps the argument `Fin (S _)` w/ `FZ`, but finds the chosen implementation impossible.

Foundational - fins:
* `finReduce : (snel : Fin (S n)) -> Either (Fin n) (FZ = snel)`
	* `finReduceIsLeft : (z = FS k) -> finReduce z = Left k`
	* ```finReduceIsRight_sym : (z : Fin (S predn))
	-> (prFZ : z = FZ)
	-> (pr : FZ {k=predn} = z ** Right pr = finReduce z)```
* `splitFinFS : (i : Fin (S predn)) -> Either ( k : Fin predn ** i = FS k ) ( i = Fin.FZ {k=predn} )`
* ```splitFinAtConcat : (i : Fin $ n+m)
	-> Either (k : Fin n ** i = weakenN m k) (k : Fin m ** i = shift n k)```
* `indexConcatAsIndexAppendee : (i : Fin n) -> index (weakenN m i) $ xs++ys = index i xs`
* `indexConcatAsIndexAppended : (i : Fin m) -> index (shift n i) $ xs++ys = index i ys`
* `FSPreservesBoolEq : (i, j : Fin n) -> (FS i == FS j) = (i == j)`
* `eqTrue_Fin : (i, j : Fin n) -> (i=j) -> (i==j)=True`
* `notEqFalse_Fin : (i, j : Fin n) -> Not (i=j) -> (i==j)=False`

Foundational - other:
* `indexFinsIsIndex : index i $ fins n = i`/`indexRangeIsIndex : index i Vect.range = i`
	* `rangeIsFins : Vect.range = Matrix.fins n`
* `replaceAtIndexForm1 : (i=j) -> index i $ replaceAt j a v = a`/`replaceAtIndexForm2 : ((i=j)->Void) -> index i $ replaceAt j a v = index i v`
* `idMatIndicesChariz : indices i j Id = kroneckerDelta i j`
* `idMatIndexChariz : RingWithUnity a => index i $ Id {a=a} = basis i`
	* `kroneckerDelta i j = ifThenElse (i==j) Algebra.unity Algebra.neutral`
	* `kroneckerDeltaSym : RingWithUnity a => kroneckerDelta {a=a} i j = kroneckerDelta {a=a} j i`
* ```runIso : Iso a b -> a -> b
runIso (MkIso to _ _ _) = to```
* `isoSymIsInvolution : isoSym $ isoSym sigma = sigma`
* ```runIsoTrans : runIso (isoTrans sigma tau) x = runIso tau $ runIso sigma x```
* `runIsoSym1 : runIso (isoTrans sigma $ isoSym sigma) x = x`/`runIsoSym2 : runIso (isoTrans (isoSym sigma) sigma) x = x`

## Data.Matrix.LinearCombinations

Most significant contents:
* Proof of definition of vector-matrix multiplication as a linear combination where the vectors under combination are rows of the matrix and the scalar weights are the entries of the same index to the vector under multiplication. `timesVectMatAsLinearCombo : (v : Vect n ZZ) -> (xs : Matrix n w ZZ) -> ( v <\> xs = monoidsum (zipWith (<#>) v xs) )`.
* Proof from the above that the definition of matrix multiplication reduces to independent linear combinations of the row vectors of the righthand matrix. `timesMatMatAsMultipleLinearCombos : (vs : Matrix (S n') n ZZ) -> (xs : Matrix n w ZZ) -> vs <> xs = map (\zs => monoidsum $ zipWith (<#>) zs xs) vs`.
* Material characterizing iterated summation `monoidsum`, such as `monoidrec1D`/...`2D`, `headOfSumIsSumOfHeads`, `tailOfSumIsSumOfTails`, `dotproductRewrite`.
* `transposeNTail2`, which helps characterize the transpose.
* Algebraic identities proved about matrices and vectors.
	* The dot product is a bilinear map from (ZZ)-(Vect)s to (ZZ) (or at least, proof up to left-right symmetry).
		* Scalar multiplication of the left factor in a vector- or matrix-matrix product is the same as multiplying the product by the same scalar. (Note rel. to bilinearity)
	* ZZ matrices form an algebra. Uses `moduleScalarUnityIsUnity`. See also: `multIdLeftNeutral`, `multIdRightNeutral`, `timesMatMatIsAssociative` in ZZModuleSpan.
	* Distributivities of matrix-matrix, vector-matrix, and matrix-vector multiplication over matrix addition and vector addition.
	* Transposition is an antiendomorphism of multiplication for a commutative ground ring and an endomorphism of addition, hence an antiendomorphism of the matrix ring.
	* Some Algebra.neutral is a zero element / scalar zero proofs.
		* `dotCancelsHeadWithLeadingZeroL : (x, y : Vect n ZZ) -> (Algebra.neutral::x)<:>(r::y) = x<:>y`/...`R` — a consequence
		* `matMultCancelsHeadWithZeroColExtensionL : (map ((Pos 0)::) xs)<>(z::ys) = xs<>ys` — a consequence
		* `timesPreservesLeadingZeroExtensionR : xs<>(map ((Pos 0)::) ys) = map ((Pos 0)::) $ xs<>ys` — a consequence
	* `dotProductCommutative : (x, y : Vect n ZZ) -> x<:>y = y<:>x`
	* The behavior & compatibility of the inverse w/ scalar multiplication of `Vect`s or `Matrix`s.

Additional algebraic:
* `doubleSumInnerSwap : VerifiedAbelianGroup t => (a, b, c, d : t) -> (a<+>b)<+>(c<+>d) = (a<+>c)<+>(b<+>d)` — a generalized associativity-commutativity law.
** `doubleSumInnerSwap_Vect`

Structural:
* `lemma_VectAddEntrywise : .{n : Nat} -> (ni : Fin n) -> (v, w : Vect n ZZ) -> index ni (v<+>w) = (index ni v)<+>(index ni w)`
	* `lemma_VectAddHead : (v, w : Vect (S n) ZZ) -> head(v<+>w) = (head v)<+>(head w)`
	* `lemma_VectAddTail`
	* `matrixAddEntrywise`, `matrixAddHead`, `matrixAddMapHead`, `matrixAddTail`, `matrixAddMapTail`

Misc foundational

## FinOrdering

Contents:
* A(n) `LTRel` relation term meant for less-than relations, in an `OrdRel` class, and a `DecLT` class for decidable relations, where such an `OrdRel` whose `LTRel x y` is occupied will have a `decLT x y` giving an inhabitant and where unoccupied `decLT x y` will be a proof of this (some `LTRel x y -> Void`).
* An instance of this for `Nat`, by which `Fin n` will be ordered indirectly through `finToNat`.
* `lteToLTERel : {a, b : Nat} -> LTE a b -> LTERel a b`, relating `FinOrdering`'s version `LTERel` of the less-than-or-equal-to relation to `LTE`, from Prelude, for `Nat`s.
* `zLtSuccIsTrue : (k : Nat) -> LTRel Z (S k)`
* Declaration: `gtnatFZImpliesIsFinSucc` — A `Fin _` of ordinal _n_ > 0 is a fin-successor.
* Declaration: `natGtAnyImpliesGtZ` — For all natural _m_ and _n_, _m_ < _n_ implies 0 < _n_.
* Declarations: `ltenatLastIsTrue`/...`2` — a number is in \{1, ..., _n_\} if and only if it is less than or equal to _n_, in our sense.

## Control.Algebra.ZZVerifiedInstances

Contents: Typeclass instance `instance VerifiedRingWithUnity ZZ`

## Data.Matrix.AlgebraicVerified

Definitions:
* Verified module
* Verified vector space

Ripped from comments of Classes.Verified, commenting out there coincides with definition of module being in the separate module Control.Algebra.VectorSpace from Control.Algebra.

Typeclass instances:
* Verified module instance for `VerifiedRingWithUnity a => Matrix n m a`.
* No such instance for `Vect`s, but proofs of the required properties.

Trivial identities about (unital) rings:
* `groupOpIsCancellativeL`/...`R` : Group operations are left/right cancellative.
* Above ...`_Vect` : Analogues for `Vect`s.
* `neutralSelfInverse`
* `groupElemOwnDoubleImpliesNeut` : Groups have a unique idempotent, the identity.
* `ringNeutralIsMultZeroL`/...`R` : Ring additive identity is a multiplicative zero.
* `ringNegationCommutesWithLeftMult`/...`RightMult` : _a_ \* (\- _b_) = \- (_a_ \* _b_) = (\- _a_) \* _b_.

## Data.Matrix.ZZVerified

Identities whose proof is particular to ZZ, mainly because of the limitations caused by Issue #24 on GitHub. Some duplicate functionality.

Proved:
* `zzVecNeutralIsVecPtwiseProdZeroL`/...`R` — the zero vector is a zero of the dot product `(<:>)`. Name is incorrect for the identity stated. Overlaps w/ `neutralVectIsDotProductZero_R`/...`L` respectively in Data.Matrix.LinearCombinations.
* `zzVecNeutralIsVecMatMultZero`/...`MatVec`... — likewise of vector-matrix and matrix-vector multiplication. Overlaps w/ `neutralVectIsVectTimesZero`/`emptyVectIsTimesVectZero` in Data.Matrix.LinearCombinations respectively.

Declared:
* `zzVecNeutralIsNeutralL`/...`R` — the zero vector is an identity for vector addition. Overlaps w/ `monoidNeutralIsNeutralL_Vect` in Data.Matrix.AlgebraicVerified.
* `zzVecScalarUnityIsUnity` — scalar multiplication of a `Vect _ ZZ` by `1` yields the original vector. Overlaps w/ `moduleScalarUnityIsUnity_Vect` in Data.Matrix.AlgebraicVerified.

## Data.Vect.Structural

A library of properties to do w/ `Vect`s as a structure and functions to/from them, including characterizations of those operations' effects structurally.

* Theorem `vecHeadtailsEq` for proving equality of `Vect`s by proving equality of their heads and tails. Often used after `headtails`.
* Theorem `vecIndexwiseEq` for proving equality of `Vect`s by proving indexwise equality of their entries.

* Theorems characterizing `Vect`s of degenerate qualities.
* Theorems characterizing the index or head of a `Vect` created with a certain operation.
* The theorem `weakenedInd` about comparing an index of a list to an index of its `init`.
* The theorem `extensionalEqToMapEq` extending an extensional equality between functions to one between their `map`s over `Vect`s.
* `composeUnderMap` w/c proves preservation of function composition for `Vect _`, what would be `functorComposition` in a `VerifiedFunctor` instance.
* `updateDeleteAtChariz : deleteAt i $ updateAt i f xs = deleteAt i xs`
* `uniformValImpliesReplicate : `...`((i : _) -> index i x = a) -> x = replicate n a`

* Compatibility between the operations of the ring (a) and of (Vect n a) as a module under (index).

* `foldrImplRec` — The recursive equation for `foldr` over `Vect`s. Converts a right fold into a left fold.
* `monoidrec : Monoid a => (v : a) -> (vs : Vect n a) -> sum' (v::vs) = v <+> sum' vs` — The recursive equation for sums in (Monoid)s over a (Vect _). Converts a right fold into a left fold.
	* See `monoidrec1D`/...`2D` in Data.Matrix.LinearCombinations.

## Data.Matrix.Structural

A library of properties to do w/ `Matrix`s as a structure and functions to/from them, including characterizations of those operations' effects structurally.

* `transposeIsInvolution : transpose $ transpose xs = xs`
* `transposeIndicesChariz : {xs : Matrix n m a} -> (i : Fin n) -> (j : Fin m) -> indices j i $ transpose xs = indices i j xs`
* `transposeIndexChariz : {xs : Matrix n m a} -> index k $ transpose xs = getCol k xs`
	* `transposeNHead: head $ transpose xs = map head xs`
* `transposeNTail : transpose $ tail $ transpose xs = map tail xs`
	* See also: `transposeNTail2` in Data.Matrix.LinearCombinations

* `vecMatMultIsTransposeVecMult`/`matVecIsVecTransposeMult` — The special cases of the transpose being an antiendomorphism of matrix multiplication for vector-matrix and matrix-vector multiplication.
* `headVecMatMultChariz` — a vector-matrix product as mapped dot product lemma.

* `matMultIndicesChariz : Ring a => {l : Matrix _ _ a} -> {r : Matrix _ _ a} -> indices i j (l<>r) = (index i l)<:>(getCol j r)` — the entrywise expression of a matrix product.

* `leadingElemExtensionAsZipWithCons : map (r::) xs = Vect.zipWith Vect.(::) (replicate _ r) xs`
	* `leadingElemExtensionFirstColReplicate`/`leadingElemExtensionColFSId` — the columns of `map (r::) xs`. Special cases of `map` being a `VerifiedFunctor`.
* `nullcolExtensionEq` — If the first column of `xs` is the zero vector, then `xs` is the appension of `0` to each of its rows' `tail`s.

* `indexNeutralIsNeutral2D` — every row of a zero matrix is the zero vector.
