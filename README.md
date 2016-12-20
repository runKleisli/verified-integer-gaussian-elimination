# verified-integer-gaussian-elimination

Idris package looking to define, implement, and verify naiive Gaussian elimination over the integers in some system of linear algebra.

Ignore these files:
* BezoutsIdentity.idr
* IntegerArith.idr
* IntegerGroupTheory.idr
* IntegerOrdering.idr

These show what other kind of theorems are needed, but about the wrong objects to be correct or to fit the system of linear algebra used in this package.

## ZZGaussianElimination

Contents:
* Declaration of gaussian elimination as an algorithm which converts a matrix into one in row echelon form which spans it. `gaussElimlz : (xs : Matrix n m ZZ) -> (n' : Nat 	* (gexs : Matrix n' m ZZ 	* (rowEchelon gexs, bispanslz gexs xs)))`
* Implementation of the second property, `rowEchelon`.
* `leadingNonzeroCalc`, which takes a `Vect n ZZ` to its first index to a nonzero entry or a proof that all entries are zero.
* `downAndNotRightOfEntryImpliesZ`, which says a matrix is zero below an index and at or to the left of a second index.
* Implementation of column-zero elimination, `elimFirstCol : (xs : Matrix n (S predm) ZZ) -> Reader ZZGaussianElimination.gcdOfVectAlg (gexs : Matrix (S n) (S predm) ZZ 	* (downAndNotRightOfEntryImpliesZ gexs FZ FZ, bispanslz gexs xs))`.
* Implementation of the inductive step for elimination, `gaussElimlzIfGCD2 : (xs : Matrix n (S predm) ZZ) -> Reader ZZGaussianElimination.gcdOfVectAlg ( n' : Nat 	* (gexs : Matrix n' (S predm) ZZ 	* (rowEchelon gexs, bispanslz gexs xs)) )`
* `foldAutoind` - A vector fold over suppressed indices. Extends one witness for some predicate `p : (m : Nat) -> Fin (S m) -> a -> Type` to a `Vect` of them.
* `foldAutoind2` - Same strength of result as `foldAutoind`, but applies where the predicate `p : (m : Nat) -> Fin (S m) -> (a m) -> Type` isn't naturally expressed or proved without affecting the type of the witnesses dealt with by this process.

## ZZModuleSpan

__All proofs mentioned below are up to Issue #24 on GitHub being solved__

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
	-> monoidsum $ monoidsum xs = monoidsum $ monoidsum $ transpose xs``` — exchanging/interchanging the order of summation / of two iterated sums / of a double sum. Statement for iterated sums of the generalized associativity law (_x_ \+ _y_) \+ (_z_ \+ _w_)=(_x_ \+ _z_) \+ (_y_ \+ _w_).
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
	-> (pr : FZ {k=predn} = z 	* Right pr = finReduce z)```
* `splitFinFS : (i : Fin (S predn)) -> Either ( k : Fin predn 	* i = FS k ) ( i = Fin.FZ {k=predn} )`
* ```splitFinAtConcat : (i : Fin $ n+m)
	-> Either (k : Fin n 	* i = weakenN m k) (k : Fin m 	* i = shift n k)```
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
* Proof, from some unproved basic facts, of definition of vector-matrix multiplication as a linear combination where the vectors under combination are rows of the matrix and the scalar weights are the entries of the same index to the vector under multiplication. `timesVectMatAsLinearCombo : (v : Vect n ZZ) -> (xs : Matrix n w ZZ) -> ( v <\> xs = monoidsum (zipWith (<#>) v xs) )`.
* Proof from the above that the definition of matrix multiplication reduces to independent linear combinations of the row vectors of the righthand matrix. `timesMatMatAsMultipleLinearCombos : (vs : Matrix (S n') n ZZ) -> (xs : Matrix n w ZZ) -> vs <> xs = map (\zs => monoidsum $ zipWith (<#>) zs xs) vs`.

## FinOrdering

Contents:
* A(n) `LTRel` relation term meant for less-than relations, in an `OrdRel` class, and a `DecLT` class for decidable relations, where such an `OrdRel` whose `LTRel x y` is occupied will have a `decLT x y` giving an inhabitant and where unoccupied `decLT x y` will be a proof of this (some `LTRel x y -> Void`).
* An instance of this for `Nat`, by which `Fin n` will be ordered indirectly through `finToNat`.
* `lteToLTERel : {a, b : Nat} -> LTE a b -> LTERel a b`, relating `FinOrdering`'s version `LTERel` of the less-than-or-equal-to relation to `LTE`, from Prelude, for `Nat`s.

## Control.Algebra.ZZVerifiedInstances

Contents: Declaration for `instance VerifiedRingWithUnity ZZ`

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
