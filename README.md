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
* Declaration of gaussian elimination as an algorithm which converts a matrix into one in row echelon form which spans it. `gaussElimlz : (xs : Matrix n m ZZ) -> (gexs : Matrix n' m ZZ ** (rowEchelon gexs, bispanslz gexs xs))`
* Implementation of the second property, `rowEchelon`.
* `leadingNonzeroCalc`, which takes a `Vect n ZZ` to its first index to a nonzero entry or a proof that all entries are zero.
* `downAndNotRightOfEntryImpliesZ`, which says a matrix is zero below an index and at or to the left of a second index.
* Implementation of column-zero elimination, `elimFirstCol : (xs : Matrix n (S predm) ZZ) -> Reader ZZGaussianElimination.gcdOfVectAlg (gexs : Matrix (S n) (S predm) ZZ ** (downAndNotRightOfEntryImpliesZ gexs FZ FZ, bispanslz gexs xs))`.
* `foldAutoind` - A vector fold over suppressed indices. Extends one witness for some predicate `p : (m : Nat) -> Fin (S m) -> a -> Type` to a `Vect` of them.
* `foldAutoind2` - Same strength of result as `foldAutoind`, but applies where the predicate `p : (m : Nat) -> Fin (S m) -> (a m) -> Type` isn't naturally expressed or proved without affecting the type of the witnesses dealt with by this process.

## ZZModuleSpan

Contents:
* Definition of the *linearly spans* relation `spanslz` between two Vects of Vects of integers (where integers means inhabitants of Data.ZZ).
** Its symmetric closure `bispanslz xs ys = (spanslz xs ys, spanslz ys xs)`.
* Some definitions related to linear spans.
* Proof of transitivity and reflexivity of `spanslz` using some unproved but known theorems.
** Their analogues for `bispanslz`, plus proof it's symmetric.
* Sketches of proof of `zippyScale` associativity in terms of the equivalent matrix multiplication associativity. `zippyScale` is shorthand for a form of linear combination of the rows of a matrix over multiple vectors, as dealt with and proved extensionally equal to matrix multiplication in Data.Matrix.LinearCombinations.
* Proof of `updateAtEquality : {ls : Matrix n k ZZ} -> {rs : Matrix k m ZZ} -> (updi : Fin n) -> (f : (i : Nat) -> Vect i ZZ -> Vect i ZZ) -> ( (la : Vect k ZZ) -> (f k la) <\> rs = f m $ la <\> rs ) -> zippyScale (updateAt updi (f k) ls) rs = updateAt updi (f m) (zippyScale ls rs)`, which lets you prove `vectMatLScalingCompatibility : {z : ZZ} -> {rs : Matrix k m ZZ} -> (z <#> la) <\> rs = z <#> (la <\> rs)` by a proof that works at least in the REPL, from which `spanRowScalelz : (z : ZZ) -> (updi : Fin n') -> spanslz xs ys -> spanslz xs (updateAt updi (z<#>) ys)` is proved.
* Many propositions introduced. Towards the end of the file, after section "Proof of relational properties of span", the holes tend to be closer to known properties that will be used directly in the gaussian elimination algorithm, while towards the "Trivial lemmas and plumbing" section at the beginning of the file, the holes are generally strategies proposed for proving theorems about reordering vectors by a permutation, particularly the problem of reaching `spanslzAdditiveExchangeAt : (nel : Fin (S predn)) -> spanslz (updateAt nel (<+>(z<\>(deleteRow nel xs))) xs) xs` from `spanslzAdditiveExchange : spanslz ((y<+>(z<\>xs))::xs) (y::xs)`.

## Data.Matrix.LinearCombinations

Most significant contents:
* Proof, from some unproved basic facts, of definition of vector-matrix multiplication as a linear combination where the vectors under combination are rows of the matrix and the scalar weights are the entries of the same index to the vector under multiplication. `timesVectMatAsLinearCombo : (v : Vect n ZZ) -> (xs : Matrix n w ZZ) -> ( v <\> xs = monoidsum (zipWith (<#>) v xs) )`.
* Proof from the above that the definition of matrix multiplication reduces to independent linear combinations of the row vectors of the righthand matrix. `timesMatMatAsMultipleLinearCombos : (vs : Matrix (S n') n ZZ) -> (xs : Matrix n w ZZ) -> vs <> xs = map (\zs => monoidsum $ zipWith (<#>) zs xs) vs`.

## FinOrdering

Contents:
* A(n) `LTRel` relation term meant for less-than relations, in an `OrdRel` class, and a `DecLT` class for decidable relations, where such an `OrdRel` whose `LTRel x y` is occupied will have a `decLT x y` giving an inhabitant and where unoccupied `decLT x y` will be a proof of this (some `LTRel x y -> Void`).
* An instance of this for `Nat`, by which `Fin n` will be ordered indirectly through `finToNat`.

## Control.Algebra.ZZVerifiedInstances

Contents: Declaration for `instance VerifiedRingWithUnity ZZ`

## Data.Matrix.AlgebraicVerified

Definitions:
* Verified module
* Verified vector space

Ripped from comments of Classes.Verified, commenting out there coincides with definition of module being in the separate module Control.Algebra.VectorSpace from Control.Algebra.

Declarations:
* Verified module instance for `VerifiedRingWithUnity a => Matrix n m a`.
