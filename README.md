# verified-integer-gaussian-elimination

Idris package looking to define, implement, and verify naiive Gaussian elimination over the integers in some system of linear algebra.

ZZGaussianElimination.idr, ZZModuleSpan.idr, Data/Matrix/LinearCombinations.idr, & FinOrdering.idr are the only usable files.
Other files show what other kind of theorems are needed, but about the wrong objects to be correct or to fit the system of linear algebra used in this package.

## ZZGaussianElimination

Contents:
* Scribbles about properties to be proven of gaussian elimination (the type signature of the function that performs the algorithm).

## ZZModuleSpan

Contents:
* Definition of the *linearly spans* relation `spanslz` between two Vects of Vects of integers (where integers means inhabitants of Data.ZZ).
* Some definitions related to linear spans.
* Proof of transitivity of `spanslz` using some unproved but known theorems.
* Sketches of proof of `zippyScale` associativity in terms of the equivalent matrix multiplication associativity. `zippyScale` is shorthand for a form of linear combination of the rows of a matrix over multiple vectors, as dealt with and proved extensionally equal to matrix multiplication in Data.Matrix.LinearCombinations.

## Data.Matrix.LinearCombinations

Most significant contents:
* Proof, from some unproved basic facts, of definition of vector-matrix multiplication as a linear combination where the vectors under combination are rows of the matrix and the scalar weights are the entries of the same index to the vector under multiplication. `timesVectMatAsLinearCombo : (v : Vect n ZZ) -> (xs : Matrix n w ZZ) -> ( v <\> xs = monoidsum (zipWith (<#>) v xs) )`.
* Proof from the above that the definition of matrix multiplication reduces to independent linear combinations of the row vectors of the righthand matrix. `timesMatMatAsMultipleLinearCombos : (vs : Matrix (S n') n ZZ) -> (xs : Matrix n w ZZ) -> vs <> xs = map (\zs => monoidsum $ zipWith (<#>) zs xs) vs`.

## FinOrdering

Contents:
* A(n) `LT` relation term meant for less-than relations, in an `OrdRel` class, and a `DecLT` class for decidable relations, where such an `OrdRel` whose `LT x y` is occupied will have a `decLT x y` giving an inhabitant and where unoccupied `decLT x y` will be a proof of this (some `LT x y -> Void`).
