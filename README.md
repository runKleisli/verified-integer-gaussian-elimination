# verified-integer-gaussian-elimination

Idris package looking to define, implement, and verify naiive Gaussian elimination over the integers in some system of linear algebra.

ZZModuleSpan.idr and Data/Matrix/LinearCombinations.idr are the only usable files.
Other files show what other kind of theorems are needed, but about the wrong objects to be correct or to fit the system of linear algebra used in this package.

## ZZModuleSpan

Contents:
* Some definitions related to linear spans.

## Data.Matrix.LinearCombinations

Most significant contents:
* Proof, from some unproved basic facts, of definition of vector-matrix multiplication as a linear combination where the vectors under combination are rows of the matrix and the scalar weights are the entries of the same index to the vector under multiplication. `timesVectMatAsLinearCombo : (v : Vect n ZZ) -> (xs : Matrix n w ZZ) -> ( v <\> xs = monoidsum (zipWith (<#>) v xs) )`.
* Proof from the above that the definition of matrix multiplication reduces to independent linear combinations of the row vectors of the righthand matrix. `timesMatMatAsMultipleLinearCombos : (vs : Matrix (S n') n ZZ) -> (xs : Matrix n w ZZ) -> vs <> xs = map (\zs => monoidsum $ zipWith (<#>) zs xs) vs`.
