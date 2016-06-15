# verified-integer-gaussian-elimination

Idris package looking to define, implement, and verify naiive Gaussian elimination over the integers in some system of linear algebra.

ZZModuleSpan.idr is the only usable file.
Other files show what other kind of theorems are needed, but about the wrong objects to be correct or to fit the system of linear algebra used in this package.

Currently implemented and verified:
* Proof,† from some unproved basic facts, of definition of vector-matrix multiplication as a linear combination where the vectors under combination are rows of the matrix and the scalar weights are the entries of the same index to the vector under multiplication. †`timesVectMatAsLinearCombo : (v : Vect n ZZ) -> (xs : Matrix n w ZZ) -> ( v <\> xs = monoidsum (zipWith (<#>) v xs) )`.
* Proof‡ the definiton of matrix multiplication reduces to independent applications of `i(<\>)` to the second matrix, where `i` runs through each row vector of the first matrix; has applications with above to a definition of matrix multiplication in terms of independent linear combinations. ‡`timesMatMatAsMultipleLinearCombos_EntryChariz` suffices by inspection of the recursion scheme for `(<>) = \m1 => \m2 => map (<\>m2) m1`.
* Some definitions related to linear spans.
