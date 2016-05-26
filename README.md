# verified-integer-gaussian-elimination

Idris package looking to define, implement, and verify naiive Gaussian elimination over the integers in some system of linear algebra.

ZZModuleSpan.idr is the only usable file.
Other files show what other kind of theorems are needed, but about the wrong objects to be correct or to fit the system of linear algebra used in this package.

Currently implemented and verified:
* Partial proof of definition of vector-matrix multiplication as a linear combination where the vectors are rows of the matrix and the scalar weights are the vector entries of the same index.
* Some definitions related to linear spans.
