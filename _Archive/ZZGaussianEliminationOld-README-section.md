Last README documentation for ZZGaussianEliminationOld.idr.

Last commit where it was supported is `720fcc5`, where it was called `ZZGaussianElimination.idr`.

`elimFirstCol-oldmaterial.idr` discusses the problems that were faced trying to complete a proof of a row echelon inference (the one that should replace `echelonHeadnonzerovecExtension` here) that led to the December 2017 rewrite.

## ZZGaussianElimination

__DEPRECATED : See ZZGaussianEliminationRedo__

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
