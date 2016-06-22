module FinOrdering
-- Classes (OrdRel, DecLT) are redundant with IntegerOrdering.idr

import Data.Fin
import Data.ZZ


-- Note that unlike (=) the types do not inherently need to be ambiguous
class OrdRel A where
	LT : A -> A -> Type

class (OrdRel s) => DecLT s where
	decLT : (x1 : s) -> (x2 : s) -> Dec ( LT x1 x2 )

data FinLTTy : (n : Nat) -> (i, j : Fin n) -> Type where
	FinLTFZPos : FinLTTy (S (S n)) FZ (FS a)
	FinLTIncrem : FinLTTy n a b -> FinLTTy (S n) (FS a) (FS b)

instance OrdRel (Fin n) where
	LT {n} = FinLTTy n

total
decLTFin : (n : Nat) -> (i, j : Fin n) -> Dec ( LT i j )
decLTFin Z a _ = No (\x => FinZAbsurd a)
decLTFin (S Z) a b = No cannit
	where
		cannit : FinLTTy (S Z) a b -> Void
		cannit FinLTFZPos impossible
		cannit (FinLTIncrem FinLTFZPos) impossible
decLTFin (S (S n)) FZ FZ = No dontDoMeIn
	where
		dontDoMeIn : FinLTTy (S (S n)) FZ FZ -> Void
		dontDoMeIn FinLTFZPos impossible
		dontDoMeIn (FinLTIncrem t) impossible
decLTFin (S (S n)) FZ (FS b) = Yes FinLTFZPos
decLTFin (S (S n)) (FS a) FZ = No itsOver
	where
		itsOver : FinLTTy (S (S n)) (FS a) FZ -> Void
		itsOver FinLTFZPos impossible
		itsOver (FinLTIncrem t) impossible
decLTFin (S (S n)) (FS a) (FS b) with (decLTFin (S n) a b)
	| Yes w = Yes (FinLTIncrem w)
	| No s = No (s' s)
	where
		s' : ( FinLTTy (S n) a b -> Void ) -> ( FinLTTy (S (S n)) (FS a) (FS b) -> Void )
		s' avo FinLTFZPos impossible
		s' avo (FinLTIncrem t) = avo t

instance DecLT (Fin n) where
	decLT {n} = decLTFin n
