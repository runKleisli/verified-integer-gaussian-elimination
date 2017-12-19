module IntegerOrdering



-- Note that unlike (=) the types do not inherently need to be ambiguous
class OrdRel A where
	LT : A -> A -> Type

class (OrdRel s) => DecLT s where
	decLT : (x1 : s) -> (x2 : s) -> Dec ( LT x1 x2 )

LTZero : Integer -> Type
LTZero x = Not (x = abs x)

instance OrdRel Integer where
	LT a b = LTZero (a-b)

decLTBigInt : (a : Integer) -> (b : Integer) -> Dec ( LT a b )
decLTBigInt a b = case ( decEq (a-b) (abs (a-b)) ) of
		Yes prPos => No (\false => false prPos)
		No prNeg => Yes prNeg

instance DecLT Integer where
	decLT = decLTBigInt
