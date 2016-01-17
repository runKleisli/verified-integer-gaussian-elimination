module IntegerArith



{-
Strategy (<) type:

To handle case a (-a)
autogen a type which is either a<b or a>b and a proof of it.
match on the with of the generating function, so that you can have distinct cases of the inequality treated as creating different assumptions about the values a and b.
use this pattern matching structure in the definition of gcdBigInt itself.
Reflection shouldn't be needed, then, except maybe for gcdBigInt a 0.

We can implement this inequality type (which mirrors LTE for Nats) using recursion, even though we aren't given a fixed enumeration of Integer, because we have decEq.

	decEq 5 3 = No ( _ 5 3 ) : Dec (5 = 3)
	decEq 5 5 = Yes Refl : (5=5)

Although actually, a case expression on (decEq a b) may be enough instead of a dependent pattern match, because the case matched on itself has a proof, and one might be able to reuse that...

=======

Strategy rewrite case argument:

If the function you're trying to prove matches an equality has a case expression or equivalent in it, we can show that the function can be computed by assuming this has a particular value, and thus when we can take the case expression outside the equality and the cases being matched on include a proof of something which determines the value of the case argument, we can apply a function using this proof to obtain a proof that the case argument is the required value.

So if our case argument is (decLT (a*b) 0) then we can get a

	(decLT (a*b) 0 = Yes pr)

from the (Yes pr : DecLT (a*b) 0) that one is pattern matching on when trying to generate the equality of gcdBigInt with its definition, by a function which manually constructs the proof from (pr) if Refl won't be recognized.

Once that (decLT (a*b) 0 = Yes pr) is used to rewrite the case argument of the equality-with-definition generator from (decLT (a*b) 0) to one of the cases (Yes _) of the case expressions in the gcdBigInt definition, we should be able to use compute to collapse the case expression and obtain the desired equality.

-}



-- Note that unlike (=) the types do not inherently need to be ambiguous
class OrdRel A where
	LT : A -> A -> Type

class (OrdRel s) => DecLT s where
	decLT : (x1 : s) -> (x2 : s) -> Dec ( LT x1 x2 )

{-
data LTBigInt where
	-- YLT 0 a : (a eq abs a) -> LTBigInt
	YLT : (x : Integer) -> {.auto Refl : x = 0} -> (a eq abs a) -> LTBigInt a b
-}

LTZero : Integer -> Type
LTZero x = Not (x = abs x)

{-
-- Designing this as an Either helped.
data LTBigInt where
	YLT : Either (a : Integer ** LTZero a) ( (a,b):(Integer,Integer) ** LTZero (a-b)) -> LTBigInt a b
-}

{-
-- Then there's a reduction from agreement of cases
data LTBigInt where
	YLT : ( (a,b):(Integer,Integer) ** LTZero (a-b) ) -> LTBigInt a b
-}

{-
Then there's a serialization.

Could make the LTZero an implicit argument, if it didn't need a standard proof that exists no matter what `a` and `b` are. A regression occurs, since we don't have something like (Refl) whose construction is closed to those arguments ((x,y)**(x=y)) related by the required property of the list of arguments.
r
Maybe we could write

	YLT : T a b -> LTBigInt

where (T a b = Void) if no proof of ( LTZero (a-b) ) exists and

	{.auto stdproof : LTZero (a-b)} -> (a,b) : (Integer,Integer)

otherwise? I don't even know that can really be stated.
-}
{-
data LTBigInt : Integer -> Integer -> Type where
	IsLT : (a : Integer) -> (b : Integer) -> LTZero (a-b) -> LTBigInt a b
-}

-- Finally, separation of concerns
instance OrdRel Integer where
	LT a b = LTZero (a-b)

{-
-- Don't even need all these layers of indirection. Defn of LT subsumed LTBigInt.

data LTBigInt : Integer -> Integer -> Type where
	IsLT : (a : Integer) -> (b : Integer) -> LT a b -> LTBigInt a b
-- 	IsLT : (a : Integer) -> (b : Integer) -> LTZero (a-b) -> LTBigInt a b

liftNoLTBigInt : (a : Integer) -> (b : Integer)
-- 	-> (LTZero (a-b) -> Void)
	-> (LT a b -> Void)
	-> (LTBigInt a b -> Void)
liftNoLTBigInt a b proof_absurd (IsLT a b pr) = proof_absurd pr

decLTBigInt : (a : Integer) -> (b : Integer) -> Dec ( LTBigInt a b )
decLTBigInt a b = case ( decEq (a-b) (abs (a-b)) ) of
		Yes prPos => No (liftNoLTBigInt a b (_ prPos))
		No prNeg => Yes (IsLT a b prNeg)

instance DecLT Integer where
-- 	decLT = decLTBigInt -- Can't cause LTBigInt isn't LT as def.d, see above comment
	decLT a b = case (decLTBigInt a b) of
			No pr => 
			Yes pr => 
-}

decLTBigInt : (a : Integer) -> (b : Integer) -> Dec ( LT a b )
decLTBigInt a b = case ( decEq (a-b) (abs (a-b)) ) of
		Yes prPos => No (\false => false prPos)
		No prNeg => Yes prNeg

instance DecLT Integer where
	decLT = decLTBigInt



{-
-- IntegerArith.gcdBigInt is possibly not total due to recursive path IntegerArith.gcdBigInt
-- %reflection
total
gcdBigInt : Integer -> Integer -> Integer
gcdBigInt a 0 = a
gcdBigInt a b = if a*b<0 then gcdBigInt (abs a) (abs b) else assert_total (gcdBigInt b (modBigInt a b))
-}

{-
-- IntegerArith.gcdBigInt is possibly not total due to: IntegerArith.case block in gcdBigInt

total
gcdBigInt : Integer -> Integer -> Integer
gcdBigInt a 0 = a
gcdBigInt a b = case ( decLT (a*b) 0 ) of
		Yes pr => gcdBigInt (abs a) (abs b)
		otherwise => gcdBigInt b (modBigInt a b)
-}

{-
-- IntegerArith.gcdBigInt is possibly not total due to: with block in IntegerArith.gcdBigInt

total
gcdBigInt : Integer -> Integer -> Integer
gcdBigInt a 0 = a
gcdBigInt a b with ( decLT (a*b) 0 )
	| Yes pr = gcdBigInt (abs a) (abs b)
	| otherwise = gcdBigInt b (modBigInt a b)
-}

{-
%reflection
total
gcdType : Integer -> Integer -> Type
gcdType a 0 = ( gcdBigInt a 0 = a )
gcdType a b with (decEq a (-b))
	| Yes pr = 
	| No pr = 
-}
{-
gcdType a b = ( gcdBigInt a b = if a*b<0 then gcdBigInt (abs a) (abs b) else assert_total (gcdBigInt b (modBigInt a b)) )
-}
{-
gcdType a b = if a*b<0 then ( gcdBigInt a b = gcdBigInt (abs a) (abs b) ) else ( gcdBigInt a b = gcdBigInt b (modBigInt a b) )
-}

{-
gcddefBigInt : (a : Integer) -> (b : Integer) -> gcdType a b
gcddefBigInt a 0 = Refl
gcddefBigInt a b = if a*b<0 then the ( gcdBigInt a b = gcdBigInt (abs a) (abs b) ) gcddefBigIntZeroPr else gcddefBigIntPr -- believe_me "by definition"
	where
		gcddefBigIntZeroPr = ?gcddefBigIntZeroPr'
		gcddefBigIntPr = ?gcddefBigIntPr'
-}



modeqBigInt : (a : Integer) -> (b : Integer) -> (nzpr : Not (b=0))
	-> mod a b + (div (a - mod a b) b)*b = a
modeqBigInt = ?modeqBigIntHole



plusAssociativeBigInt : (left : Integer) ->
                  (centre : Integer) ->
                  (right : Integer) ->
                  left + (centre + right) = left + centre + right
plusAssociativeBigInt = believe_me "Integer addition is associative."



rdivBigInt : (x : Integer) -> (y : Integer) -> (x+y)-y = x
rdivBigInt x y = believe_me "Integer addition is right divisible."

unRDivBigInt : (x : Integer) -> (y : Integer) -> (x-y)+y = x
unRDivBigInt = believe_me "Integer (right) subtraction is right divisible."

lcancBigInt: (left1 : Integer) -> (left2 : Integer) -> (right : Integer) -> (left1+right = left2+right) -> (left1 = left2)
lcancBigInt left1 left2 right = ?lcancBigIntpr

lcancBigIntpr = proof
  intro
  intro
  intro
  intro prsum
  rewrite sym (sym $ rdivBigInt left1 right)
  rewrite sym (sym $ rdivBigInt left2 right)
  exact cong {f=\x => x-right} prsum



plusRightIdBigInt : (x : Integer) -> x = x+0
-- plusRightIdBigInt x = believe_me "assume x=x+0"
plusRightIdBigInt x = ?plusRightIdBigIntPr

plusRightIdBigIntPr = proof
  intro
  claim addZeroTwice (x+0=(x+0)+0)
  unfocus
  exact lcancBigInt x (x+0) 0 addZeroTwice
  exact trans Refl (plusAssociativeBigInt x 0 0)



negSumImedBigInt : (x : Integer) -> (y : Integer) -> (x-y)+y = (x+(negate y))+y
negSumImedBigInt = proof
  intros
  rewrite sym (unRDivBigInt x y)
  rewrite sym (sym $ plusAssociativeBigInt x (negate y) y)
  rewrite sym (unRDivBigInt 0 y)
  rewrite sym (plusRightIdBigInt x)
  trivial

differenceAsSum : (x : Integer) -> (y : Integer) -> x-y = x+(negate y)
differenceAsSum x y = ?differenceAsSumPr

differenceAsSumPr = proof
  intros
  claim pr0 ((x-y)+y = (x+(negate y))+y)
  unfocus
  let prf1 = replace pr0 {P= \t => t-y=x-y}
  claim prf1Arg (((x - y) + y)-y = x - y)
  unfocus
  rewrite sym (sym $ prf1 prf1Arg)
  rewrite sym ( rdivBigInt (x+(0-y)) y )
  exact Refl
  claim prmainReAssoc (x = x + negate y + y)
  unfocus
  exact trans (unRDivBigInt x y) prmainReAssoc
  exact rdivBigInt (x-y) y
  claim prmain (x = x + (negate y + y))
  unfocus
  exact trans prmain (plusAssociativeBigInt x (negate y) y)
  claim prmainPlusZ (x+0 = x+(negate y + y))
  unfocus
  exact trans (plusRightIdBigInt x) prmainPlusZ
  exact cong (sym $ unRDivBigInt 0 y)



plusCommutativeBigInt : (left : Integer) ->
                  (right : Integer) ->
                  left + right = right + left
plusCommutativeBigInt = believe_me "Integer addition is commutative."



subtractionexchange : (x : Integer) -> (y : Integer) -> (z : Integer)
	-> (x-y)+z = x+(z-y)
subtractionexchange = ?subtractionexchangepr

subtractionexchangepr = proof
  intros
  rewrite sym (differenceAsSum x y)
  rewrite sym (sym $ plusAssociativeBigInt x (0-y) z)
  rewrite sym (plusCommutativeBigInt (0-y) z)
  rewrite sym (sym $ differenceAsSum z y)
  trivial
