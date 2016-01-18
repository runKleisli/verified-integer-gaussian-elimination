module IntegerArith

import IntegerOrdering
import IntegerGroupTheory



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

=======

Strategy recursion:

gcdBigInt can probably be reduced to a single case expression step followed by the usual gcd on nonnegative numbers, which by not having a case expression can be proved total just like gcd can. So gcdBigInt could be proved total simply by factorization.

-}



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



total
modBigInt_total : Integer -> Integer -> Integer
modBigInt_total a 0 = a
-- This is wrong too, in fact (div 5 (-2) = -3), so not even close.
-- I suspect we must define remainders as coset representatives or by long division.
modBigInt_total a b = a - div a b

{-
Would have said

	modBigInt_total a b = prim__sremBigInt a b

but need to be able to prove modEqBigInt.
If we can't prove this, we might as well switch to a definition of div in.
-}
modEqRem : (a : Integer) -> (b : Integer) -> (nzpr : Not (b=0)) -> (a - div a b = prim__sremBigInt a b)



{-
modeqBigInt : (a : Integer) -> (b : Integer) -> (nzpr : Not (b=0))
	-> mod a b + (div (a - mod a b) b)*b = a
-}

modeqBigInt : (a : Integer) -> (b : Integer) -> (nzpr : Not (b=0))
	-> modBigInt_total a b + (div (a - modBigInt_total a b) b)*b = a
modeqBigInt a b pr = ?modeqBigIntHole
