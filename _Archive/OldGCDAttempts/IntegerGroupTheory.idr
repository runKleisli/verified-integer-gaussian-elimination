module IntegerGroupTheory



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
