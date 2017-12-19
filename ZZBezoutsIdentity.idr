module ZZBezoutsIdentity

import Control.Algebra
import Classes.Verified

import Data.ZZ
import Control.Algebra.NumericInstances
import Control.Algebra.ZZVerifiedInstances
import Data.Matrix.AlgebraicVerified 	-- for (ringNeutralIsMultZeroL)

import ZZDivisors

import FinOrdering
import FinStructural

import Control.Isomorphism

-- Dependent pattern matching using (do) notation binds improves clarity
import Control.Monad.Identity
import Syntax.PreorderReasoning

import Control.Algebra.DiamondInstances



{-
Some algebra about groups
-}

groupSubtractionIsRDivision : VerifiedGroup t
	=> {auto ok :
		((<+>) @{vgrpSemigroupByGrp $ the (VerifiedGroup t) %instance})
		= ((<+>) @{vgrpSemigroupByVMon $ the (VerifiedGroup t) %instance})
		}
	-> (a, b : t)
	-> (a <-> b) <+> b = a
groupSubtractionIsRDivision {ok} a b = rewrite ok in
	trans (sym $ semigroupOpIsAssociative a (inverse b) b)
	$ trans (cong $ groupInverseIsInverseR b)
	$ monoidNeutralIsNeutralL a

groupDivisionAddLToSubR : VerifiedGroup t
	=> {auto ok :
		((<+>) @{vgrpSemigroupByGrp $ the (VerifiedGroup t) %instance})
		= ((<+>) @{vgrpSemigroupByVMon $ the (VerifiedGroup t) %instance})
		}
	-> (x, y, z : t)
	-> x <+> y = z
	-> x = z <-> y
groupDivisionAddLToSubR {ok} x y z pr
	= groupOpIsCancellativeR x (z <-> y) y
	$ trans pr
	$ sym $ groupSubtractionIsRDivision {ok=ok} z y

inverseIsInvolution : VerifiedGroup t
	=> (r : t)
	-> inverse $ inverse r = r
inverseIsInvolution r = groupOpIsCancellativeR (inverse $ inverse r) r (inverse r)
	$ trans (groupInverseIsInverseR _)
	$ sym $ groupInverseIsInverseL _



{-
About rings
-}

ringOpIsDistributiveSubR : VerifiedRing a
	=> {auto ok :
		((<+>) @{vrSemigroupByGrp $ the (VerifiedRing a) %instance})
		= ((<+>) @{vrSemigroupByVMon $ the (VerifiedRing a) %instance})
		}
	-> (l, c, r : a)
	-> (l <-> c) <.> r = l <.> r <-> c <.> r
ringOpIsDistributiveSubR {ok} l c r =
	( (l <-> c) <.> r )
		={ rewrite ok in Refl }=
	( (l <+> inverse c) <.> r )
		={ ringOpIsDistributiveR l (inverse c) r }=
	( l <.> r <+> (inverse c) <.> r )
		={ rewrite sym ok
			in cong $ ringNegationCommutesWithRightMult c r }=
	( l <.> r <-> c <.> r )
		QED
-- (but true by divisibility of addition even without associativity)

ringOpIsDistributiveSubL : VerifiedRing a
	=> {auto ok :
		((<+>) @{vrSemigroupByGrp $ the (VerifiedRing a) %instance})
		= ((<+>) @{vrSemigroupByVMon $ the (VerifiedRing a) %instance})
		}
	-> (l, c, r : a)
	-> l <.> (c <-> r) = l <.> c <-> l <.> r
ringOpIsDistributiveSubL {ok} l c r =
	trans (rewrite ok in ringOpIsDistributiveL l c (inverse r))
	$ rewrite sym ok in cong $ ringNegationCommutesWithLeftMult l r
-- (but true by divisibility of addition even without associativity)



{-
Dummy definitions - modulo & properties
-}

||| The nonnegative residue of the 1st modulo the subgroup generated by the 2nd.
||| Can factor through a modulo on naturals, but must be everywhere defined.
modZ : ZZ -> ZZ -> ZZ

quotientPartZ : (x, m : ZZ) -> (x <-> modZ x m) `quotientOverZZ` m

divZ : ZZ -> ZZ -> ZZ
divZ a b = getWitness $ quotientPartZ a b

reverifyDivZ : divZ a b <.> b <+> modZ a b = a
reverifyDivZ {a} {b}
	= trans (cong {f=(<+> (a `modZ` b))}
		$ getProof $ quotientPartZ a b)
	$ groupSubtractionIsRDivision a $ a `modZ` b

bezoutsIdentityLincombEqZZ :
	(a, b, c, d, q, r : ZZ)
	-> q<.>d = c <-> r
	-> b<.>c <+> (a <-> b <.> q)<.>d
		= a<.>d <+> b<.>r
bezoutsIdentityLincombEqZZ a b c d q r pr =
	(
	b<.>c <+> (a <-> b <.> q)<.>d
	) ={
		cong {f=((b<.>c) <+>)}
		$ (
		(a <-> b <.> q)<.>d
		) ={ ringOpIsDistributiveSubR _ _ _ }= (
		a<.>d <-> (b<.>q)<.>d
		) ={
			cong {f=((a<.>d) <->)}
			{- Bracketing style switch -}
			$ ( b<.>q<.>d ) ={ sym $ ringOpIsAssociative b q d }=
			( b<.>(q<.>d) ) ={ cong {f=(b<.>)} pr }=
			( b<.>(c <-> r) ) QED
			}= (
		a<.>d <-> b<.>(c <-> r)
		) ={ abelianGroupOpIsCommutative (a <.> d) _ }= (
		(inverse $ b<.>(c <-> r)) <+> a <.> d
		) QED
		}= (
	b <.> c <+> ( (inverse $ b<.>(c <-> r)) <+> a <.> d )
	) ={ semigroupOpIsAssociative _ _ _ }= (
	b <.> c <-> b<.>(c <-> r) <+> a <.> d
	) ={ abelianGroupOpIsCommutative _ (a <.> d) }= (
	a <.> d <+> ( b <.> c <-> b<.>(c <-> r) )
	) ={
		cong {f=((a <.> d) <+>)}
		$ trans (sym $ ringOpIsDistributiveSubL _ _ _)
		$ cong {f=(b<.>)}
		{- Bracketing style switch -}
		$ ( c <-> (c <-> r) )
			={
				cong {f=(c<+>)}
				$ trans (ringOpIsDistributiveR _ _ _)
				$ cong {f=((inverse c) <+>)}
				$ inverseIsInvolution r
				}=
		( c <+> (inverse c <+> r) )
			={ semigroupOpIsAssociative c (inverse c) r }=
		( (c <-> c) <+> r )
			={ cong {f=(<+> r)} $ groupInverseIsInverseL c }=
		( Algebra.neutral <+> r )
			={ monoidNeutralIsNeutralR _ }=
		( r ) QED
		}= (
	a<.>d <+> b<.>r
	) QED

bezoutsIdentityExtQuotientLincombZZ :
	(c, d, q, r, x : ZZ)
	-> (q<.>d <+> r = c)
	-> (d `quotientOverZZ` x)
	-> (r `quotientOverZZ` x)
	-> (c `quotientOverZZ` x)
bezoutsIdentityExtQuotientLincombZZ c d q r x eqpr (dq ** dqPr) (rq ** rqPr)
	= (q<.>dq <+> rq
	** trans (ringOpIsDistributiveR (q<.>dq) rq x)
	$ rewrite rqPr
	in trans ( cong { f= (<+>r) }
		$ trans (sym $ ringOpIsAssociative _ _ _)
		$ cong {f=(q<.>)} $ dqPr )
	$ eqpr)

bezQTy : (c, d, a, b : ZZ) -> Type
bezQTy c d a b =
	( c `quotientOverZZ` (a<.>c <+> b<.>d)
	, d `quotientOverZZ` (a<.>c <+> b<.>d) )

bezoutsIdentityZZ :
	( c, d : ZZ )
	-> ( zpar : (ZZ, ZZ) ** uncurry (bezQTy c d) zpar )
-- bezoutsIdentityZZ c (Pos Z) = ( (1, 0) ** ((1 ** _), (0 ** _)) )
bezoutsIdentityZZ c (Pos Z) = ( (Algebra.unity, Algebra.neutral)
	** rewrite ringWithUnityIsUnityR c
		in rewrite monoidNeutralIsNeutralL c
		in ( (Algebra.unity ** ringWithUnityIsUnityR c)
			, (Algebra.neutral ** ringNeutralIsMultZeroL c) ) )
bezoutsIdentityZZ c d with (bezoutsIdentityZZ d (c `modZ` d))
	| ((a,b) ** oldpr) = runIdentity $ do {
			(q ** qIsDivD) <- Id $ c `quotientPartZ` d
			((a' ** divsPrA), (b' ** divsPrB)) <- Id $ oldpr
			-- reverifyDivZ across the bind
			let reverifyDivZ' =
				trans (cong {f=(<+> (c `modZ` d))} qIsDivD)
				$ groupSubtractionIsRDivision c $ c `modZ` d
			-- the goal linear combo of c & d gives d `gcd` (c `modZ` d)
			let lincombEq = bezoutsIdentityLincombEqZZ
				a b c d q (c `modZ` d)
				$ groupDivisionAddLToSubR
					(q <.> d) (c `modZ` d) c
					$ reverifyDivZ'
			-- d `gcd` (c `modZ` d) | c
			let extQuotientLincombZZ = bezoutsIdentityExtQuotientLincombZZ
				c d q (c `modZ` d) ( a<.>d <+> b<.>(c `modZ` d) )
				reverifyDivZ'
				(a' ** divsPrA)
				(b' ** divsPrB)
			return $ ( (b, a <-> b <.> q)
				** ((getWitness extQuotientLincombZZ
					** trans (cong lincombEq)
					$ getProof extQuotientLincombZZ)
				, (a' ** trans (cong lincombEq) divsPrA)) )
		}
