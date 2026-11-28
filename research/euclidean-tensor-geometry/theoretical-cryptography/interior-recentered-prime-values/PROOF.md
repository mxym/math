# Recentring labelled root disks: an interior level-or-critical theorem

## 1. Public structure

For n>=2 put L=bitlength(n). Fix a positive integer r independent of L. A deterministic rule on L alone supplies r integer centres A_j of bit length polynomial in L; nonnegative integers R,W that are polynomial in L as numerical values; and a catalogue of monic integer polynomials of positive degree with deterministic polynomial construction time and total polynomial **dense coefficient encoding**. Every polynomial has a public label j such that its entire complex root multiset lies in the disk |z-A_j|<=R. There need not be any separations between the disks. A label is a property of the public catalogue, not information provided about the factors. Duplicate public centres may be allowed with separate labels; identical effective centres are merged for analysis. It can be checked by exact fixed-dimensional real algebraic decision on Re F(u+iv)=Im F(u+iv)=0 and (u-A_j)^2+v^2>R^2; each such test has two variables and polynomial degree and coefficient bits.

For the prime factorization n=prod_i p_i^{e_i}, require each distinct p_i to equal a catalogue value F_i(x_i)>1 at an integer x_i>=2. Some choice of these witnesses has max x_i-min x_i<=W. There is no side restriction on the witnesses relative to the public centres, and no bound independent of L on the number of factors or the degrees and exponents used.

**Theorem.** On this promise, deterministic complete prime factorization from n alone takes polynomial bit time, and membership in the promise is decidable in polynomial bit time. The theorem does not assert that a composite catalogue value can be decomposed or that a prime merely dividing an evaluation belongs to the class.

## 2. Effective centres from bounded integers

Write a=min x_i, delta_i=x_i-a in [0,W], and d_i=deg F_i. Multiplicity e_i lies on each repeated root of F_i. If F_i has label j, attach to it the translated multiset of all its roots rho=alpha-delta_i, counted e_i times. This multiset is the root multiset of F_i(X+delta_i) with repetition; its values at a are exactly the factor values at x_i. Each translated root lies at most M=R+W from its public centre A_j. Its total labelled count, weighted by multiplicity, is E_j. The total offset about A_j is

  S_j = sum_{i labelled j} e_i (sum_{alpha root of F_i} alpha - d_i(A_j+delta_i)).

The shifted sum is an **integer** by the coefficient of degree d_i-1 in each monic F_i and integrality of A_j,delta_i. The modulus bound is |S_j|<=M E_j. Neither S_j nor E_j is supplied. When E_j=0 set S_j=0 and ignore that group. Otherwise set C_j=A_j+S_j/E_j. Then the summed translated offsets about C_j are exactly zero and each translated root is at distance at most B=2M from C_j. The C_j are rational. If any coincide the weighted multisets may be merged, since each already has that centroid. This recentering does not guess each witness or each root. It uses one bounded integer statistic per label. For every input there is an a priori bound sum_j E_j<=D_L L, where D_L is the largest catalogue degree (take 1 for an empty list), since sum_i e_i<=L. Thus the nonzero E vectors and bounded S vectors are both enumerable in total polynomial size for fixed r. A sharper bound applies away from the centres.

## 3. A level-or-critical alternative with explicit constants

Set D=20(M+1) and Delta=4(B+1). If |a-A_j|<=D for some public centre, every true witness is in the explicit short interval [A_j-D,A_j+D+W]. Include all these intervals in the candidate set unconditionally. Otherwise |a-C_j|>=|a-A_j|-M>D-M=19M+20>2 Delta for every active centre. The absolute distance from a to any translated root is at least |a-A_j|-M>2, so multiplying across all roots yields n>=2^(sum E_j); on this branch sum E_j<=L. It is therefore sufficient to enumerate only sum E_j<=L in the construction of the far candidate set.

For a real t away from the active C_j put

  G(t)=prod_j (t-C_j)^{E_j},   g(t)=log|G(t)|,
  Q_2=sum_j E_j/(a-C_j)^2 > 0.

At the true vector, monicity gives log n = sum_rho log|a-rho|. For each translated root in group j write v=(rho-C_j)/(a-C_j), so |v|<=B/|a-C_j|<=1/2. The power series for log(1-v) gives

  |log|1-v|+Re v| <= sum_{m>=2} |v|^m/m <= |v|^2.

The sum of the real linear terms is zero group by group. Therefore

  |log n-g(a)| <= B^2 Q_2.

In the interval I=[a-Delta,a+Delta] there are no active centres. Differentiating explicitly gives g'(t)=sum_j E_j/(t-C_j) and -g''(t)=sum_j E_j/(t-C_j)^2. For t in I, |t-C_j|<=3|a-C_j|/2, hence -g''(t)>=(4/9)Q_2. If any g' zero is in I, it supplies the required critical point.

Otherwise g' has constant strict sign there. If positive, g'(a+Delta)>0 and curvature gives g'(a+s)>=(4/9)Q_2(Delta-s) for 0<=s<=Delta. Thus g(a+Delta)-g(a)>=(2/9)Q_2 Delta^2. Since g' is decreasing the left increment is at least the same magnitude. If negative, reflect through a and repeat the argument. Therefore the values at the two endpoints enclose g(a) with margin at least (2/9)Delta^2 Q_2 on each side; this is greater than B^2 Q_2. The intermediate value theorem yields a point z in I with g(z)=log n. In either case the unknown a lies within Delta of a level point or a critical point. The analysis permits the observed value to lie above the maximum of g on its gap; in that case no level root in the gap is needed. No logarithm is computed by the algorithm.

## 4. Finite candidate set with exact bit complexity

For each E vector with sum<=L and S_j in [-M E_j,M E_j], inspect the following real roots. Let the products below use only indices with E_j>0.

* For levels, isolate the real roots of both integer polynomials
  prod_j (E_j(t-A_j)-S_j)^{E_j} - n prod_j E_j^{E_j}
  and the same with + n prod_j E_j^{E_j}.
  The roots are exactly the real points with |G(t)|=n. The denominators have been cleared by a positive scalar; the equations have degree sum E_j and are not identically zero.
* For critical points, first merge identical rational C_j into distinct D_j with total weights f_j>0; if there is just one active centre, there are no critical points. For s distinct active centres compute the polynomial
  sum_{j=1}^s f_j prod_{k != j}(t-D_k).
  It is degree s-1 with positive leading coefficient, and is nonzero at every D_j (only the j-th summand survives at D_j). Its real zeros are exactly the noncentre critical points of g. Clear denominators before isolation.

Between any two consecutive active centres, g' decreases from +infinity to -infinity, thus there is exactly one simple critical point in that gap. On the two exterior intervals all summands in g' have the same sign, hence no critical point. Strict monotonicity on each side of a critical point bounds each gap to two distinct level points and each exterior interval to one. Thus even if degree is large there are at most 2s level points and s-1 critical points. A multiple root of a level equation (for example a tangent at a critical point) is not a problem: isolate distinct real roots via square-free parts. Roots forced by repeated centre factors do not enter either level equation and are not critical candidates.

Integer coefficients of the level equations have bit length polynomial in L: there are fixed many factors, each linear coefficient has bit size O(max_j bitlength(A_j)+log(L(M+1))+1), and the total expansion degree is <=L. Products by binomial expansion or dense arithmetic and denominator factors therefore stay polynomial in bit size. The same is immediate for the fixed-degree cleared critical equation. Standard deterministic real root isolation and refinement give rational isolating intervals of width at most 1 in polynomial time in degree and coefficient bits. There is no need to decide by floating rounding whether a root exactly equals an integer. Enumerate all integer x>=2 within distance Delta+W+1 of each such interval (the +1 is harmless). Every true x_i lies in this set or one of the near-centre intervals by section 3. The total count is polynomial since r is fixed, M,W are polynomial, and all interval endpoints have polynomial bit size.

Evaluate the publicly encoded polynomials exactly at these candidate integers, keeping only positive prime values <=n (deterministic primality). Retain all witnessed bases for repeated prime values. Exact division by the candidate primes extracts all the true primes and their multiplicities on promised inputs. A nonunit residual certifies nonmembership. A unit residual gives a correct factorization; to decide the actual promise, test for an interval of length W with a witnessed base for every extracted prime. Enumerate only left endpoints among the retained bases. If witnesses exist, the true minimum is included in the candidate set and one such interval passes; if an interval passes, its witnessed bases are exact polynomial equalities giving the required certificate. This proves the complete statement for the given public class. It supplies neither an algorithm for general factoring nor an input-taking implementation in this package.

## 5. Strict geometry and exact fixtures

The one-sided multi-disk envelope already applies to candidates with all witnesses to the right of the public disks, including catalogue polynomials whose roots span several disks. The present result trades that per-polynomial flexibility for publicly labelled single-disk polynomials, but drops the one-sided requirement entirely and still permits a cluster of hidden arguments rather than requiring that they coincide. Even a common stationary point alone would not be enough without a second-order bound: the first-coefficient recentering makes that bound uniform without a hidden centroid hypothesis.

Take public centres (-123,130), R=3, W=1, and the labelled quadratics (X+123)^2+1, (X-130)^2+5. At x_1=3, x_2=4, the respective values are 15877 and 15881, both prime. Here a=3, E=(2,2), S=(0,-2), C=(-123,129), D=100, Delta=36. The true a is outside both near-centre windows. It is exactly the critical point of |G| between the effective centres. In that gap |G|<=126^4 but n=(126^2+1)(126^2+5)>126^4. The exterior level roots are also more than Delta from a, since any real t with |G(t)|=n must have (t-a)^2=126^2+sqrt(n). Thus for this true aggregate, a nearby critical point is needed in the stated localisation argument: there is no nearby level point for that aggregate. This example is not an ablation claim for the full enumeration, in which another, non-witness aggregate may happen to supply a nearby level point. This is a fixed illustrative number-theory fixture, not an asymptotic prime-value or density claim.
