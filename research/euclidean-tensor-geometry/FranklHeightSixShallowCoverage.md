# Frankl at height six: a shallow-chain coverage theorem

**Yongxian Zhang.** AI-assisted proof development and internal verification; no external peer review or priority claim.

Use the empty-set-free strict-majority formulation. Let F be a nonempty finite union-closed family of nonempty sets with union U, n=|U| and inclusion height at most six, counting members of a chain. Let G={U\A : A∈F}. Then G is intersection-closed, contains ∅, and omits U. Call a four-subset Q of U covered if it contains a chain B_1⊂B_2⊂B_3 of members of G with |B_i|=i. Equivalently F has a chain of one-, two- and three-element complements supported in Q.

**Theorem.** F has a strict-majority element if every four-subset is covered. More generally, if n≥47, it suffices that at least 23/24 of all four-subsets are covered. Asymptotically, for any fixed ε>0, a covered proportion ≥15/16+ε suffices for all sufficiently large n. No assertion is made for general height six.

## Structural and incidence bounds

Suppose all element frequencies in F are at most |F|/2. Every coordinate then occurs in at least |G|/2 members of G. Split G into a shallow portion S of sets of size ≤3 and the deep portion of size d. Put M=∑_{B∈S}(1-2|B|/n). The sum of cardinalities over the deep portion is at least n(d+M)/2, by subtracting the shallow sum from n|G|/2. Also d≥M by the weaker bound |V|≤n on deep V. For n≥7, all shallow summands are nonnegative. Write C=binom(n,4), u=#uncovered four-subsets. At least (C-u)/(n−3) triples belong to G because each witness triple covers at most n−3 four-subsets. Hence
M ≥ (1−6/n)(C-u)/(n−3) = (1−u/C)(n−1)(n−2)(n−6)/24.

Fix a covered Q. If the family of G-members containing Q is nonempty, its intersection I belongs to G and contains Q. It sits above the four-member chain ∅, B_1, B_2, B_3. Because height is at most six, the containing family has height at most two. Any two of its strict supersets of I are incomparable and intersect exactly in I: if their intersection strictly exceeded I, the intersection would be strictly between I and a strict superset. Their nonempty increments over I are therefore disjoint. The containing family has at most 1+n−|I|≤n−3 members.

Double-counting (deep member, contained covered four-subset) gives
∑_{V deep} binom(|V|,4) ≤ (C-u)(n−3)+du.                 (1)
There is no assumption that Q itself lies in G.

## Complete coverage

When n≤12, use the [12-element theorem of Vučković and Živković](https://ipsitransactions.org/journals/papers/tir/2017jan/fullPaper.pdf) (2017, 13(1), 65–71; [author bibliography](https://poincare.matf.bg.ac.rs/~ezivkovm/publications/pub.htm)), after adjoining the empty set to F, which yields strictly more than half in F by integrality. For n≥13, choose a constant K below or equal to every binom(s,4)/(s−n/2) with integer n/2<s≤n−1. For s≤n/2, nonnegative binom(s,4) already implies binom(s,4)≥K(s−n/2). Summing and invoking (1) with u=0 is incompatible with K>2(n−3)^2/(n−6), since K nM/2 > C(n−3).

For n=13 the exact minimum K across s=7,...,12 is 140/3; at n=14 it is 63 across s=8,...,13. Both exceed the requisite threshold. For n≥15, write x=s−n/2>0 and b=n/2−3. Then binom(s,4) ≥ (s−3)^4/24, whose ratio to x is at least 32b^3/81, obtained by minimizing (x+b)^4/(24x) at x=b/3. This is 4(n−6)^3/81, greater than 2(n−3)^2/(n−6) at n=15 and after, since 2(n−6)^4/[81(n−3)^2] starts above one and increases (logarithmic derivative 4/(n−6)−2/(n−3)>0).

Complete coverage does not mean having every co-triple. For example, partition U into three nearly equal parts labeled cyclically, take all singletons and pairs as shallow complement members, and take as triples those lying entirely in one part or having two elements in part i and one in part i+1. Every four-set has one of these triples: distributions 4 and 3+1 use a monochromatic triple, 2+2 uses one of the two directed choices, and 2+1+1 always contains the successor part of the doubled part. This intersection-closed shallow pattern has asymptotic triple density 4/9.

## Approximate coverage

The function binom(s,4), interpreted as the polynomial s(s−1)(s−2)(s−3)/24, is increasing and convex for s≥4 (polynomial in y=s−3 with positive coefficients). Average deep size ≥n/2 gives by Jensen
d(binomial(n/2,4)−u) ≤ (C-u)(n−3).                      (2)
Set z=1−u/C>0 and A=(n−1)(n−2)(n−6)/24, so d≥zA. The exact ratio R=binom(n/2,4)/C is (n−4)(n−6)/[16(n−1)(n−3)]. When R>u/C, dividing (2) by zC gives A(R−u/C)≤n−3. For u≤C/24 this is false for n≥47: at n=47, A(R−1/24)/(n−3)>1 by exact integer comparison, and both R=(1−3/(n−1))(1−3/(n−3))/16 and A/(n−3)=(n−1)(n−2)(1−3/(n−3))/24 increase. The asymptotic claim follows since R→1/16 and A/(n−3) tends to infinity.

## Bounded holes instead of high global coverage

Let k≥5 and b=binom(k,4). If every k-subset of U contains a covered four-subset, and n≥22√b, then F has a strict-majority element. The requirement is local, not a near-full global coverage assumption. The k=4 case is the all-covered theorem above.

For a set V of size s≥k, count pairs (k-subset of V, covered four-subset in it). Each k-subset contributes at least one, so V contains at least binom(s,4)/b covered four-subsets. For 4≤s<k, the weaker lower bound [binom(s,4)−binom(k−1,4)]/b is automatic from nonnegativity and holds for s≥k as well. Let z>0 be the actual global covered fraction. Using this per-deep-member bound in the covered-subset double count and applying Jensen gives
d[binom(n/2,4)−binom(k−1,4)] ≤ bzC(n−3).
Since d≥zA, cancellation gives A(R−B)≤b(n−3) when R>B, where B=binom(k−1,4)/C. For k=5, n≥50; direct comparison at n=50 is strict in the other direction, and R increases, B decreases, and A/(n−3) increases with n. For k≥6, n≥86 and b≥(k−1)^2/4, the latter following from k(k−2)(k−3)≥6(k−1). Thus B≤((k−1)/n)^4≤1/11^4; R−B≥R(86)−1/11^4>1/18. Also A/(n−3)≥(85/86)(84/86)(80/83)n²/24>9n²/240. Their product exceeds 9·484b/(240·18)>b.

## General fixed-height form

For height at most h≥5, set r=h−3 and l=r+1 (take h fixed). Call an l-subset covered if it contains a chain of complement-family members of sizes 1 through r. The same proof gives strict majority whenever the covered density exceeds 1−2^(-l) by any fixed positive amount and n is sufficiently large depending on the amount and h. In fact, with z the covered density, at least z*binom(n,r)/l shallow r-sets are present, so M≥zA_r where A_r=(1−2r/n)binom(n,r)/l. A covered l-set has at most n−l+1 containers by the height-two argument, and the deep average is at least n/2 as before. With C_l=binom(n,l), the moment inequality is A_r[binom(n/2,l)/C_l−(1−z)]≤n−l+1 if the bracket is positive. The ratio tends to 2^(-l) and A_r grows like n^r. For bounded holes (every k-subset contains a covered l-set), the same local incidence count gives A_r[binom(n/2,l)/C_l−binom(k−1,l)/C_l]≤binom(k,l)(n−l+1) when the bracket is positive. Hence n≥c_h k^(l/(r−1)) suffices for a constant c_h depending only on h: choose c_h large so n≥4k, the bracket stays above a positive constant (e.g. half of 2^(-l) for n sufficiently large), then compare n^(r−1) with binom(k,l). Neither criterion implies an unconditional bounded-height theorem.

## Comparison and scope

[Tian, arXiv:2608.25147](https://arxiv.org/abs/2608.25147) established height four and partial reductions at five. Two subsequent preprints claim height five: [Wang, Zenodo 23252932](https://zenodo.org/records/23252932) and [we-solve Math-7809](https://we-solve.github.io/contributions/frankl-s-union-closed-sets-conjecture-964c25bb/attempt-3/r1/). Our counting strategy is an extension of the latter preprint's §6 full-pair third-moment method, using fourth moments on covered four-subsets, not a claim to invent the incidence method. That preprint §8 explicitly does not address height six. No matching height-six shallow-chain coverage theorem surfaced in the checked sources. The above proof does not depend on either height-five claim. The announced broader entropy lower bound [Quantavane, 0.383175...](https://quantavane.com/major-results/union-closed-sets-conjecture/) has no linked proof, so cannot be audited here and is orthogonal.

