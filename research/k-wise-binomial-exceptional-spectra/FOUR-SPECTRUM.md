# Exceptional four-wise binomial parameters: exact arithmetic spectrum and rarity in the number of bits

Let an *exceptional point* of Berend–Ernst–Kontorovich–Kumar (BEKK, §5.2–5.3) mean an interior change between consecutive positive-length optimal phases at which at least two distinct basis sites depart. Fix k=4. For an integer n≥6 put N=n−1, V=n−2. The following results concern the two-departure event, not feasibility of an arbitrary isolated basis.

1. For 0<p<1 let s=1+2Vp and D=√(1+4Vp(1−p)). The parameter is exceptional at n **if and only if** s and D are integers of the same parity and D≥3.
2. Every rational p in (0,1) is exceptional for infinitely many n. Conversely, every four-wise exceptional point is rational (the inclusion itself is prior). In particular the union of these sets over n is exactly the rationals in (0,1).
3. Let E₄(X) count the integers n≤X with at least one such point. With absolute positive constants, for large X,
   
       √X log X ≪ E₄(X) ≪ √X (1+log X)^8.
   
   Thus E₄(X)=X^(1/2+o(1)) and the set has natural density zero, but it is more numerous than the single symmetric-parameter sequence by an unbounded factor. No sharp logarithmic exponent or statement for every fixed k is claimed.

## Exact criterion and its relationship to the previous classification

The previous [four-wise manuscript](../k-wise-binomial-optimal-bases/FOUR.md) already classified individual paired bases, including isolated feasible parameters, by two quadratic inequalities; its final argument proves rationality at four-wise exceptional points. The two-site test below is a reformulation of that quadrature calculation which identifies a genuine transition, not a claim of a new formula for roots of the degree-two binomial orthogonal polynomial. The scope added here is chiefly the converse across n and the size of the set of exceptional n.

At an exceptional interior transition the old basis has two pairs of consecutive count sites in addition to n. The [phase characterization](../k-wise-binomial-optimal-bases/PROOF.md) reweights the nondistinguished masses to a positive quadrature for X~Bin(N,p) through degree three. Only lower members of old pairs can vanish; two departures therefore force both of them to vanish, leaving two distinct sites u<v. The monic quadratic Q(x)=(x−u)(x−v) is orthogonal to 1,x for the binomial law. Denote t=Np, W=Np(1−p), c=1−2p. The centered binomial second and third moments W,Wc show directly that
   
       Q(x)=(x−t)^2−c(x−t)−W.
   
Its roots straddle t strictly, have sum 2t+c=s, and squared difference c²+4W=D². They lie strictly in (0,N): Q(0)=N(N−1)p²>0, Q(N)=N(N−1)(1−p)²>0, and Q(t)<0. Conversely the positive two-site law on these roots with mean t is exact through degree three: divide any cubic by Q; the multiple of Q has degree at most one times Q and integrates to zero, and the linear remainder is determined by the mean.

At the transition, the old pairs have to be {u−1,u}, {v−1,v}; the new pairs have to be {u,u+1}, {v,v+1}, because at this interior transition each upper member of the old basis and each lower member of the new basis has positive mass. Equivalently, these are the only possible pairs for the positive sites by the strict tilted-mean sign rule. In particular the positive integer gap D=v−u is at least 2. If D=2 those sets of four sites differ in only one actual departure, not two; D=1 cannot form the old four distinct sites. Thus D≥3 as claimed. Conversely, for integral roots u,v with D≥3 these two proposed paired supports lie on the grid, with disjoint pairs, and have the same nonnegative two-site quadrature at p. In the old support the upper weights are positive; the two zero lower weights are strictly positive just to the left, since each pair's strictly increasing tilted mean crosses the upper node there. In the new support the lower weights are positive, and the zero upper weights become strictly positive just to the right. The distinguished weight is positive in the interior (for example, every optimal objective is at least p^n). Thus these are neighboring positive-length phases, and exactly two sites depart. Finally u=(s−D)/2, v=(s+D)/2 are integers precisely under the stated parity condition. At n=5 (outside the range above) the two positive-length phases differ in only one site, so adding this boundary does not alter the counts.

## All rational probabilities occur

Write |2p−1|=a/b in lowest terms with 0≤a<b, using 0/1 at p=1/2, and d=b²−a². Choose any j≥1, put D=1+2dj, L=(D²−1)/d=4j(1+dj), V=b²L and n=V+2. Then 1+4Vp(1−p)=1+dL=D², and s=1+b(b±a)L is odd, as is D≥3. Each j produces a different n. Conversely s integral implies p=(s−1)/(2V) rational. For p=1/2 the exact criterion reduces to n=D²+1 with D≥3; parity is automatic.

## Upper count

For any exceptional n, use the reduced a/b and d from above. The identity D²−1=Vd/b² and gcd(b²,d)=1 imply b² divides V and d divides D²−1. For each integer 3≤D≤√X, there are at most τ₃(D²−1) possibilities for n, with τ_j counting ordered j-factorizations in positive integers. Indeed (b−a,b+a,(D²−1)/d) is such a triple and recovers V=b²(D²−1)/d. Counting triples may overcount n. The function τ₃ is submultiplicative even without coprimality: prime by prime, any ordered exponent triple of total e+f can be canonically split into ordered triples of totals e,f (fill the first in fixed coordinate order). Thus
   
       τ₃(D²−1) ≤ τ₃(D−1) τ₃(D+1).

Moreover τ₃(h)^2≤τ₉(h): primewise, from two exponent triples of the same total, form a 3×3 nonnegative integer matrix with those row and column sums, deterministically by filling the first remaining row and column greedily. The margins recover both triples, giving an injection into nine-part exponent compositions. Iterated harmonic sums give Σ_(j≤Y) τ₉(j) ≤ Y(1+log Y)^8, by summing 1/(d₁⋯d₈) over the first eight factors. Applying Cauchy–Schwarz to the preceding display summed to √X proves the upper bound.

## Lower count for distinct n

Use slopes a/b in [1/4,1/2] in lowest terms with b≤T=⌊X^(1/10)⌋. Put c=1−(a/b)²∈[3/4,15/16] and fix p=(1+a/b)/2; no reflected probability is counted. The construction D=1+2dj used above contributes at least C√X/b²−1 different n≤X for an absolute C>0 since n=(D²−1)/c+2 and d≤b². There are O(T²) slopes.

For completeness the number of slopes with denominator ≤Y in this interval is κY²+O(Y log(2Y)) for a constant κ>0. By Möbius inversion it is
   
       Σ_(m≤Y) μ(m) Σ_(v≤Y/m) #{v/4 ≤ u ≤ v/2, u integral}
       = Y²/(8ζ(2)) + O(Y log(2Y)).
   
Hence each sufficiently large dyadic denominator block (Y/2,Y] contributes ≫1 to the sum of 1/b²; the weighted total over all slopes is ≫log T.

The count with multiplicity consequently exceeds a constant times √X log T−O(T²). To control double counting, fix distinct slopes with values c₁,c₂. Every common n yields positive integers D₁,D₂ with
   
       (D₁/D₂)^2=c₁/c₂+(1−c₁/c₂)/D₂².
   
Here c₁≠c₂, so the ratio determines D₂ and n uniquely. For Y≤D₂<2Y its distance from √(c₁/c₂) is at most C'/Y² for an absolute constant, since the c's stay in the stated compact interval. Two distinct such rational ratios differ by at least 1/(4Y²), by the integer cross product, whether or not either fraction is reduced. Thus O(1) common n arise per dyadic block, O(log X) for the entire pair. The sum of all pairwise intersection sizes is O(T⁴ log X)=o(√X). Subtracting it from the sum of the set sizes proves the stated lower bound for distinct n. The counting uses no distributional assumption on the exceptional points.
