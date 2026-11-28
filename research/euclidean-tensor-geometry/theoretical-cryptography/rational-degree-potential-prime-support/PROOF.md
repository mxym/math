# A rational degree potential on connected prime supports

## 1. Uniform model and statement

Fix relatively prime positive integers a>b, write lambda=a/b, and regard them as constants of the family, not as input-dependent parameters. For each positive integer L a public deterministic rule, running in polynomial time in L, returns a finite list of pairs (F_s,G_s) of monic, positive-degree polynomials over Z, as dense coefficient lists of total binary size polynomial in L. It also returns an integer R=R(L)>=1, numerically polynomial in L, such that the roots of all polynomials in the list are in |z|<=R. Thus the degree, the number of polynomials and the coefficient bit lengths are separately polynomially bounded. Every degree quotient deg(F_s)/deg(G_s) belongs to lambda^Z. The public data depend on L, not on the input integer or on any of its factors.

One can instead compute a root bound from the catalogue. For a monic polynomial T^d+sum_{i<d} c_i T^i, let M be the maximum of 1 and the least integers m_i>=0 with m_i^(d-i)>=|c_i|. For |z|>2M, the sum of the lower terms in absolute value is strictly smaller than |z|^d by the geometric series bound, so 2M is a valid radius. If some radius bound R_0>=1 on the root moduli is numerically polynomial, expansion in the roots gives |c_i|<=binom(d,d-i) R_0^(d-i)<=(d R_0)^(d-i). Thus computing the maximum of these explicit bounds still gives a polynomial radius. These comparisons, and testing that each degree quotient is an integer power of fixed lambda by exact rational powers, are polynomial bit operations. This observation is about certifying the public catalogue, not testing a condition on unknown primes.

For N>=2 set L=bitlength(N) and let V(N) be its distinct prime support. Its relation graph on V(N) has an oriented labelled edge from distinct p to q when F_s(p)=G_s(q), with increment k_s determined by deg(F_s)/deg(G_s)=lambda^k_s. Traversal in reverse has increment -k_s. Retain all labels in this multigraph; connectivity ignores orientations and labels. A singleton is connected. The promise is that this graph is connected; neither a relation on a particular pair, nor a tree, seed, multiplicity, or support size is supplied. No claim is made that any chosen pair of polynomials has infinitely many prime solutions.

**Theorem.** There is a deterministic bit-polynomial recognizer for the promised class which outputs the complete prime factorization when it accepts. The input is only N, with the fixed public catalogue rule above. There is no fixed bound on the distinct support size, multiplicities, or the diameter of the support graph. No complexity bound is asserted for factoring outside this class: on an unpromised input the procedure rejects rather than promising to factor it.

## 2. Root bounds and edge comparison

Let P=min V(N), and write N=prod_{p in V(N)} p^{e_p}. We use the analytic estimates only in the completeness proof, not as arithmetic operations in the procedure.

For a monic real polynomial F of degree d with all roots |z|<=R, F(t) is positive on t>R, because it has no zeros there and is positive for large t. The product over its roots, using absolute values on each complex factor, gives
```
(t-R)^d <= F(t) <= (t+R)^d.
```
For t>=2R this yields
```
log(F(t))/d = log(t)+epsilon_F(t),     |epsilon_F(t)| <= 2R/t.       (1)
```
The undivided logarithmic error is at most 2dR/t; division by d in (1) is essential and gives the stated degree-independent constant. Indeed |log(1+u)|<=2|u| for real |u|<=1/2. Also F is strictly increasing for all t>R. Its logarithmic derivative is the sum of 1/(t-z) over its roots with multiplicities, a real number. Every summand has positive real part because t>R>=Re(z).

Let A_0 be the least positive integer for which lambda^A_0>=2 and define B=16 A_0 L R. If a prime p<=B divides N it can be found among the small candidate seeds; see §4. For the rest of the proof suppose P>B, so P>=3, log(P)>1 and (1) holds on the whole support. On an oriented edge p to q with increment k,
```
log(q)+epsilon_G(q) = lambda^k (log(p)+epsilon_F(p)).               (2)
```
All parenthesized quantities are positive. Taking another logarithm and subtracting log log of each endpoint gives
```
|log log(q)-log log(p)-k log(lambda)| <= 8R/(P log(P)).              (3)
```
To check the constant, each logarithm correction is log(1+epsilon_F(p)/log(p)) or its G counterpart, with |epsilon_F(p)/log(p)|<=2R/(P log(P))<1/2. Each is therefore at most 4R/(P log(P)) in magnitude.

## 3. Potential and additive localization

Choose any spanning tree of the true graph for the analysis only. Define integer heights along it by summing the signed increments from one vertex. The heights automatically extend to all labelled edges at large P. In fact, a non-tree edge together with its tree path makes a closed walk of length at most |V(N)|<=L, allowing a two-edge walk for a second label on the same pair. Sum (3) along that closed walk. The log-log differences telescope and the remaining error is at most 8LR/(P log(P))<1/(2A_0)<=log(lambda), where log 2>1/2 was used. The sum of the increments, being an integer, must be zero. Thus every edge agrees with the tree heights. In particular their differences are independent of the choice of tree.

Subtract the minimum height from all heights, write h_p>=0 for the result and let x be any support vertex of height zero. Set w_p=lambda^(-h_p) log(p). For an edge p to q, (2) now implies
```
|w_q-w_p| <= 2R(lambda^(-h_q)/q + lambda^(-h_p)/p) <= 4R/P.
```
The path from x to any vertex therefore gives
```
|w_p-log(x)| <= delta := 4LR/P < 1/4.                             (4)
```
In particular w_P<=log(P) as h_P>=0, so x<=exp(delta)P<=2P. Also w_p>=log(x)-delta>=log(3)-1/4>log(2) for every p. Let
```
E=sum_{p} e_p lambda^(h_p).
```
It is at least one, and log(N)=sum_p e_p lambda^(h_p) w_p, so E<=log(N)/log(2)<L. From the very same identity, log(N)/E is a convex weighted mean of the w_p's. Thus its distance from log(x) is at most delta and, using exp(delta)-1<=2 delta for 0<=delta<=1/4,
```
|N^(1/E)-x| <= x(exp(delta)-1) <= 4P delta = 16LR.                 (5)
```
This is additive in the actual prime variable, not a bound only on a logarithm. It arises from normalizing the edge errors before propagation; multiplying the errors by unnormalized degree quotients can give a false path bound.

Let H=max{h>=0: a^h<=L b^h}, computable by fixed-integer comparisons. From e_p>=1 and E<=L, every h_p<=H. Put D=b^H. The integer D is polynomial in L: it is 1 when b=1; otherwise choose a fixed integer c with b<=lambda^c to obtain b^H<=lambda^(cH)<=L^c. The true E equals J/D with an integer D<=J<=LD. No guess of the individual heights, graph or multiplicities is needed. This includes fractional ratios, not just integer-base heights.

## 4. Deterministic consequence and bit accounting

All candidate seeds are positive integers in [2,N]. Include those up to B. For every D<=J<=LD include the integers within 16LR+1 of the integer part of N^(D/J). The integer part is obtained without floating point by searching [1,N] for the largest integer t with t^J<=N^D. Equation (5) proves that at least one true seed is on this list on every connected promised input with P>B. If P<=B the small portion already supplies one. In forming the list one may clip every interval to [2,N]. Test that a seed is a prime divisor by deterministic primality testing and exact division.

The closure under exact labelled relations is considered only on prime divisors of N: given one retained prime p, and one catalogue pair, compare G_s(Y) to the integer F_s(p), then also F_s(Y) to G_s(p). On [2,R] simply enumerate the integers (clipped to [2,N]); on the integer interval R<Y<=N strict monotonicity from §2 leaves at most one match, findable by an exact binary search with evaluation, including testing equality at its endpoint. This also treats nonpositive target integers and all polynomial values on the small interval. Retain just distinct neighbouring prime divisors, and process a retained node once per closure. Self-edges are not used. The closure therefore has at most |V(N)|<=L vertices no matter how many label sequences exist. This does not enumerate spanning trees or paths.

For each candidate that passed the divisor and primality tests, its closure gives a connected subset of the exact graph. Repeated division by its listed primes yields their full valuations and a remaining integer. If one closure gives remaining integer 1, accept with the resulting factorization; otherwise reject. For completeness, the true seed is present on a connected input and its closure reaches all vertices, so the remaining integer is 1. For soundness, a remaining integer 1 proves that all prime divisors are accounted for, and the closure's relation witnesses connect that whole set. This includes prime and prime-power inputs under the singleton convention, and excludes N=1 from the stated model. If a small seed has incomplete closure, that alone is not a reason to accept. A large polynomial value need not be at most N: it is an edge label evaluation, not necessarily a divisor.

The seed list size counting duplicates is at most B+(LD-D+1)(32LR+3). Each of its root comparisons has integers of O(L max(D,LD)) bits, with at most O(L) comparisons per J and polynomial-time integer powering. If d bounds the two degrees and C the coefficient bit lengths, evaluation on [2,N] has intermediate integer bit lengths O(dL+C+log(d+1)); Horner evaluation therefore has polynomial bit cost. The neighbour searches need at most R+O(L) evaluations per polynomial per node. There are polynomially many candidate seeds and labels and at most L nodes per closure. Primality and integer division have polynomial bit complexity. This proves the unconditional deterministic bit bound in this fixed catalogue family. It uses no modulo-polynomial small-root theorem, factoring oracle, or location bits supplied with N.

## 5. Fixed unequal-degree fixture and limits

Let x=1000003, y=1000033 and z=1000004507, all prime. The fixed catalogue consists of the two pairs
```
(T^3 + 13993 T + 271043,             T^2),
(T^3 - 90 T^2 + 16694 T - 1175780,   T^2).
```
With lambda=3/2, its distinct-prime graph on {x,y,z} has precisely the two labelled edges x to z and y to z; each has increment 1. Thus neither height-zero vertex alone reaches the other by only forward oriented edges. The configuration is connected as required, without a common forward origin. Take multiplicities (1,2,1). Then N=1000073508597992067523724369, L=90, R=260 is certified by §1 and P>B=748800. The normalized heights are (0,0,1); E=9/2, H=11, D=2048 and J=9216. The exact center floor(N^(2/9)) is 1000016, in the stated additive neighbourhood of both height-zero vertices. This is a finite arithmetic illustration, not an asymptotic existence or density statement.

This theorem is a narrow input predicate: it assumes exact equalities of values of uniformly public monic pairs, bounded root radii, and one fixed rational generator of the relative degrees. A public catalogue cannot be picked after seeing unknown factors of the input. Nonmonic drift, arbitrary degree-ratio groups, disconnected supports and numerical approximate edges are not covered. Neither the powers of lambda nor the valency of the relation graphs (on integers rather than the actual prime support) are claimed small uniformly in the integer value.
