# One numeric totient: a valuation-rank criterion with one missing direction

## 1. The rank is a promise, not side information

Fix integers k>=2 and A>=1. Input is an odd integer N>=3 and T=phi(N) in binary, with bitlength(N)=L. The unknown set S of distinct prime divisors has size at most k, and max(S)<=A min(S). Write P=min(S). On S draw p -> q when p divides q-1, let t be its number of weak components, and let e_p=v_p(N). For p in S define the rational profile rho_p=v_p(T)/e_p. Form the matrix with one row per occurring profile and one column per weak component:
```
E[j,i] = sum of e_p over vertices p in component i with profile j.
```
**Theorem.** If rank_Q(E)>=t-1, the entire prime factorization including multiplicities can be computed deterministically in time polynomial in L. Constants may depend on k,A. No matrix, graph, number of components, witness for the rank, individual profile, or factorization of the totient is supplied. One never queries a totient oracle. There is no diameter-of-cluster condition other than the fixed ratio.

We use the following fixed constants to make all large-input estimates uniform over false templates as well. Put
```
H=(A+1)^(k+1),  Z=k^2 H L,  Q0=16 A k^2 Z^k .
```
Trial divide through Q0. If a prime factor is found, divide completely through A Q0, which suffices on the size promise. Both limits are polynomial in L for fixed k,A. From now on P>Q0 (in particular P>A). Every edge increases the prime; no vertex can have two parents, since their product would be >=P^2 but would divide q-1<AP. Nor can p^2 divide q-1. Thus the graph is a forest of rooted out-trees: the greatest vertex on an undirected cycle would have two parents. Every node is at least its root, so min of the true roots equals P.

## 2. Obtaining all profile products

At these sizes, for d_p the outdegree, Euler's formula gives v_p(T)=e_p-1+d_p. Each edge contributes exactly one (and a nonedge zero); multiplicities of children do not multiply this contribution. Thus every true j is among the reduced fractions (e-1+d)/e for 1<=e<=L, 0<=d<k. Enumerate and deduplicate these fractions; there are O_k(L) of them.

For any reduced fraction j=b/a>=0 with a>=1 form exactly
```
J = gcd(N^b,T^a),     W=(N^b/J)(T^a/J),
N_j = N/gcd(N, W^L mod N).
```
The two quotients defining W are coprime. For p|N its W-valuation is |b e_p-a v_p(T)|, so saturation by exponent L removes precisely the full N-powers for unequal valuations. Consequently N_j is the product of p^e_p for exactly that profile. Primes of T outside N do not matter. The case j=0 has (a,b)=(1,0), J=1 and W=T; no positive-valuation assumption is made. Keep the nonunit N_j. They are pairwise coprime and multiply to N on the true input. The powers before the gcd have O(L(L+k)) bits, and modular powers and gcds have polynomial bit cost. This is elementary arithmetic on valuations, not a polynomial-time general factorization of either input.

## 3. Enumerating bounded affine templates

Enumerate r<=k, every labelled rooted forest on r vertices, every edge slope 1<=m<=A, and all exponent assignments e_v=1,...,L. There are at most a constant (depending only on k,A) times L^k such choices: e.g. <=2^(k(k-1)) graphs and A^(k-1) slope assignments per r. Roots are variables x_1,...,x_t. Start a root as l_v(x_i)=x_i and compose edge maps z -> m z+1 in its tree, giving l_v(x_i)=a_v x_i+b_v with 1<=a_v<=H and 0<=b_v<=H for **every** template (a path has length <k; bound prefix products and their sums). All templates, including incorrect ones, contain the root form x_i in each component. The true primes supply one of the enumerated templates since (q-1)/p<=A.

Compute the profile of each proposed vertex using its proposed outdegree and exponent. Discard mismatches with the set of nonunit numeric blocks, or a matrix E below the required rank. The exact polynomial equations associated to the template include
```
F_j(x) := product over v of profile j of l_v(x_i)^e_v = N_j;
T product_all_v l_v(x_i) - N product_all_v (l_v(x_i)-1) = 0.            (1)
```
Here and below a node's x_i is its own component variable. The true roots meet every equation. Wrong templates need yield no roots, and no root of a wrong template is trusted without primality and complete product verification. Degrees of F_j are O_k(L), for true inputs no greater than L but the algorithm only needs kL. Coefficients have O_{k,A}(L+log L) bits by multiplying absolute-value majorants at 1. The Euler polynomial has degree <=k and O_{k,A}(L) bit height. The dense representations have polynomial size in fixed dimension.

## 4. Full rank: exact arithmetic for a polynomial-width window

When E has rank t choose t independent rows and let M be that square integer matrix. For these rows set C_j=product of a_v^e_v over the row, and h_j=log(N_j/C_j). Logs in the next estimate explain the algorithm, not its implementation. At a true solution with u_i=log x_i,
```
h = M u + eta,  where  0<=eta_j=sum e_v log(1+b_v/(a_v x_i))<=kHL/P .
```
Each row sum of exponents is at most kL. All entries of M are at most kL, its spectral norm is <=k^2 L, and |det M|>=1. By the product of singular values, ||M^(-1)||_2 <=(k^2 L)^(t-1). Also ||eta||_2<=Z/P. Thus each coordinate of M^(-1)h differs from log x_i by at most Z^t/P. On the large-prime branch this is <1/2, so |exp((M^(-1)h)_i)-x_i|<=2A Z^t, using x_i<=A P and |exp(z)-1|<=2|z| for |z|<=1/2.

To compute centers exactly set D=|det M| and H_ij=sign(det M) adj(M)_ij. Form the positive rational
```
S_i = product_j (N_j/C_j)^H_ij.
```
The desired integer center is floor(S_i^(1/D)), found by binary search with exact numerator/denominator comparisons. There is no floating-point logarithm. Determinant and adjugate entries have absolute values <=(k^2 L)^k by the determinant norm bound (for size one the adjugate is 1); the ratios have O_{k,A}(L) bits. The resulting powers, products and integer-root calculations thus have polynomial bit cost even on false guesses. If S_i<1 its floor-root is zero. A bitlength bound for its numerator provides an upper bound for the root search. Enumerate integers within 2 A Z^t+1 of each computed center. Evaluate that tree's node forms at them and keep only certified prime divisors of N. The true forest/rank-full template finds all true primes. If a prime is already known, one may instead recover its entire actual component by section 7. No need for all guesses to locate genuine roots.

## 5. One missing rank: uniform curvature on the relevant positive domain

Take t>=2 and rank(E)=t-1, and choose h=t-1 independent rows M. Select an invertible h-by-h minor by exact linear algebra. Consider candidate real roots x_i>=Q0, x_i<=A x_j for all i,j, and x_i<=N; put Q=min x_i. These are rational box and linear inequalities. Every true tuple lies in this region after the preliminary trial division. Estimates below apply to every template and every point in this region, not just an asymptotic sequence of true primes.

In local real variables u_i=log x_i put f_j(u)=log F_j(exp u) for the selected rows. Let J be its Jacobian. Each term log(a exp(u)+b) with s=a exp(u) has first derivative s/(s+b), and second derivative s b/(s+b)^2. Mixed partials of each f_j vanish. Since 0<=b<=H and s>=Q,
```
||J-M||_2 <= Z/Q,        ||Hess f_j||_2 <= k H L/Q .
```
The first bound follows from at most k rows and columns and per-entry error <=kHL/Q. The least nonzero singular value of M is >=(k^2 L)^(-(h-1))>=Z^(-(h-1)): the chosen minor has nonzero integer determinant and norm <=k^2 L, and adding other columns cannot decrease the smallest eigenvalue of M M^T. For Q>=Q0 the perturbation bound gives sigma_min(J)>=1/(2 Z^(h-1)). Hence the h selected equations define a locally smooth curve through every real solution in this region.

Use Euclidean arc length s0 in u-space on a local level curve, with unit tangent w and acceleration u''. We have w dot u''=0 and
```
J u'' = -(w^T (Hess f_j) w)_j.
```
The kernel of J is the tangent line, so u'' is the unique normal preimage of this right side. Its norm is at most 2 Z^h/Q by the preceding singular-value estimate and sqrt(h) kHL <= Z.

On the positive domain define
```
G(u) = sum_v log(1-1/l_v(exp u_i)).
```
The actual Euler equation in (1) is equivalent here to G(u)=log(T/N). This log is used only in the proof. For one term with s=a exp(u), b=b_v, direct differentiation gives
```
g'  = s/((s+b)(s+b-1)),
g'' = s [ b(b-1)-s^2 ] / ((s+b)^2 (s+b-1)^2).
```
All second derivatives are nonpositive for Q>=Q0>H+1, and |g'|<=2/Q. In each coordinate the root form x_i itself supplies exactly -x_i/(x_i-1)^2 <= -1/(A Q) to the diagonal Hessian. So ||grad G||_2<=2 k^2/Q and w^T(Hess G)w<=-1/(A Q) for every unit w. Along the local curve,
```
d^2 G / ds0^2 <= -1/(A Q) + 4 k^2 Z^h/Q^2 < -1/(2 A Q).
```
The last inequality uses the explicit Q0 and h<=k. This is a local calculation at the solution, even if it lies on the boundary of the linear inequalities; it need not stay inside the inequalities on both sides to evaluate the derivative. One must not assume there is a unique global level curve.

**Real isolation and total count.** The rank statement gives a single smooth real arc locally for the h selected profile equations. If the derivative of G along the arc is nonzero at a solution, the corresponding Euler level is locally isolated; if it is zero, the strict second derivative makes it a strict local maximum and again isolates the point. The log-coordinate change and the positive denominators lose no nearby positive real solution of the polynomial equations (1). This reasoning isolates the point in the *full real polynomial zero set*, not merely after imposing the candidate inequalities: the derivative tests are pointwise on the regular local arc. No assertion about the entire complex variety follows or is required. Every such isolated real point is a separate connected component. By Milnor, Theorem 2 (1964), the sum of the Betti numbers of a real affine variety in t variables defined by polynomials of degrees at most d is at most d(2d-1)^(t-1). Apply this to the h selected profile equations and the Euler polynomial, with d=O_k(L). In particular the number of isolated real solutions in our controlled region is O_k(L^k), regardless of other real or complex components elsewhere. No inference from strict concavity on a single global curve is needed.

## 6. Exact listing in the deficiency-one case

Use fixed-dimensional existential real feasibility (Renegar in the bit model) for those h+1 polynomial equations, the stated linear inequalities and a current integer-endpoint box within [2,N]^t. Split a coordinate interval [l,r] at m=floor((l+r)/2), testing [l,m] and [m+1,r] separately. No integer is lost in the gap; discard infeasible boxes, cycle coordinates and stop at singleton boxes. At each level disjoint feasible boxes contain distinct feasible real points, each an isolated real solution counted above. There are polynomially many tested boxes per level and O(t L) levels. There are at most k variables and a fixed bound on the number of constraints; degrees, coefficient bitlength and domain constants Q0 have polynomial encoding. This is a deterministic bit-polynomial algorithm. Recheck all profile equations, not just the selected ones, before accepting candidate data. When t=1 the full-rank case applies since there is at least one nonempty profile.

## 7. Verification and interpretation

No template needs external approval or a supplied certificate. Evaluate all forms at integer candidates; certify primality deterministically and divisibility in N. For a possible true vertex p there is also an exact way to enumerate its actual connected component: on the large-prime branch its sole parent, if present, is gcd(N,p-1)>1 (equal to a prime, since p-1<P^2). Every child is a prime divisor of N among the finitely many integers m p+1, 1<=m<=A. Visit distinct encountered vertices until finished. In particular a candidate subtree is never assumed to include all children merely because a template says so. Saving only proved prime divisors, divide into N to determine their exact valuations; accept only a complete factorization reproducing N and the numeric totient T. On the true promised template all factors are found. The polynomial bound is uniform over enumerated false templates: their full-rank intervals have polynomial width, and every deficiency-one feasibility search is restricted to the controlled positive domain. If on an unpromised input the verifications fail, the algorithm need not produce a factorization. This is not a theorem about factoring with N alone.

## 8. Rank examples and a limit of the method

Take five roots (1013,1103,1451,1481,1511) and, for each p, the two leaves 2p+1 and 6p+1. Exact trial arithmetic (see the first checker) verifies that all fifteen numbers are distinct primes, the ratio is <9 and there are no other edges. Give each root multiplicity 1, hence common profile 2. In the first assignment give the two leaves at tree i (i=0,...,4) the cyclic multiplicities 1+i and 1+((i+1) mod 5). Each leaf profile occurs in two trees; dividing each of the five leaf rows by its leaf multiplicity gives the incidence matrix I plus the five-cycle permutation, of determinant 2. This is a full-rank example without an exclusive class.

For a genuinely deficient example give the leaves of the five trees the respective unordered multiplicity pairs (1,1),(1,2),(2,3),(3,4),(4,4). The four normalized leaf rows are (2,1,0,0,0), (0,1,1,0,0), (0,0,1,1,0), (0,0,0,1,2). They are independent; the root row of ones is one half of their sum. Thus the rank is exactly four, and its nullspace is spanned by (1,-2,2,-2,1). No coordinate unit vector lies in the row span. The common root profile is not an exclusive class either. For another genuinely deficient example take only the first four roots and give their leaves cyclic pairs (1,2),(2,3),(3,4),(4,1). The four normalized leaf rows are the four-cycle incidence matrix, of rank three and null direction (1,-1,1,-1), and again their half-sum is the root row. A smaller mixed-shape fixture in the checker has roots 19,23,29,41 and children (191,229),(47,139),(59),(83), with leaf multiplicities (1,2),(1,3),2,3 and root multiplicity one. Its five occurring profile rows also have rank three, with no exclusive row. Direct primality and all ordered-pair edge tests validate both examples. These finite instances illustrate the criterion, not growth rates or an infinite family of simultaneous primes.

Already with three isolated primes of multiplicity 1, the rank can be t-2. For example take 101,103,107. The nonunit profile block is their product D and the other equation is the exact shifted product K. Fix a real x near 101. Then yz=D/x and y+z=1+D/x-K/(x-1) give a quadratic for y,z. Its discriminant is positive at the original distinct pair and remains positive in an interval. Thus the positive comparable real equations can have a continuum of solutions at deficiency two. This shows why the one-missing-direction argument does not simply extend; it is not a lower bound on other algorithms for the integer problem.
