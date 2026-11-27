# Exact nondeterministic degree profile

## 1. Definitions and weighted evaluation duality

Let F be an infinite field and A=∏_(i=1)^n A_i a finite Cartesian grid of distinct field elements, with q_i=|A_i|≥2. Put N=|A| and D=Σ_i(q_i−1). For nonempty S⊆A, define nd(S) as the least total degree of a polynomial whose nonzero evaluations on A are exactly S. This agrees with the real nondeterministic degree of the membership function of S on the Boolean cube. All polynomials may be taken reduced (degree in variable i <q_i) by reduction modulo the monic vanishing polynomial of each coordinate. This gives a unique representative by tensor Lagrange interpolation, and never raises total degree. Thus 0≤nd(S)≤D.

Let E_t⊆F^A be the polynomial evaluation space of total degrees ≤t, with E_(-1)={0}. At x∈A put
```
   w(x) = ∏_i [∏_(y∈A_i\{x_i})(x_i−y)]^(−1).
```
With the usual pairing Σ_x u(x)v(x), the exact dual is
```
             E_t^⊥ = diag(w) E_(D−t−1)       (0≤t≤D).           (1)
```
In one coordinate, comparison of the top coefficient in Lagrange interpolation for a power below degree q_i−1 gives its weighted sum zero. Thus for monomials of total degree <D the tensor weighted sum vanishes: some coordinate exponent is below q_i−1, regardless of the other coordinates. Products of degrees t and D−t−1 have total degree <D, giving the inclusion in (1). Reduced monomials are independent as functions on A. Complementing each exponent e_i to q_i−1−e_i pairs monomials of total degree ≤t with monomials of degree ≥D−t. It follows that dim E_t+dim E_(D−t−1)=N. The weights are nonzero, so the dimensions prove equality.

## 2. Exact single-hit identity

For every nonempty S⊆A,
```
   nd(S) = D − min{deg g : |{x∈S:g(x)≠0}|=1}.                (2)
```
The minimum exists, for example by interpolation of a point indicator.

Indeed E_t∩F^S is the subspace of evaluations of degree≤t supported inside S (here F^S is embedded by zero extension). It has a vector nonzero on all of S iff for each a∈S some vector in the subspace has nonzero a-coordinate. The implication from separate vectors uses the infinite field: finitely many proper linear hyperplanes cannot cover a finite-dimensional space. For completeness, choose a basis of that space and view the coordinate evaluations as linear polynomials in the basis coefficients. Their product is a nonzero polynomial and cannot vanish at every field assignment.

On the other hand, the a-coordinate is identically zero on E_t∩F^S iff the a-th standard basis vector is in
```
  (E_t∩F^S)^⊥ = E_t^⊥ + (F^S)^⊥,
```
where the latter equality is the elementary dimension identity for annihilators. This is equivalent to a vector of E_t^⊥ taking value 1 at a and 0 on S\{a}. By (1) and nonzero weights, it is equivalent to a polynomial of degree≤D−t−1 nonzero at just that one point of S. If the minimum such degree is e, support realization at degree t is possible precisely for t≥D−e, proving (2). On the real cube this is a direct formulation of the row-space unit-vector obstruction in Rajagopalan–Saurabh, Lemma 4 and Lemma 24, with multiplication by full parity turning its high Walsh rows into low rows; the linear-algebra principle is not new.

## 3. The exact profile for arbitrary grids

For 0≤e≤D let
```
   L_e = min{∏_i(q_i−a_i) : 0≤a_i≤q_i−1 are integers, Σ_i a_i≤e}.
```
This is the known generalized Alon–Füredi minimum support size in degree at most e. A self-contained proof in this setting is short: take the leading power in the last variable, and iterate on its nonzero leading coefficient in the other variables. This selects a monomial with exponent vector a, total degree≤e. At each fixed point where the leading coefficient is nonzero, the univariate polynomial has at most a_n roots among q_n entries. Induction gives support size≥∏(q_i−a_i). Conversely a product of a_i distinct coordinate factors in each coordinate has precisely that support size and the indicated degree. This proves the formula. The sequence L_e is strictly decreasing for e<D: a minimizing vector may be chosen with Σa_i=e, because any unused degree can increase some unsaturated a_i and strictly decrease the product; the same increase then compares L_e and L_(e+1).

For 1≤s≤N put e_s=min{e:L_e≤N−s+1}. Then the exact maximum is
```
         max_(|S|=s) nd(S) = D−e_s.                            (3)
```
If g hits S just once, at least |supp g|−1 points outside S are required, so L_(deg g)≤N−s+1. Thus (2) gives the upper bound. For attainment choose a degree≤e_s polynomial with minimum support L_(e_s), pick one nonzero evaluation a, and choose S to consist of a and any s−1 points outside that polynomial's support. This is possible by the inequality in the definition of e_s, and (2) gives the matching lower bound.

The critical cardinality for a target degree k=0,…,D is s_k=N−L_(D−k)+1. At this size nd(S)=k iff
```
   A\S = supp(g)\{a}  for a minimum-support degree-(D−k) polynomial g
                       and some a∈supp(g).                    (4)
```
Indeed strict decrease of L shows the maximum here is k. In case of attaining k, the polynomial in (2) has degree D−k, and its support has at most N−s_k+1=L_(D−k) points, hence has exactly that size. This forces the complement description. Conversely every such complement yields equality. No minimum-support classification on general unequal grids is assumed.

## 4. Binary cube, exact endpoint shapes and counts

On the real Boolean cube N=2^n and D=n. Since every q_i=2, L_e=2^(n−e). Thus (3) becomes
```
        max_(|S|=s) nd(S) = floor(log_2(2^n−s+1)).             (5)
```
At s=1 this recovers Proposition 22's extremal degree n; for any s>1 it already gives a strictly smaller upper bound. If both S and S^c are nonempty, the rational degree of the membership function is max(nd(S),nd(S^c)): a representation f=p/q with no zero denominator provides p and q−p as exact-support representatives for S and S^c, and conversely from exact-support representatives P,Q use the ratio P/(P+Q). Hence the maximal rational degree at fixed size s is
```
  max{floor(log_2(2^n−s+1)), floor(log_2(s+1))}.
```
This uses the maximum of the two separate pointwise bounds and attainment of either of the larger bounds by (5). The two constant Boolean functions have rational degree zero.

For k≥2 and s_k=2^n−2^k+1 the shapes in (4) are entirely explicit. Theorem 2(2) of Valyuzhenich with the lower Walsh-level endpoint 0 classifies real polynomials of degree≤n−k attaining the support bound 2^k. Written in bit coordinates, their supports are precisely the following signed block cubes C: some coordinates are fixed to prescribed bits, and the rest are partitioned into k nonempty blocks; within a block each coordinate is the common free bit or its complement. The k block bits vary independently. This is the support of the tensor on k signed two-point blocks (of any lengths, including one) and single-point fixed-coordinate factors in his theorem. For example, the two extreme block values {all-zero, all-one} can be assigned opposite signs when block length is even, and equal signs when odd, so the highest Walsh level in that block is one less than its length. Products over blocks with fixed-bit indicators attain degree n−k. We use this previously known classification, not a new claim about minimum-support polynomials. By (4) the extremizing S are exactly the complements of C with one of its points removed, i.e. S=A\(C\{a}).

Each signed block cube is an affine k-subspace over F_2 on its grid indices. For k≥2 its punctured set C\{a} affinely spans it: its size 2^k−1 exceeds the size 2^(k−1) of any proper affine subspace of C. Thus the complement determines C and a uniquely. The coordinates fixed on C and the partition of nonconstant coordinates are intrinsic: two nonconstant coordinates belong to the same block exactly when their bitwise xor is constant throughout C. Partition choices, with a possibly empty fixed-coordinate set, are counted by the Stirling number of the second kind S(n+1,k+1), by adjoining a sentinel to the fixed block. For each partition there are 2^(n−k) orientation and fixed-bit choices (complementing every bit within a free block redundantly changes its free variable's convention). For each C there are 2^k possible a. So the exact number of extremizers at this size is
```
               2^n S(n+1,k+1)   for 2≤k≤n.                     (6)
```
For k=1 the complements are singletons; every singleton is possible, giving 2^n distinct supports (the deleted two-point block need not be unique). For k=0 the whole cube is the sole support. At k=n formula (6) yields 2^n singleton supports, consistent with Proposition 22.

The infinite-field condition in (2) cannot simply be discarded. Over the two-element coefficient field every function nonzero precisely on S must be its indicator. On the two-variable cube a support of size 3 has a degree-2 indicator (odd parity of truth values forces the top coefficient), although its real nondeterministic degree is 1 by (5).
