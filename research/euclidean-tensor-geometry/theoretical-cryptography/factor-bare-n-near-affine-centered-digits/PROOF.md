# Connected near-affine factors and centered coefficient windows

## 1. Promise

Fix integers r>=2 and C>=0. Let N be the product of exactly r distinct primes and let L=bitlength(N), M=L^C. On the unknown prime support of N, join p<q if at least one integer 1<=m<=M satisfies

```
|q-m p|^r <= p M^r.                                               (1)
```

Assume this undirected graph is connected. Its slopes and offsets are not given. An allowed edge need not have offset 1, and a valid graph can contain cycles. The constants r,C are parameters fixed before the input.

**Theorem.** Given N alone under this promise, its entire prime factorization can be found deterministically in time polynomial in L. No oracle or factorization of an auxiliary integer is assumed. All steps below use exact integer or rational arithmetic and ordinary deterministic univariate root operations.

## 2. A polynomial list of integer normalizations

Temporarily label the r unknown primes and enumerate every rooted labelled spanning-tree shape, orientation of its edges from smaller to larger prime, and an integer slope in 1,...,M per edge. Each edge orientation is independent of the direction away from the root. There are O_r(M^(r-1)) guesses. For the true guess place the minimum prime x at the root, choose any spanning tree of its true graph, and keep valid selected slopes. Cycles or additional edges do not matter. For a guess, assign positive rational numbers a_i to the vertices starting with a_root=1 and imposing a_q=m a_p on an edge directed p to q. Tree paths make this well-defined, using a multiplication or division by m at each step. Numerators and denominators in lowest terms are at most M^(r-1), so in particular

```
M^(-(r-1)) <= a_i <= M^(r-1).
```

Let B be the product of these numerators, B_0=M^(r(r-1)), and b_i=B/a_i. The b_i are positive integers, B<=B_0, and the known number

```
K = N product_i b_i
```

is an integer even for an incorrect guess. At true primes p_i, the scaled values y_i=b_i p_i are positive integers of product K. They are not asserted prime or distinct. Set s=floor(K^(1/r)), by exact integer comparisons.

For a true edge p<q, (1) implies q/p<=m+M p^(1/r-1)<=2M. Thus every true prime, along at most r-1 edges from x, is at most H x where H=(2M)^(r-1). The scaled discrepancy on one edge is bounded by

```
|y_q-y_p| = (B/a_q) |q-m p|
          <= B_0 M^r H^(1/r) x^(1/r)
          <= B_0 M^r H x^(1/r).
```

Absolute differences give the same bound when traversing an edge backwards. Hence, with Lambda=(r-1) B_0 M^r H, every true y_i is within Lambda x^(1/r) of the root value Bx. The positive geometric mean K^(1/r) lies between the extreme y_i. Furthermore each y_i>=Bx/M^(r-1) and is at least 2, so s>=K^(1/r)/2 and x<=2 M^(r-1)s/B. Consequently, with the explicit integer J=4 Lambda M^(r-1)+1,

```
u_i := y_i-s,      |u_i| <= J s^(1/r).                              (2)
```

Indeed the distance to the geometric mean is bounded by the full range, at most 2 Lambda x^(1/r), and taking the floor adds less than 1; use B>=1 and s>=1. J is a polynomial in L with constants depending only on r,C and can be used for every guess. This argument neither estimates nor enumerates the true minimum prime x. It uses a center computed from the known normalized product.

## 3. Digit windows at the known center

Write E_j for the j-th elementary symmetric function of the u_i and put E_0=1. Then

```
K = product_i(s+u_i) = sum_(j=0)^r E_j s^(r-j),
|E_j| <= binomial(r,j) J^j s^(j/r).                                (3)
```

The E_j may be negative. Their recovery is not an assertion that the base-s digits are equal to the E_j. Suppose E_1,...,E_(j-1) have been guessed. Form the exact rational number

```
R_j = (K - s^r - sum_(h=1)^(j-1) E_h s^(r-h)) / s^(r-j).
```

For a correct prefix, (3) gives

```
|R_j-E_j| <= sum_(h=j+1)^r binomial(r,h) J^h s^(h/r-(h-j))
          <= (1+J)^r.
```

For every term, h/r<=1 and h-j>=1, which is why an initially large uncertainty in the individual offsets does not imply a large coefficient window. Try all integers in this closed rational window. At j=r, the residual gives E_r exactly. Because r is fixed, the total count of prefixes and complete lists is polynomial in L. The same count bound applies to prefixes of false guesses; we never assume their offsets satisfy (2). Every branch has polynomial bit size: K is O_{r,C}(L+log L) bits, s and its fixed powers are of comparable bit length, and a bounded number of residual operations and polynomial-width shifts preserves this bound up to fixed constants.

One can optionally round E_j without branching for j<=r-2 if s>(2(1+J)^r)^r: every exponent in the tail is then at most -1/r, making the tail strictly smaller than 1/2. This optional simplification is not needed for the proof and is not used to assume anything about the size of the smallest prime. The final nontrivial window j=r-1 cannot in general be replaced by nearest-integer rounding.

## 4. Verification and running time

For each complete list form the monic integer polynomial

```
U(Z) = Z^r - E_1 Z^(r-1) + E_2 Z^(r-2) - ... + (-1)^r E_r.
```

List its integer roots and their multiplicities by exact univariate root isolation and synthetic division. For example, deterministic polynomial-time real feasibility for one variable on integer-endpoint boxes suffices: restrict to [2-s,K-s], bisect integer intervals dropping only the open gap between adjacent integers, and retain a box only if it contains a real root. The nonzero monic polynomial has at most r real zero locations, so the retained work is polynomial. The interval contains all true shifts because every true y_i lies in [2,K]. An integer root's multiplicity is checked by repeated exact division. Discard candidates without a full multiset of r roots in this interval.

Add s to the resulting shifts. Try all assignments of this multiset to the scale factors b_i, at most r! even with repetitions. The prospective primes are y_i/b_i. Verify integrality, primality, distinctness, and exact product N. The original promise can also be checked on these values by testing the r choose 2 unordered pairs and the M possible slopes using (1), and then checking graph connectivity. A declared correct prime factorization is unique, even if more than one template or branch gives it. No uniqueness of representations by scaled integer factors is used.

The true tree guess yields a normalization satisfying (2); every branch containing its true prefix, and hence the entire true polynomial, is included. The certificate at the end cannot accept a wrong prime factorization. The number of templates and residual branches, their exact arithmetic, fixed-degree root operations, and deterministic primality tests are polynomial in L. The polynomial exponent may depend on r,C. The proof does not enumerate the allowable offsets, which can grow as a positive power of a prime. It also does not imply any statement about numbers without this promise or a density of promised examples.
