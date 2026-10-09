# Proof supplement and semantic coverage

This additive supplement leaves previously published paper versions and their
checksums untouched. It makes the normalization-free argument used by the
Lean proof explicit and records the precise boundary of the new certificate.

## Objects

For rows a,b in C^4 let U=sum |a_j|^2, V=sum |b_j|^2,
E=|sum a_j conjugate(b_j)|^2, and T=sum |a_j|^2 |b_j|^2.
Index the six increasing pairs as 01,02,03,12,13,23. The vector p(a,b)
has entries a_j b_k+a_k b_j; the vector w(a,b) has entries with subtraction.
Write S=sum |p|^2 and W=sum |w|^2. The Lean definitions use these actual
complex entries; their identities are proved by ring identities over real
and imaginary parts, not assumed from a checker result.

Expansion gives S=UV+E-2T and W=UV-E. Cauchy gives 0<=E<=UV and E<=4T.
For every real c,

    S+cW = (1+c)UV + (1/2-c)E - 2(T-E/4).

If c<=1/2, use E<=UV; if c>=1/2, use E>=0. In both cases
S+cW<=max(3/2,1+c)UV. Nothing here divides by a row norm, so a zero row
requires no excluded case or unproved limiting argument.

## Actual matrix Laplace expansion

For a 4-by-4 matrix write its rows as a,b,d,e. Pair complementation reverses
the six-element indexing above. The determinant shuffle signs are
(1,-1,1,1,-1,1). The Lean proof establishes both Laplace expansions from
Mathlib's permutation-sum definitions, using an explicitly bijective list
of all 24 permutations. Kernel evaluation verifies that finite bijection;
ring normalization verifies the identities for arbitrary complex entries.
This finite step is an exact polynomial identity, not a finite verification
of the matrix inequality.

Complex Cauchy gives |per A|^2<=S(a,b)S(d,e) and
|det A|^2<=W(a,b)W(d,e). The weighted Cauchy step for c>=0 follows from

    (s+cu)(t+cv) - (sqrt(s)sqrt(t)+c sqrt(u)sqrt(v))^2
      = c(sqrt(s)sqrt(v)-sqrt(t)sqrt(u))^2 >= 0.

Apply the two-row bound to both pairs, then compare nonnegative squares.
The product of row norms is exactly product_i sqrt(sum_j |A_ij|^2).
This proves the asserted bound for every matrix without normalization.

## Sharp constants and real pencil supremum

The all-ones matrix has permanent 24, determinant 0, and product of row
norms 16, giving the normalized value 3/2. The identity has permanent 1,
determinant 1, and product of row norms 1, giving 1+c. Therefore the
universal tradeoff constant is exactly max(3/2,1+c), and it is attained.

For the pencil, the triangle inequality bounds |per A+t det A| by
|per A|+|t||det A|. The identity attains 1+|t| when t>=0; the permutation
matrix swapping the first two coordinates has permanent 1 and determinant
-1 and attains 1+|t| when t<=0. The flat matrix attains the other branch.
Thus the set of actual normalized values has the stated greatest element,
which yields the exact supremum. The supremum theorem is not merely a
renamed predicate on proposed upper bounds.

## What the certificate does not assert

The witnesses above prove attainment and optimality but do not classify
all equality matrices. The critical c=1/2 support/phase argument, the
all-n rectangular result, the pairwise deficit, general convex objectives,
and tensorization remain outside the v1 proof closure. No external
geometric or analytic theorem is silently postulated to fill these gaps.
