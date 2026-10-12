# Lieb/Marcus investigation: rigorous stage boundary

Date: 8 October 2026.

## Main problem status

This investigation has not proved or disproved the full arbitrary-subgroup
Lieb permanent-dominance conjecture, or Marcus's equal-block inequality

    per A >= per([per A_ij]),

where A is Hermitian PSD and the m by m blocks have common size k. The finite
literature check in SOURCE_AUDIT.md found current partial results, not a full
resolution. A cofactor Rayleigh vector is not automatically a subgroup character
or a legal subgroup-fixed projection vector.

The research route is being closed at this stage because its validated spectral
amplification does not supply the missing character/subgroup realization. The
claim is that these attempted mechanisms are blocked or incomplete, not that
all conceivable approaches to Lieb/Marcus have been ruled out.

## Complete results supplied in this package

1. Let R_N maximize lambda_max(C(A))/per A over complex Hermitian PSD matrices
   of order N, and let R_N^R maximize lambda_max(Re C(A))/per A. Then
   R_N/log N -> 1 and R_N^R/log N -> 1/2. The same leading limits hold when the
   lower examples are restricted to rank-two correlation matrices, at every
   sufficiently large N. The unrestricted suprema retain their leading limits
   for positive-definite correlation matrices. A real test vector is not the
   same as a real matrix; no real-matrix extremal theorem is asserted.
2. An explicit algebraic dyadic family gives finite lower bounds
   33K(2^K-1)/(343*2^K) and 33(K+1)(2^K-1)/(686*2^K), with N=2^(K+1).
   Separate exact integer algorithms verify full complex/real Rayleigh
   quotients at orders 512 and 2048, plus a direct order-eight Gram check.
3. For the ramp w_i=2i-N-1, the exact finite universal bound is
   12(sum_{j=1}^{N-1} sqrt(j(N-j)))^2/[N^2(N^2-1)]. Its asymptotic constant
   3*pi^2/16 is attained as a limsup already by rank-two matrices.
   The corresponding normalized rank-two q-permanent endpoint ratio has
   optimal limsup pi^2/8. This is not a claim of the same endpoint bound for
   arbitrary rank, nor a new proof that the original Bapat conjecture is false.

The main proof is complete in sharp_cofactor_extrema.tex and its PDF, with a
plain-text rendering in PROOF.md. It contains the classical indicator bound's
full contraction proof, rather than depending on an inaccessible source.

## A proved rank-two barrier for the Marcus route

Normalize A to a correlation matrix of rank at most two and order N=mk. If U
is uniform on the unit sphere in C^2, the Gaussian/Fock identity and radial
integration give

    per A = (N+1)! E_U product_i |<v_i,U>|^2.

For every unit v, |<v,U>|^2 is uniform on [0,1], so E log |<v,U>|^2=-1. Jensen
therefore gives per A >= (N+1)! exp(-N). On the other side the block-permanent
matrix G is PSD, G_ii<=k!, and its Gram/Cauchy--Schwarz bound gives

    per G <= m! product_i G_ii <= m!(k!)^m.

Thus no rank-two counterexample exists whenever

    Q(m,k):=(mk+1)!/[m!(k!)^m e^(mk)] >= 1.              (A)

For m>=3,k>=2, Q is strictly increasing in both arguments. To check increase
in m, the k=2 ratio is (2m+3)/e^2>1; for k=3 it is
(3m+2)(3m+4)/(2e^3)>1. For k>=4 the ratio is at least
(m+1)^(k-1)/e^k >=4^(k-1)/e^k>1. The last bound follows by comparing the j-th
factor mk+1+j with (m+1)j, for j=1,...,k.
For increase in k, at m=3 the ratio is
[27-3/(k+1)^2]/e^3>1. At m>=4 each normalized factor is at least
(2m+2)/3>=10/3>e.

The starting values Q(7,2), Q(4,3), Q(3,7) exceed one by the exact rational
certification e<87/32 and the integer checks in verify_stage_bounds.py.
Consequently the only m>=3,k>=2 pairs not excluded by (A) are

    (3,2),(4,2),(5,2),(6,2),(3,3),(3,4),(3,5),(3,6).

Their largest order is 18. The two-block case m=2 is the classical proved
Lieb/Marcus case, and m=1 or k=1 is trivial. Therefore every rank-two Marcus
instance of order at least 19 is already excluded from the counterexample
search by these bounds. This does not prove the unexcluded low-order instances,
and does not address rank growing with N.

## A proved local James-wreath barrier

Let J be James's rank-two 4 by 4 PSD equality matrix with diagonal sqrt(3)
and off-diagonal rows (i,i,-i), (-i,i,i), (-i,-i,-i), (i,-i,i).
Its permanent is 24 and the deleted-minor matrix is

    D_J=4sqrt(3) I+2 conjugate(J),

which is positive definite. Choose the non-real degree-one character chi of
A4 satisfying d_chi(J)=24. For a block matrix A(t) with fixed diagonal blocks
J and fixed off-diagonal blocks t E_ij, E_ji=E_ij*, the coefficient of t^2 in
per A(t) is

    24^(m-2) sum_{i<j} vec(E_ij)^*(D_J^T tensor D_J)vec(E_ij).

Indeed one cross move in each direction gives, for a pair of blocks,
sum E_ab conjugate(E_cd) per J(a|c) per J(d|b), exactly this quadratic form.
It is strictly positive if any E_ij is nonzero. But for
G_ij(t)=d_chi(A_ij(t)), the off-diagonal entries are of order t^4, so
per G(t)=24^m+O(t^8). Hence this fixed-diagonal coupling has a positive Marcus-
type character gap near t=0 whenever it is PSD. This excludes only that local
construction. It does not exclude remote couplings or arbitrary changing-
diagonal perturbations. The exact James identities were checked algebraically;
the displayed positive-definite formula is also their direct proof.

## Unproved bridges and exploratory evidence

- The fixed-k repeated-row higher-compound limit produces eigenvalues
  1,s,...,s^k. Here k and the base configuration are fixed before repetition
  tends to infinity. No estimate uniform in k was established in that route.
  This mechanism remains internal supplementary work; it is not used in the
  two main theorems or advertised as a solution of a new conjecture.
- Ordinary irreducible immanants on rank-two Gram matrices only have nonzero
  two-row sectors, whose permanent dominance is a known classical theorem.
  A bad noncentral direction in such a sector cannot refute that theorem.
- Direct conversion to an arbitrary-subgroup projector, or to a genuinely
  higher-rank coupled Marcus family, remains missing. Occurrence of the same
  irreducible representation is insufficient to provide the needed direction
  and normalization.
- Structured floating-point optimizations, including James A4 wreath products
  on two and three blocks, produced no certified counterexample. Their return
  to equality strata is not a theorem, global minimum certificate, or exhaustive
  search. No numerical non-discovery supports a universal claim in this package.

## Higher-compound source consistency check

For the explicitly defined matrix
C_k(B)[I,J]=per B[I,J] per B[I^c,J^c], an internal exact computation finds
B=A direct_sum A of order 400 and rank four, and a binary vector supported on
3502 cross-block two-subsets, with normalized C_2 Rayleigh quotient strictly
between 139/100 and 140/100. This checks only the expressly defined unrestricted
binary-vector statement. The potentially related Pate 2008 full theorem and its
qualifications were not obtained; no claim about a mistake in that theorem is
made. The internal certificate is not a premise of the present results and is
not part of the minimal public package.

## Prior work and novelty boundary

Drury's finite cofactor counterexample, classical two-block contraction
positivity, Pate's first-compound indicator refinement, the Gaussian/Fock
permanent identity, and the noncentral/character distinction are prior inputs.
Earlier work in this investigation had already established unbounded cofactor
ratios and the rank-two endpoint construction. The present stage supplies the
sharp dimension-leading constants, elementary explicit finite family, and
matching endpoint upper constant. The literature search is finite, so this is
not an assertion of exhaustive priority clearance.
