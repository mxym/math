# The unrestricted APPT excess-purity asymptotic

Research working proof, 10 October 2026. No new manuscript or Release is prepared. This is an analytic proof, not a Lean certificate or externally peer-reviewed result. The finite checks are supporting calculations, not proofs of the compactness argument in the multiscale lower construction.

## 1. Main theorem

Let Pmax(m,n) be the maximum purity of an APPT density matrix on C^m tensor C^n, with 2<=m<=n, and put D=mn. Then

    sup_{integers n>=m}
    | D^2[Pmax(m,n)-1/D]/max(8,4+n/m) - 1 | ->0
    as m tends to infinity.                                    (F1)

The error in this equivalent is uniform in the larger dimension n. In particular, for every fixed finite gamma>=1 and every sequence n/m->gamma,

    D^2[Pmax(m,n)-1/D] -> max(8,4+gamma).                         (F2)

Thus the coefficient is 8 for 1<=gamma<=4 and 4+gamma for gamma>=4. The balanced law is

    Pmax(m,m)=1/m^2+8/m^4+o(m^-4).                               (F3)

This is an unrestricted maximum theorem at its leading excess-purity scale: no number of levels, flat-tail condition or eigenvalue-multiplicity constraint is imposed on the upper bound. It does not determine exact finite-dimensional maxima or classify their maximizers. It does not prove absolute separability of the lower constructions.

The stronger uniform form also applies when n/m diverges while m tends to infinity. It does NOT apply with the smaller dimension m fixed. Previous files record intermediate bounds; this file gives the current sharp all-aspect-ratio conclusion.

## 2. A necessary quantum test that permits arbitrary edge rearrangements

For 3<=m<=n let lambda_1>=...>=lambda_D be an APPT spectrum. Define

    R=m(m-1)/2, S=m(m+1)/2, j=D-S+1,
    b=lambda_j, delta_i=lambda_i-lambda_{D+1-i}, 1<=i<=R.

For every assignment of the R nonnegative differences to edges of the complete graph on m vertices, let A_delta be its symmetric zero-diagonal adjacency matrix. Then

    lambda_max(A_delta)<=2b, hence ||A_delta||_op<=2b.             (F4)

For completeness, take a unit Schmidt vector psi=sum_l x_l |ll>, x_l>=0. The partial transpose W of its rank-one projector has eigenvalues x_l^2 on diagonal vectors, +/-x_l x_t on symmetric/antisymmetric pairs, and zero on the other D-m^2 dimensions. Assign lambda_i to the negative vector of the edge carrying delta_i and lambda_{D+1-i} to its positive vector. Assign the next m smallest eigenvalues, all at most b, to the diagonal vectors. The slots are distinct since m^2<=D, and a global unitary realizes this eigenbasis. APPT gives

    0<=sum_l beta_l x_l^2-(1/2)x^T A_delta x
      <=b-(1/2)x^T A_delta x.

A symmetric nonnegative matrix has a nonnegative maximizing Rayleigh vector, by replacing coordinates with absolute values. Also |z^T A_delta z|<=|z|^T A_delta |z|, so the magnitude of every eigenvalue is bounded by its largest eigenvalue. This proves both parts of (F4). No spectral-characterization equivalence or product-ordering premise has been inserted.

## 3. A row-by-row graph inequality

Let eta_1>=...>=eta_R>=0 be any list, and place it in the upper triangle row by row: first all edges from vertex 1 to vertices 2,...,m, then from vertex 2 to vertices 3,...,m, and so on. Let A_eta be the resulting adjacency matrix and e=m^(-1/2)(1,...,1). Then

    sum_{i=m}^R eta_i^2 <= ||A_eta e||^2.                         (F5)

To prove this, let a_t be the least edge weight in upper-triangular row t, 1<=t<=m-2. Every incoming weight at vertex t came from an earlier row and is at least a_t. The m-t outgoing weights are also at least a_t. Thus the weighted degree of that vertex is at least (m-1)a_t. Every weight in row t+1 is at most a_t, and that row has m-t-1 entries. Since

    (m-1)^2/m >= m-2 >= m-t-1,

the squared degree of vertex t divided by m is at least the sum of squared weights in row t+1. Sum over t=1,...,m-2. The right side is bounded by the sum over all vertices, which is exactly ||A_eta e||^2. The left side contains all weights except the first row's m-1 entries. This proves (F5) with no graph enumeration.

## 4. The sharp unrestricted finite upper bound

Write

    w=delta_R, eta_i=delta_i-w, A=sum_i eta_i,
    V=sum_i lambda_i^2-1/D.

First put delta_1,...,delta_{m-1} on a star, filling the other edges with the remaining nonnegative differences. Its spectral radius and (F4) give

    sum_{i=1}^{m-1}eta_i^2
      <=sum_{i=1}^{m-1}delta_i^2<=4b^2.                          (F6)

For a DIFFERENT rearrangement, put all eta_i row by row as in Section 3 and add the baseline w to every edge. This is a permitted rearrangement of the delta_i, so

    ||(A_eta+w A_complete)e||^2<=4b^2.

The sum of the weighted degrees of A_eta is 2A. Expanding the square exactly,

    ||A_eta e||^2 + [4(m-1)/m]w A+(m-1)^2 w^2 <=4b^2.             (F7)

Equations (F5)-(F7) therefore imply

    sum_i eta_i^2
      <=8b^2-[4(m-1)/m]w A-(m-1)^2w^2.                         (F8)

Next choose z=(lambda_R+lambda_{D-R+1})/2. Each top/bottom pair has distances u,v>=w/2 from z and u+v=delta_i, so

    u^2+v^2<=delta_i^2-w delta_i+w^2/2.

The remaining D-2R eigenvalues are within w/2 of z. The mean minimizes the total squared distance to a scalar. Consequently

    V<=sum_i delta_i^2-w sum_i delta_i+D w^2/4
      =sum_i eta_i^2+w A+D w^2/4.                               (F9)

Insert (F8):

    V<=8b^2+[D/4-(m-1)^2]w^2+[1-4(m-1)/m]w A.

The last term is nonpositive for m>=2. Also the all-ones Rayleigh test in (F4) gives (m-1)w<=2b. Maximizing the remaining expression over 0<=w<=2b/(m-1) yields

    V <= C(m,n)b^2,
    C(m,n)=max{8,4+D/(m-1)^2}.                                  (F10)

This finite inequality applies to every actual APPT spectrum. It has no unproved restriction to a small number of spectral levels. The coefficient 8 arises from two different tests of the same spectrum: a star for the largest m-1 gaps and a degree-square estimate for all the rest.

The discarded negative term in the argument explains why treating the constant tail and all intermediate levels as independent can produce a loose upper bound. The baseline w contributes to every weighted degree and must be included before squaring.

## 5. Uniform normalization, including unbounded aspect ratios

Since j b<=1, (F10) gives V<=C/j^2. More usefully, for every spectrum

    b<=1/D+sqrt(V/j).

When b>1/D the first j eigenvalues each contribute at least (b-1/D)^2 to V; otherwise the inequality is immediate. Thus, whenever C<j,

    D^2 V <= C/(1-sqrt(C/j))^2.                                 (F11)

For m>=3, n>=m, one has j>=D/3. Also C<=8+D/(m-1)^2, so uniformly in n,

    C/j <=24/m^2+3/(m-1)^2 =: epsilon_m^2 ->0.

Let K(m,n)=max(8,4+n/m). Since

    C(m,n) <= [m/(m-1)]^2 K(m,n),

we obtain the explicit uniform upper estimate, for all sufficiently large m,

    D^2[Pmax(m,n)-1/D]/K(m,n)
      <= [m/(m-1)]^2/(1-epsilon_m)^2 ->1.                       (F12)

Uniformity allows choosing a maximizing state separately at every dimension. The maximum exists because the APPT set is a closed subset of the compact density-matrix set. No limit of a numerical maximizer is used.

## 6. Matching lower bounds, uniformly in n>=m

### 6.1 Separated intermediate plateaus contribute eight

MULTISCALE.md gives, for every fixed integer h>=1 and rational eta in (0,1), rational nested-projection states with all-unitary APPT positivity for every sufficiently large m. Their ranks and coefficients depend only on m, and the Schmidt-test proof is valid for every n>=m. Writing B=I+X, T=Tr X and S=Tr X^2, their scaled centered purity is exactly

    (S-T^2/D)/(1+T/D)^2.

Here X is supported on at most m^2 coordinates. Cauchy--Schwarz gives S>=T^2/m^2, and for D>=m^2 the displayed expression is at least

    (S-T^2/m^2)/(1+T/m^2)^2.

The latter tends to (1-eta)^2[4+4h^2/(h+1)^2]. First choose h and eta to make this arbitrarily close to eight, then take m large enough. The threshold in m is independent of n. Hence, for every epsilon>0, for all sufficiently large m and EVERY n>=m,

    D^2[Pmax(m,n)-1/D] >=8(1-epsilon).                           (F13)

The order of limits in the multiscale graph lemma is unchanged: the number of levels and slack are fixed before m grows. This is not an assumption that an arbitrary growing hierarchy is certified.

### 6.2 A broad plateau and a spike contribute 4+n/m

The finite rational construction in ASYMPTOTIC.md is valid for every m>=4,n>=m. Put

    h_m=ceil(sqrt(m)), k=ceil((m-1)n/2), y=k-1,
    c=2/(m+h_m),
    a=2-4(m-2)/[(m+h_m)(h_m+3)],
    B=I+cP+(a-c)|v><v|,

where P has rank k and v is a unit vector in its range. For q0=2-(m-3)c, the identities

    q0>0, (2-a)q0=2(m-2)c^2, a>=c>=0

give the exact positive-semidefinite two-block Schmidt-test certificate proved in PROOF.md. Therefore the normalized B is an actual APPT state at each finite dimension pair.

Let theta=y/D and gamma=n/m. Uniformly for n>=m,

    1/2-1/(2m)-1/m^2 <=theta<=1/2,
    a->2, mc->2.

Its exact centered numerator and normalization are

    N=a^2(1-1/D)+D c^2 theta(1-theta)-2a theta c,
    Q=(1+a/D+theta c)^2.

Define quantities depending on m only:

    A_m=a^2(1-1/m^2)-a c ->4,
    B_m=m^2 c^2[1/4-(1/(2m)+1/m^2)^2] ->1,
    Q_m=(1+a/m^2+c/2)^2 ->1.

For all sufficiently large m, these give

    D^2[Tr((B/Tr B)^2)-1/D]=N/Q >=(A_m+B_m gamma)/Q_m.

Consequently, for every epsilon>0, for all sufficiently large m and all n>=m,

    D^2[Pmax(m,n)-1/D] >=(1-epsilon)(4+n/m).                     (F14)

Combining (F13) and (F14) proves the uniform lower estimate (1-epsilon)K(m,n). Together with (F12), this proves (F1), and hence (F2)-(F3).

## 7. What is now resolved and what is not

The incorrect inner-polytope formula had fixed-aspect centered coefficient max(4,gamma). The actual unrestricted coefficient is max(8,4+gamma). In balanced systems the leading excess purity is therefore twice that predicted by the old formula. The one-spike/broad-plateau lower bound 4+gamma is sharp at this scale for gamma>=4; for gamma<4 it is overtaken by the multiscale hierarchy.

The result resolves the leading excess-purity maximum for every regime in which the smaller local dimension grows, including arbitrarily fast growth of the larger one, in the uniform sense (F1). It does not determine the exact finite maximum, the full asymptotic expansion, limiting extremizer classification, or the absolute-separability maximum. Fixed-m limits are not covered by (F1), and require a separate argument. The qutrit Lean theorem remains a separate completed result.

The new unrestricted upper bound is elementary finite-dimensional matrix analysis derived from physical all-unitary APPT tests. The lower bound eight uses the proved compactness/forest argument in MULTISCALE.md. Exact rational and integer checks test the finite identities and failed alternatives; no finite test, native calculation or pre-existing Lean result is presented as certification of the unbounded theorem.
