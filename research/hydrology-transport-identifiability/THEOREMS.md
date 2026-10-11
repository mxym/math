# Architecture–tracer identifiability in conservative compartment networks

**Research checkpoint, 11 October 2026.** Complete written proofs below apply
only to the specified model class and ideal experimental information.
They are not Lean formalizations, an external peer review, a field validation,
or an established claim of historical novelty. Classical realization and
similarity theory are prior work; see NOVELTY.md.

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. No external funding. AI-assisted research.
Original additions: all rights reserved, subject to existing applicable
repository and third-party notices. No third-party source code is copied.

## 1. Physical class and observations

There are n perfectly mixed water stores, with inventory x in R^n_+.
Time is measured in days; inventories can be catchment-equivalent mm. Let
b >= 0, 1^T b = 1, be the input allocation; q_i > 0 the outlet-loss
coefficients; and e_i >= 0 the environmental water-loss coefficients.
A scalar environmental driver u(t) lies in [0,1]. It is a normalized
experimental demand, not automatically a measured potential-ET series.

An internal transfer matrix K has nonnegative off-diagonal entries and
zero column sums. Entry K_ij, i != j, is the rate from store j to store i.
Consider the affine driver-dependent class

    K(u) = K0 + u K1,
    1^T K0 = 1^T K1 = 0,
    K0 and K0+K1 have nonnegative off-diagonal entries.

K1 need not have nonnegative off-diagonals: a transfer may decrease with u.
Affineness makes the two endpoint inequalities sufficient for every u in [0,1].
Write Dq=diag(q), De=diag(e), A=K0-Dq, and Bw=K1-De. Water obeys

    x' = (A+u Bw)x + b p,                 Q=q^T x,
    ET=u e^T x,                          S=1^T x.           (1)

Then S'=p-Q-ET exactly. For bounded piecewise-constant u and nonnegative
locally integrable p, the model has a unique nonnegative trajectory from a
nonnegative initial state. On each constant-u interval its exponential is
nonnegative: add a sufficiently large scalar multiple of I, use the
nonnegative power series, and multiply by the positive scalar exponential.
Variation of constants and concatenation prove the assertion. The extension
to bounded measurable u follows by the usual linear-ODE approximation; the
identification results below already use only piecewise-constant experiments.

A tracer inventory z has the same internal transfer rates, input allocation,
and outlet sampling, but environmental losses g_i >= 0:

    z' = (A+u Bz)z + b v,   Bz=K1-Dg,    L=q^T z.          (2)

Here v is the known incoming tracer mass rate and L is the outgoing tracer
mass rate. If concentration is observed, L=Q times that concentration.
Perfect mixing implies an internal water flux K_ij x_j transports tracer
mass K_ij z_j. No sorption, additional baseline reaction, unknown deposition,
or tracer-dependent internal transfer is present in (2).

Important cases are g=e (ideal nonfractionating water-following labels),
g=0 (an ideal solute entirely excluded from environmental water loss), and
g=rho e. Nonvolatile does not by itself establish g=0 in a real catchment:
plant uptake or chemical reactions can violate that assumption.

Experiments start with zero incremental inventory. Impulse kernels denote
limits of narrow bounded-input pulses. For tracers a positive background water
inventory can be maintained; because the assumed rate law depends on u but
not on water inventory, this does not change the incremental tracer operator.
The full-information statements concern arbitrary such experiments, not one
natural rainfall record. Their input requirements are substantive assumptions.

The baseline realization (A,b,q^T) is **minimal** when

    R=[b,Ab,...,A^(n-1)b],
    O=[q^T; q^T A; ...; q^T A^(n-1)]

are both invertible. This assumption is explicitly checked for the example.
It can fail through equal response modes or inaccessible stores.

A is invertible: -A^T is strictly row diagonally dominant, since each row's
diagonal exceeds the sum of absolute off-diagonals by q_i>0. The elementary
maximum-coordinate proof of diagonal dominance gives invertibility. Therefore

    ell^T = -q^T A^(-1) = 1^T.                            (3)

This conservation identity will remove the otherwise arbitrary eigenvector
scalings in reconstruction.

## 2. What response data suffice?

Define baseline moments r_j=q^T A^j b for j=0,...,2n-1 and mixed moments

    W_pq=q^T A^p Bw A^q b,
    Z_pq=q^T A^p Bz A^q b,       0 <= p,q < n.             (4)

These are derivatives of response kernels, not ordinary statistical moments
of a rainfall distribution. They are an ideal structural-identification data
object. High-order numerical differentiation of noisy field data is not
recommended by this theorem.

To see that complete controlled input-output data determine (4), inject a
unit incremental pulse, evolve at u=0 for s, at u=a for delta, and again at
u=0 for t. The outlet kernel is

    q^T exp(A t) exp((A+a B) delta) exp(A s) b.

The derivative first in a and delta at zero is
q^T exp(A t) B exp(A s)b. Its t- and s-derivatives give (4).
Right derivatives from nonnegative a,delta suffice by analyticity. Baseline
impulse derivatives give r_j. This also explains exactly why a single
uncontrolled observational record need not supply the required information.

## 3. Constructive identification from a transport contrast

**Theorem 1 (unknown-network reconstruction).** Fix n and the class (1)-(2).
Assume its baseline realization is minimal and the diagonal entries of

    Dc = De-Dg

are pairwise distinct. The finite data (4) and r_0,...,r_(2n-1) determine
K0,K1,b,q,e,g uniquely up to a common permutation of stores. None of these
coefficients, including the loss rates, needs to be known in advance.
In particular, with g=0, one retained-solute channel together with water
outlet response identifies the entire affine network under these assumptions.

**Proof and reconstruction.** Form the n-by-n matrices

    H0_pq=r_(p+q),          H1_pq=r_(p+q+1).

The factorization H0=OR proves invertibility. Set

    Ahat=H0^(-1) H1 = R^(-1) A R,
    Bwhat=H0^(-1) W = R^(-1) Bw R,
    Bzhat=H0^(-1) Z = R^(-1) Bz R,
    Dhat=Bzhat-Bwhat = R^(-1) Dc R,
    bhat=(1,0,...,0)^T,
    chat=(r_0,...,r_(n-1))=q^T R.

Compute lhat=-chat Ahat^(-1)=1^T R. The distinct real eigenvalues of Dhat
are exactly the entries of e-g, with unknown order. Choose any eigenvector
v_i for each eigenvalue and normalize it so that lhat v_i=1.
This normalization is possible and unique: every such eigenvector has the
form alpha R^(-1)e_j for exactly one coordinate j, so lhat v_i=alpha != 0.
Let V be the matrix of normalized eigenvectors. Then

    V=R^(-1) P

for a permutation matrix P. Hence

    Arec=V^(-1) Ahat V=P^(-1) A P,
    brec=V^(-1) bhat=P^(-1)b,
    qrec^T=chat V=q^T P,
    Bwrec=V^(-1) Bwhat V,
    Bzrec=V^(-1) Bzhat V.

Conservation gives the physical loss rows without any prior rates:

    erec^T=-1^T Bwrec,       grec^T=-1^T Bzrec.

Finally

    K0rec=Arec+diag(qrec),
    K1rec=Bwrec+diag(erec).

These are the original coefficients in the order selected by P.
The construction depends only on the specified response data, proving both
recovery and uniqueness. Conversely a common permutation preserves all
input-output responses. This completes the classification. □

The theorem asserts identification *within this class*, not model correctness.
Candidate data can be falsified if the inferred baseline is singular, contrast
spectrum is nonreal, conservation normalization fails, or recovered transfers
are negative. Repeated contrast eigenvalues instead signal unresolved blocks,
not necessarily a false model.

**Corollary 1 (contrast rather than channel count).** Repeating material channels
with g=e, with arbitrary different source concentration histories, does not
supply the missing diagonal contrast. In contrast, one channel with g=0 and
pairwise distinct e_i is sufficient in the ideal minimal setting.
Uniform known tracer decay does not change this distinction: it is removed
by multiplying inventories, inputs, and outputs by the corresponding scalar
exponential. The corollary does not apply to unknown fractionation or arbitrary
reactive tracers; those change the assumed operators.

**Multiple signatures.** For several independently varied environmental inputs,
apply (4) separately to each input and each material. All recovered diagonal
contrasts commute. If their joint signatures distinguish every pair of stores,
their common eigenspaces are one-dimensional, and the same normalization
proves Theorem 1. If signatures coincide, only the corresponding common
invariant subspaces are obtained by this step. This does not claim that every
repeated-signature case is unidentifiable: other anchored measurements or
structural restrictions can still identify it.

## 4. Exact water-only equivalence and its dimension

For the next theorem b,q,e and any additional calibrated linear measurements
are fixed, not estimated. Let H include rows 1^T,q^T,e^T and these additional
measurement rows; h=rank H. Multiple fixed input allocations form a matrix B
of rank r (the single-input case is B=b). Assume the baseline with these
inputs and outlet q^T is controllable and observable.

For every invertible T satisfying

    H T=H,                    T B=B,

define

    K0[T]=T(K0-Dq)T^(-1)+Dq,
    K1[T]=T(K1-De)T^(-1)+De.                              (5)

**Theorem 2 (complete local water-only equivalence).** In the affine class,
(5) gives the entire local input-output equivalence class under the fixed
anchors, provided all internal transfer rates are strictly positive uniformly
on [0,1]. Its dimension is exactly

    (n-h)(n-r).                                             (6)

All models in a sufficiently small neighborhood of T=I are physical,
conservative and observationally identical for every allowed forcing.
Ideal water-following tracer channels do not reduce (6).

**Proof.** Write T=I+X. The anchor conditions are precisely HX=0 and XB=0.
Thus X is an arbitrary map from R^n/im B into ker H, a vector space of
dimension (n-r)(n-h). Invertibility is an open condition around I.
Uniform strict positivity on the compact forcing interval persists for small X.
Moreover 1^T T=1^T, q^T T=q^T and e^T T=e^T show directly that both matrices
in (5) have zero column sums.

The transformed water generator is T(A+u Bw)T^(-1). Therefore x[T]=T x by
uniqueness of the forced linear system, since TB=B and initial incremental
inventory is zero. All anchored outputs and co-transported label outputs are
identical. A nonmonomial T need not map the *whole* positive orthant onto
itself: physicality follows from the transformed rate inequalities and the
nonnegative forcing. No whole-orthant order-isomorphism is asserted.

For completeness, equality of baseline impulse responses of two minimal
realizations gives a unique similarity. In the single-input case take
T=Rtilde R^(-1). Equality of H0,H1 and the factorization in Theorem 1 show
Atilde T=TA, T b=b, and q^T T=q^T. Equality of mixed environmental kernels
then gives Bwater_tilde T=T Bw. Equality of each further calibrated linear output's baseline
responses on the spanning columns of R gives H T=H. The ET row is recoverable
even though ET=u e^T x vanishes at u=0: switch u to any positive value at the
observation time and take the right-hand outlet-ET limit divided by that value.
The state is continuous at the switch, giving e^T x at the baseline state. With multiple inputs,
choose any n independent baseline reachability columns and repeat the same
argument; well-definedness follows by applying the full observable row span.
Thus every equivalent realization is of the form (5).

There is no hidden stabilizer: if T commutes with A and TB=B, it fixes every
baseline reachability vector and hence T=I. The derivative of the orbit map
has the same trivial kernel. Its inverse is the smooth reachability-basis
formula above. Consequently the local equivalence class is a manifold of the
stated dimension, rather than merely containing that many formal directions. □

**Theorem 3 (static/contrasting-material phase diagram).** In the static subclass
K1=0, an equivalence (5) remains static exactly when T commutes with De.
In the affine subclass, adding a tracer with known fixed loss profile g
restricts (5) exactly by T Dc = Dc T, where Dc=De-Dg.
If the equal-signature blocks have sizes m_a, write H_a for columns of H
and B_a for rows of B within block a. The surviving local dimension is

    sum_a (m_a-rank H_a)(m_a-rank B_a).                    (7)

**Proof.** For static models the second line of (5) is zero iff TDe=DeT.
For the tracer, at u=0 it shares the *same* baseline realization as water.
Minimality makes the baseline similarity unique, so separate arbitrary
similarities cannot be selected for the two materials. Subtract their mixed
kernel identities; this gives TDc=DcT, and conversely this commutation
establishes the joint conjugacy. A matrix commuting with a diagonal matrix
has nonzero entries only inside equal-eigenvalue blocks. Within each block,
H_a X_a=0 and X_a B_a=0 give the quotient-to-kernel dimension argument in
Theorem 2. Strict positivity and minimality establish the exact local-fibre
interpretation. □

For a scalar multiple of De, any known rho != 1 gives the same exact block
structure. When De has pairwise distinct entries, (7) vanishes because the
1^T row fixes every diagonal scaling. Additional water channels with rho=1
leave (6) unchanged. Thus adding forcing can identify a *fixed* architecture,
while permitting compensating forcing-dependence in other transfers can
restore the ambiguity. This is not a contradiction of fixed-model forcing
identifiability results: the admissible model class has been enlarged.

## 5. Exact four-store witness and maximal physical interval

Use the matrices in exact.py:

    K0 = (1/100) [ -7  3  1  2 ]      q=(8,1,2,4)/100,
                 [  4 -9  3  1 ]      e=(8,4,1,0)/100,
                 [  2  4 -8  3 ]      b=(1,0,0,0)^T,
                 [  1  2  4 -6 ]      K1=0.

Let v=(-1,4,-8,5)^T/5, w=(0,2,1,0)^T, N=v w^T and T(theta)=I+theta N.
Exactly, N^2=0, HN=0, Nb=0, and T^(-1)=I-theta N. Both transformed K
matrices are given by (5).

**Theorem 4 (continuous physical witness).** The transformed model is physical
for every u in [0,1] exactly for

    -1/10 <= theta <= 1/8.                                (8)

Every model on this entire interval has identical water and ideal
water-following-label outputs for every input history. At theta=0 the network
is driver-independent; at nonzero theta it generally is not. Thus an apparent
learned environmental dependence can be observationally spurious.

**Proof.** Expanding the nilpotent conjugacy gives the exact degree-(2,1)
polynomial

 K(theta,u) = K0 + theta(NA-AN) - theta^2 NAN
             + u[theta(DeN-NDe)+theta^2 NDeN].              (9)

For each off-diagonal entry, exact.py converts the quadratic in theta to its
three Bernstein coefficients on (8), separately at u=0 and u=1. The 72
coefficients are nonnegative rational numbers. The degree-two Bernstein
basis is ((1-t)^2, 2t(1-t), t^2); its entries are nonnegative and sum to one
on [0,1]. Interpolation in u therefore proves nonnegativity on the whole
continuous rectangle, not only on the finitely tested endpoints.
Conservation was proved in Theorem 2. Conversely two entries of (9) are

    K_41=1/100+theta/10,       K_31=1/50-4theta/25.

Their nonnegativity forces exactly (8). Invertibility holds for all real
theta, since N^2=0. The conjugacy identities prove all-forcing equivalence.
The exact baseline controllability and observability determinants are
2197/10^12 and -23163231/10^20, respectively, so minimality is not presumed.
Finally the retained-solute mixed response coefficient is

    Z_01(theta) = -2 theta / 15625,                       (10)

whereas Z_01(0)=0. This identity is also checked exactly. □

For H=[1^T;q^T;e^T], rank H=3 and rank b=1. The full local affine fibre has
three dimensions, although (8) exhibits only one curve through it.
One added independent internal-inventory measurement removes that local
fibre in this four-store example. Adding one more independent injection
location reduces its dimension from three to two. These are statements
about this anchored model, not universal counts of field instruments.

## 6. Sensitivity in the directions water cannot identify

At a driver-independent base K1=0 and a retained tracer g=0, set T=I+theta X
with HX=0 and Xb=0. The derivative of the retained-tracer generator at zero is

    [X,A] + u[De,X].

For a unit initial tracer pulse, z(t)=exp(A t)b. Writing the parameter
sensitivity as Xz+xi, the Xz part is invisible to q^T and the remaining part is

    xi' = A xi + u[De,X]z,          xi(0)=0,
    J_X(t)=q^T xi(t).                                      (11)

This follows by substituting into the differentiated linear ODE; the [X,A]
terms cancel. Formula (11), not sensitivity of the water outputs, is used
in design.py to target the unidentifiable directions.

For coefficient observations in (4), the derivative is particularly simple:

    dZ[X] = O[De,X]R.                                      (12)

Since O,R are invertible, its kernel is exactly the commutant of De inside
the anchored gauge space. For g=rho e, multiply the informative contrast by
1-rho. This explains why arbitrarily many co-transported channels can add
practical precision without removing structural ambiguity.

A coordinate-level conditioning bound is also elementary. If distinct e_i
have minimum gap delta>0 and 1^T T=1^T, then

    ||T-I||_F <= sqrt(n)/delta * ||De T-T De||_F.           (13)

Indeed the squared off-diagonal norm is bounded by the commutator's squared
norm divided by delta^2. Each diagonal entry of T-I is minus the sum of its
column's off-diagonal entries; Cauchy-Schwarz bounds their squared sum by
(n-1) times the off-diagonal squared norm. Add the two bounds. This is not
an output-noise-to-parameter-error bound: conditioning of O,R and recovery
of the response coefficients must also be included.

## 7. Finite-time reconstruction without response derivatives

**Theorem 5 (two-time-scale controlled reconstruction).** Fix a baseline spacing
h>0 and a short middle-dwell duration delta>0. Define F=exp(h A), and suppose
R_h=[b,Fb,...,F^(n-1)b] and O_h=[q^T;q^T F;...;q^T F^(n-1)] are invertible.
Assume the admissible model class satisfies a known bound

    delta * max(||A||, ||A+Bw||, ||A+Bz||) < log(2),        (14)

in a submultiplicative matrix norm. Keep the distinct-contrast assumption of
Theorem 1. Then sampled baseline impulse responses and the three families of
finite-time middle-dwell responses

    H_pq = q^T F^(p+q)b,
    J^s_pq = q^T F^p exp(delta G_s) F^q b,
    G_0=A, G_w=A+Bw, G_z=A+Bz,       0<=p,q<n             (15)

identify the unknown network up to permutation. No response derivatives are
required. Each entry is an outlet response after a baseline dwell qh, a
controlled middle dwell delta (u=0 or 1, water or tracer), and baseline dwell ph.
Repeated experiments and a known source pulse remain required; these are not
all extracted from one arbitrary natural weather series.

**Proof.** H=O_h R_h and H^(-1)J^s=R_h^(-1)exp(delta G_s)R_h. Condition (14)
gives ||exp(delta G_s)-I||<1. Thus the absolutely convergent logarithm series
log(I+Y)=sum_(j>=1) (-1)^(j+1)Y^j/j recovers delta G_s. To verify the identity,
substitute the absolutely convergent exponential series: the scalar analytic
identity log(exp(z))=z near zero implies identical power-series coefficients,
and absolute convergence permits the same substitution in a single matrix.
The logarithm of the conjugated matrix is the conjugated logarithm; convergence
is preserved under a fixed similarity because each partial sum is conjugated.
The recovered generators are therefore

    Ghat_s = log(H^(-1)J^s)/delta = R_h^(-1)G_s R_h.

Set Ahat=Ghat_0, Bwhat=Ghat_w-Ghat_0, Bzhat=Ghat_z-Ghat_0. With
chat=(q^T b,...,q^T F^(n-1)b) and bhat=e_1, the conservation normalization and
contrast diagonalization in Theorem 1 apply verbatim with R_h replacing R.
Every candidate in the bounded class has the same logarithms, so the argument
proves uniqueness as well as construction. The bound is a sufficient
anti-aliasing restriction, not a necessary condition. Without it, a generator
logarithm ambiguity cannot simply be ignored. The sampled minimality condition
is separate from continuous-time minimality. This proves the theorem. □

The two time scales serve different purposes: h can be chosen to separate
observable modes, while delta controls the unique generator logarithm. One
does not need to take the logarithm of F, so h itself is not constrained by
(14). This is a constructive alternative to the derivative data, not a theorem
of numerical stability. In the example, h=10 days and delta=1 day reconstruct
all coefficients to below 8e-11 absolute floating-point error without passing
the true contrast rates to the estimator. But the resulting Hankel condition
number is still about 2.3e6. See finite_time.py and its complete spacing sweep.

## 8. What the results do not establish

No theorem above identifies an arbitrary nonlinear catchment, chooses a
correct number of physical stores from finite noisy observations, validates
perfect mixing, or ensures a natural weather record supplies persistent
excitation. No superiority over HBV, LSTM, or a large-sample baseline is claimed.
All simulations are synthetic. No catchment data, Lean proof, or external
review is included. The positive result is especially limited when several
deep stores have identical or zero effective ET contrast. Unknown reactions,
source profiles, nonshared transport, and state-dependent coefficients require
new analysis. Numerical conditioning is a substantial obstacle, not a detail.
