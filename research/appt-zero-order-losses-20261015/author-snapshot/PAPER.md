# Three nonnegative spectral losses at the APPT zero-order boundary

Yongxian Zhang (张永贤), South China University of Technology.
Research manuscript, 15 October 2026, Asia/Shanghai. No external funding.
OpenAI AI assistants assisted. Original material copyright 2026 Yongxian
Zhang, all rights reserved; credited sources retain their original notices.

Author proof, independent current-source review pending. This manuscript
uses the already proved zero-order value and actual-state estimates. It
does not claim a second entropy-value theorem, an external human review,
a priority certificate, a new major-problem count or a Lean theorem.

## 1. Domain, credited inputs and the remaining boundary

Let rho be an actual complex positive semidefinite trace-one density on
C^m tensor C^n, 2<=m<=n, which remains PPT after every global unitary.
Write D=mn, gamma=n/m, and order its actual eigenvalues decreasingly.
For alpha>0 put

    e_alpha(rho)=log D-S_alpha(rho),
    E_alpha(m,n)=max_APPT e_alpha,
    ell=D lambda_D,       Q=sum_i(D lambda_i-1)^2.

The optimization uses the original density matrices, not a relaxed list
of moments. Its positive value is at least log[D/(D-1)], attained as a
lower benchmark by the actual uniform rank-(D-1) APPT state. In this
manuscript alpha tends to zero through positive real values and m tends
to infinity, while every integer n>=m is allowed. Neither alpha log m
nor alpha gamma is required to converge or stay bounded.

The captured earlier SMALL_ORDER_BOUNDARY.md supplies these ordinary
theorems for every sequence A_m>0 tending to zero:

    W=max{1,1-m^(-alpha)+(alpha gamma)/2},
    D E_alpha/W -> 1                                    (1)

uniformly over n>=m and 0<alpha<=A_m; and for EVERY actual APPT state,

    D e_alpha=1-ell^alpha+(alpha/2)Q+o(1+alpha gamma),     (2)

with the same uniform quantifiers, including uniformity in the state.
The o term in (2) keeps the exact trace-centering correction. The value
(1) is not a new claim here.

For m>=3 put h=m-1, S=m(m+1)/2, j=D-S+1 and

    b=lambda_j>0,       t=1/(D b).

The existing actual-APPT physical estimates, specifically Z4 and Z7 of
that manuscript, give

    |t-1|<=1/m+2/(m-1),
    t^2 Q<=8+(D/h^2)min{1,h t ell}.                     (3)

The coefficient eight is a finite physical bound, not an asserted
attained exceptional variance for the particular state. The preceding
proofs use the true ordered spectrum, partial-transpose witnesses and
normalization. They are explicitly credited inputs here.

The earlier Z2 near-minimizer theorem treats alpha log m tending to a
FINITE tau and alpha gamma tending to a FINITE c, with a=exp(-tau)>0.
It gives the hole branch, bulk branch and two-point critical tie. It
does not state the uniform criterion below at tau tending to infinity,
degenerating phase gaps, or arbitrary oscillation among those regimes.
The fixed-positive-order SUBUNIT_RIGIDITY.md also has a different domain.

## 2. Exact physical deflation and a nonnegative decomposition

Define from the actual pivot and variance

    v=(h^2/D)(t^2 Q-8)_+,
    z=ell^alpha,       a=(h t)^(-alpha),
    beta=alpha D/(2h^2 t^2),
    W_t=1+(beta-a)_+.

Here x_+=max{x,0}, and 0^alpha=0 for positive alpha. The deflation is
essential: Q/gamma alone can include exceptional mass on a bounded
aspect path. There is no replacement of an actual integer rank by a
continuous multiplicity.

By (3), EXACTLY at every permitted finite dimension,

    0<=v<=min{1,h t ell}.                                (4)

For 0<alpha<=1 and u=h t ell, one has u^alpha>=min{1,u}.
Consequently

    z=a u^alpha>=a v.                                   (5)

No limiting argument or independent choice of z and v was used in (5).
Define the three losses

    L_0=z-a v,
    L_P=(beta-a)_+(1-v),
    L_B=(a-beta)_+ v,       L=L_0+L_P+L_B.               (6)

All three are nonnegative. The subscripts on the last two terms identify
the lost side of a phase choice, not independently feasible states.
Direct algebra gives the exact identity

    L=W_t-[1-z+beta v].                                 (7)

Since 0<=ell<=1, the bracket is nonnegative, so also 0<=L<=W_t.
In particular 1-L/W_t always lies in [0,1].

## 3. Uniform relative loss theorem

**Theorem A (every zero-order path).** For every A_m>0 tending to zero,

    sup_(n>=m, 0<alpha<=A_m, rho actual APPT)
      | e_alpha(rho)/E_alpha(m,n) - [1-L(rho)/W_t(rho)] |
            ->0.                                       (8)

All quantities in (6) are evaluated on the actual density at the actual
integer dimensions and real order. Therefore, on EVERY stated sequence,
relative nearoptimality is equivalent to

    L/W_t ->0,                                         (9)

and also to the simultaneous vanishing of L_0/W_t, L_P/W_t and L_B/W_t.
This handles oscillating dimension, aspect, order and phase gaps without
selecting a fixed branch. It is a complete observable spectral criterion
for entropy nearoptimality in this window; it does not classify every
possible empirical spectral law, eigenbasis, or exact finite optimizer.

**Proof.** First the deflation loses at most a bounded amount before
multiplication by alpha. More precisely, directly from its definition,

    0<=alpha Q/2-beta v<=4alpha/t^2.                    (10)

If t^2Q>=8 the difference is exactly 4alpha/t^2; otherwise v=0 and the
same interval bound follows. This treats both sides of the positive part.
By (3), t is bounded away from zero once m exceeds one common threshold.
Thus (2), (7) and (10) give, uniformly in every parameter and state,

    D e_alpha=W_t-L+o(W),                              (11)

because W>=max{1,alpha gamma/2}, so W is comparable with 1+alpha gamma,
and alpha->0 uniformly in the indicated order interval.

To replace the state-dependent scale by the known value scale, put
a_0=m^(-alpha) and c=alpha gamma. The uniform t estimate and h=m-1 give

    |a-a_0|=O(alpha/m),
    beta=(c/2)[1+O(1/m)].                              (12)

For example log(a/a_0)=alpha log[m/(h t)]=O(alpha/m);
a_0<=1 and alpha<=1/2 eventually. All constants can be chosen independent
of n, alpha and the density once m is large. The positive-part map is
1-Lipschitz, and W>=max{1,c/2}; hence

    W_t/W=1+O(1/m)                                    (13)

uniformly. Combining (1), (11), (13), 0<=L/W_t<=1 and the eventual positive
denominators gives (8). Nonnegativity of each term in (6) proves both
directions of (9) and of its three-term version. This completes the proof.

## 4. The old finite window and the degenerate corners

The criterion can be used directly without extracting any parameters.
The following consequences explain what happens at familiar boundaries.

If alpha log m->tau<infinity and alpha gamma->c<infinity, put
a_*=exp(-tau)>0. Then a->a_*, beta->c/2 and W_t has a positive finite
limit. If c<2a_*, nearoptimality is exactly z->0: when c>0, L_B forces
v->0 and then L_0 forces z->0; conversely z>=a v makes z->0 sufficient.
When c=0, (7) gives L=z-beta v+o(1) directly, and beta v->0. There is
no claim that Q/gamma must vanish when gamma stays bounded.

If c>2a_*, L_P forces v->1 and L_0 forces z->a_*; their converse also
follows from (6). Since c>0, gamma->infinity, and the actual definition
and (3) give v-Q/gamma->0. These are the old high-branch conditions.

If c=2a_*>0, the last two terms of (6) vanish automatically and the first
term tends to zero precisely at the two old limiting pairs (0,0) and
(a_*,1). To check the only potentially extra case, if v->v_* in (0,1),
then (4) implies u>=v, hence z=a u^alpha>=a v^alpha->a_*.
It cannot also satisfy z-a v->0. The same argument treats v_*=1;
v_*=0 gives z->0 directly. Compactness proves the distance-to-two-points
version, including alternating sequences. Thus (8) recovers Z2 without
relabeling it as a new result.

Now suppose alpha log m->infinity, so a->0.

* If alpha gamma->c in (0,infinity), (6) gives exactly z->0 and v->1.
* If alpha gamma->0, it gives exactly z->0, with NO requirement on v.
* If alpha gamma->infinity, then W_t~beta->infinity; L_0<=z<=1 and
  a<=1 eventually, so (9) is exactly v->1. No unweighted least-power
  condition survives at that relative scale.

The last conclusion in fact holds whenever alpha gamma->infinity,
without a limit assumption on alpha log m. It is a consequence of the
present criterion, not a new value theorem or a substitute for a separate
W2 body-law theorem. When none of these parameters converges, (6)-(9)
already give the complete criterion; subsequences are unnecessary in its
statement.

## 5. Actual continuum of nearoptimal variances at a collapsing tie

The absence of a v condition at the double zero corner is necessary.
Here is an actual APPT construction for every prescribed p in [0,1].
Let l>=2 be an integer, s=sqrt(p), and choose

    m=l^(l^2),       n=2l m,       D=2l m^2,
    alpha=1/l^2,     H=l,         k=D/2.

These are physical integer dimensions and rank. Take a projection P of
rank k and a unit vector w orthogonal to its range. Put

    b_0=(H+1)m,       d=b_0-H^2>=0,
    B_s=b_0 I+2Hs P-d ww*,
    Z=(D-1)b_0+2Hs k+H^2,       rho_s=B_s/Z.             (14)

The eigenvalues before normalization are b_0+2Hs (k copies), b_0
(D-k-1 copies) and H^2 (one copy). Thus B_s is positive definite and
Tr B_s=Z>0. At s=0 the first two blocks simply coincide.

For every global unitary and unit partial-transpose witness with Schmidt
coefficients r_1>=...>=r_m>=0, the projection term is at least
-2Hs sum_(i<j)r_i r_j, and the negative projector term is at least
-d r_1^2. Since 0<=s<=1 and the cross sum is nonnegative, their sum with
the b_0 term is at least the already exact quadratic

    b_0 sum r_i^2-2H sum_(i<j)r_i r_j-d r_1^2
      =(H r_1-T)^2+(H+1)[(m-1)Q_0-T^2]+(2H+1)Q_0>=0,

where T=sum_(i>=2)r_i and Q_0=sum_(i>=2)r_i^2. The final inequality is
Cauchy-Schwarz. This proves APPT after every global unitary, with no
commutation assumption on the conjugated witness. The negative-projector
bound uses its largest witness eigenvalue r_1^2, and the projection bound
uses the sum of the negative witness eigenvalues. Both hold for any
projection of the stated actual rank.

For explicit asymptotics set

    p_0=H^2/[(H+1)m],    kappa=2Hs/[(H+1)m],
    t_0=Z/(D b_0)=1+kappa/2-(1-p_0)/D.

The three normalized levels are (1+kappa)/t_0, 1/t_0 and p_0/t_0.
For the actual middle pivot j, one has k<j<=D-1, so t=t_0 even when
s=0. Here k<j follows from D/2>S-1 since gamma=2l>=4. Normalization
has not been dropped. Direct summation gives the exact variance

    Q=D{[k(1+kappa)^2+(D-k-1)+p_0^2]/(D t_0^2)-1}.

Consequently

    Q/gamma->s^2=p,       v->p,
    z=(p_0/t_0)^(1/l^2)->0.                             (15)

For detail, t_0=1+O(1/m), m kappa->2s and the half/half baseline has
variance D kappa^2/(4 t_0^2); replacing one baseline entry by p_0 costs
only O(1) in Q. Division by gamma=2l makes that cost vanish. The
deflation eight and t,h factors also vanish on this scale. Finally
alpha log m=log l, alpha log[H^2/(H+1)]=o(1) and alpha log t_0=o(1),
so z=l^(-1)exp(o(1))->0.

These dimensions satisfy the exact CANONICAL moving tie

    alpha gamma=2/l=2m^(-alpha),

but both sides tend to zero. Equations (6)-(9) or the all-state identity
then prove e_alpha(rho_s)/E_alpha->1 for every p in [0,1]. Thus the
nontrivial continuum of variance limits is real on original APPT states.
Extending the finite-window two-point rule into this degenerate corner
would exclude p in (0,1) incorrectly. This is not a new counterexample to
any correctly stated earlier theorem.

## 6. A separate exact zero-order endpoint

For alpha=0, S_0=log rank. The existing shifted-star argument shows every
singular actual APPT density for m>=3 has exactly the uniform rank-(D-1)
spectrum: a zero least eigenvalue forces all the other ordered eigenvalues
equal, and trace one determines them. Thus E_0=log[D/(D-1)], and

    e_0/E_0=1 if the density is singular, 0 if it is full rank.       (16)

Define L/W_t at zero order instead by the piecewise loss zero for a
singular state and one for a full-rank state. With this explicitly separate
definition, (8) remains valid for sequences of NONNEGATIVE orders tending
to zero, including arbitrary alternation between alpha=0 and alpha>0.
Equation (16) is exact; the positive-order error is uniform. No value is
assigned to 0^0, and the rank endpoint is not derived by substituting zero
into the positive-order kernels. Full-rank examples (14) also show why
positive orders tending to zero do not force eventual singular rank.

## 7. Scope of the new argument and verification

The new part is the physical deflation, exact three-loss identity, uniform
all-state relative criterion, arbitrary zero-boundary oscillations and
the actual degenerate-tie continuum example. The old value (1), state
identity (2), physical estimates (3), singular-state fact and the base
negative-spike sufficient quadratic are credited. The actual construction
uses a reduced projection strength and exact integer multiplicities.

Local source comparison and bounded primary-source searches are recorded
separately. No worldwide priority or full-paper absence claim follows.
Checks are finite author controls and do not replace the ordinary proof.
Independent full current-source review and final public metadata binding
are still pending. No Lean, Lake or kernel audit was run or enlarged;
no Gaussian worktree, Git main, preprint submission, email, Release or DOI
was changed. This is not complete all-order spectral rigidity or APPT=ASEP.
