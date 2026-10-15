# Exact APPT entropy optimizers in every fixed-order linear critical window

Yongxian Zhang (张永贤), South China University of Technology.
15 October 2026 (Asia/Shanghai).

**Status: complete author manuscript, pending independent ordinary review.**
This packet has no new Lean proof or kernel audit. The current user instruction
is root-only research, with no subagents. All new proof checking in this packet
is by the authoring agent; it must not be described as independent review.
Previously reviewed C0-C4 and E0-E4 are explicit inputs, left unchanged.

## 1. Original object, critical ratio, and compact parameter set

Let 2<=m<=n be integers, D=mn, and let APPT(m,n) be the ORIGINAL set of
complex positive semidefinite trace-one matrices whose partial transpose is
positive semidefinite after EVERY global unitary conjugation. No necessary
spectral relaxation replaces this feasible set. For each fixed finite alpha>0
write

    e_alpha(rho)=log D-S_alpha(rho),
    E_alpha(m,n)=max_(rho in APPT(m,n)) e_alpha(rho).

Here S_alpha is the usual Renyi entropy, and S_1 is von Neumann entropy;
all logarithms are natural. The maximum exists: the feasible set is closed
in the compact set of density matrices, and the entropy is continuous at
each fixed positive order. In raw positive coordinates x with trace S,

    e_alpha(x/S)=[log(sum x_i^alpha/D)-alpha log(S/D)]/(alpha-1),
    e_1(x/S)=sum x_i log x_i/S-log(S/D).                         (1)

Use the kernels from C0 and E0,

    psi_alpha(y)=[y^alpha-1-alpha(y-1)]/(alpha-1),
    psi_1(y)=y log y-y+1,
    c_+(p)=4p/(2-p), c_-(beta)=2beta/(1-beta),
    r_+(p)=(2-p)psi_alpha(1+p)/(2 alpha p), 0<p<2,
    r_-(beta)=(1-beta)psi_alpha(1-beta)/(alpha beta), 0<beta<1,
    d_alpha=max{sup r_+,sup r_-}.                              (2)

Both ratios extend continuously by zero at BOTH endpoints. Each is positive
inside its interval. Their maxima are attained in the interior, d_alpha>0,
and the sets

    P_alpha={p: r_+(p)=d_alpha},
    B_alpha={beta: r_-(beta)=d_alpha}                            (3)

are compact interior sets, possibly empty separately, but not both empty.
Do not assume that one sign wins for every order, or that each set is a
singleton. Associate z_+(p)=2p/(2-p), z_-(beta)=beta/(1-beta), and put

    r_alpha=min z over (3), R_alpha=max z over (3),
    I_alpha=[r_alpha/2,2 R_alpha].                              (4)

Thus 0<r_alpha<=R_alpha<infinity. The same nonempty compact interval is
used for both finite spectral families, even if one critical sign is absent.
This definition requires only the explicit one-dimensional ratios (2).

Set t=2/(m-1), q_m=1+t. The exact integer bulk value is

    G_alpha(m,D)=max_(k in {0,...,D})
                     e_alpha((I+t Pi_k)/(D+t k)),              (5)

where Pi_k is any orthogonal rank-k projection. The ratio bound q_m makes
every such state actual APPT. The eventual maximizing ranks are interior;
the explicit floor/ceiling calculation is the head-free case of Section 7.

## 2. The complete finite-window target H0-H4

Fix alpha>0 and A>0 BEFORE the dimensions. There is an M_(alpha,A) such
that, for every integer pair m<=n with m>=M_(alpha,A) and

    |n-d_alpha m^2|<=A m,                                      (6)

the actual maximum and every optimizing matrix have the following exact
description. No effective M_(alpha,A) is supplied.

For z in I_alpha define

    kappa=2/(m-1+z), q=1+kappa, a=2+kappa,
    p=a z/(z+2), beta=a z/[2(1+z)],
    c=m^2(t-kappa)=2m^2 z/[(m-1)(m-1+z)].                       (7)

The positive family and the negative family are, respectively,

    rho_+(z,k)=(I+kappa Pi+p |v><v|)/(D+kappa k+p), v in ran Pi,
    rho_-(z,k)=(I+kappa Pi-beta |v><v|)/(D+kappa k-beta), v in ker Pi,
    ||v||=1, rank Pi=k, R<=k<=D-K,
    R=m(m-1)/2, K=m(m+1)/2.                                   (8)

Both families are ACTUAL APPT for every listed z,k, including exact PSD
boundary points. The normalization uses their actual trace. In the negative
family 1-beta=(m-1)/[(m-1+z)(1+z)]>0; in the positive family 0<p<2.

**H0.** The exact value in the entire band (6) is

    E_alpha(m,n)=max{G_alpha(m,D),
                     max_(z in I_alpha, k in L_+(z)) e_alpha(rho_+(z,k)),
                     max_(z in I_alpha, k in L_-(z)) e_alpha(rho_-(z,k))}.
                                                                    (9)

L_+(z) and L_-(z) consist of the actual floor and ceiling of the respective
real-rank maximizer, calculated explicitly in Section 7. Each candidate is
evaluated; ties are retained, and nearest-integer selection is not assumed.
The maxima in (9) are attained. This is a compact scalar/integer formula,
not a claim that every winning z is given in closed form.

**H1.** Every optimizing density matrix is a unitary conjugate of a winning
bulk state in (5), or a winning state in (8)-(9). All bulk/sign/z/rank ties
and all unitary conjugates are included. Every optimizer with c>0 in the
physical coordinates below has EXACTLY one anomaly, no other positive or
negative anomaly mass, exact protection equality, and an endpoint body.

**H2.** Section 5 proves a relative same-body deformation for each sign,
including alpha=1. It excludes arbitrary positive tiny tail mass and
protection slack at EACH finite optimizer in the eventual band. Limiting
one-anomaly convergence by itself would not prove H1.

**H3.** Sections 4 and 6 prove the original all-unitary sufficiency, including
the negative-diagonal and negative-edge assignments, endpoint counts,
trace-weighted convex decomposition, and every integer-rank equality.

**H4.** At alpha=1/2,

    d_(1/2)=5 sqrt(5)-11,
    P_(1/2)=empty,
    B_(1/2)={(sqrt(5)-1)/2},
    c_*=1+sqrt(5), z_*=(1+sqrt(5))/2.                           (10)

In that complete band, every nonbulk optimizer is eventually in the
negative family. The positive maximum can be omitted from (9) at this
order. Bulk/negative ties and all integer/z ties are still retained.

## 3. Localization of every potentially profitable actual spectrum

Here and below all constants may depend on the fixed alpha,A. Take any
actual APPT spectrum lambda in decreasing order. Use the exact physical
coordinates of C0 Sections 4-6 and E0 Section 3:

    b=lambda_(D-K+1)>0, x_i=lambda_i/b,
    kappa=x_R-1, c=m^2(t-kappa),
    p_i=x_i-1-kappa (i<=R), beta_j=1-x_(D+1-j) (j<=K),
    T=sum p_i+sum beta_j,
    y_i=clip(x_i,[1,1+kappa]).                                 (11)

The original Schmidt witnesses imply

    0<=kappa<=t, T<=c/2, T<=m,
    sum p_i^2+sum beta_j^2<=34, 0<=x_i<=3.                      (12)

These are bounds on EVERY actual spectrum; the anomaly counts are not
assumed bounded. For reference, two other credited E0 results are

    |D[e_alpha(x/Tr x)-e_alpha(y/Tr y)]-H|
                 <=C_alpha(kappa T+T^2/D),
    H=sum psi_alpha(1+p_i)+sum psi_alpha(1-beta_j),              (13)
    D[G_alpha(t,D)-G_alpha(kappa,D)]
                 >=alpha delta_m c/2 (1-C/m),
    delta_m=D/m^3=n/m^2,                                     (14)

where (14) is for bounded c. The same input's coercivity says that every
potentially profitable spectrum e_alpha(rho)>=G_alpha(m,D) has c<=B when
delta_m>=d_alpha/2, without a finite-head assumption. On the full band (6)
this applies for large m.

Since psi_alpha(1+p)<=C_alpha p^2 and
psi_alpha(1-beta)<=C_alpha beta^2, including beta=1, (12)-(14) imply

    D[e_alpha(rho)-G_alpha(m,D)]
             <=C_alpha c^2-alpha delta_m c/2+C_alpha,B c/m.   (15)

There is therefore a fixed c_small>0 such that no potentially profitable
state can have 0<c<=c_small once m is large. This relative estimate remains
valid for c below every power of 1/m.

For any sequence of potentially profitable states in (6), delta_m->d_alpha.
C0's actual additive maximum law bounds the limsup of their D-scaled profit
by F_alpha(d_alpha)=0. Their profit is nonnegative, so it converges to zero.
C4 then forces the exact clipped-body loss

    J_m=D[B_alpha(kappa)-e_alpha(y/Tr y)] ->0                   (16)

and l1 convergence, in distance, of the full anomaly lists and c to the
critical maximizer set. C2 identifies that set as the empty lists/c=0,
or precisely one p in P_alpha with c=c_+(p), or precisely one beta in
B_alpha with c=c_-(beta). The empty branch is excluded at c>0 by (15).
Sequential contradiction makes all these conclusions UNIFORM over every
potentially profitable state with c>0 in (6).

For each such state choose its retained anomaly u to be either p=p_1 near
P_alpha or beta=beta_1 near B_alpha. Its sign may vary between states.
The two alternatives are separated in l1 because their retained mass
stays bounded away from zero. The retained positive mass is in a compact
subset of (0,2), or the negative mass in a compact subset of (0,1).
Write tau=T-u. Then tau->0 uniformly; all other anomalies are at most eta
for any chosen eta>0 once m is large. The full tail energy is <=eta tau.
This statement includes a growing number of heads.

Write y_i=1+kappa theta_i, with 0<=theta_i<=1. The first R theta's are
one and the last K are zero. Let

    mu=D^-1 sum theta_i, nu=D^-1 sum theta_i^2, sigma^2=nu-mu^2.

Uniform Taylor expansion over ALL these bounded body coordinates gives

    e_alpha(y/Tr y)=alpha kappa^2 sigma^2/2+O_alpha(kappa^3),
    B_alpha(kappa)=alpha kappa^2/8+O_alpha(kappa^3).             (17)

The same equations hold at alpha=1 by expanding x log x. Now
D kappa^2~4 d_alpha m tends to infinity. Divide (16) by D kappa^2 and
use (17) to conclude sigma^2->1/4 uniformly. No quantitative rate in
C4 is needed, and no positive derivative is claimed for an arbitrary
unprofitable, nearly flat body.

## 4. Exact costs for both retained signs, and actual boundary states

For every assignment of the original R positive anomalies to distinct
negative Schmidt edges and the K negative anomalies to distinct positive
edges or diagonal slots, the original all-unitary APPT condition gives

    M=a I-kappa 11^T-P >=0, a=2+kappa,                       (18)

where P is symmetric and entrywise nonnegative. An edge anomaly contributes
its mass to both symmetric off-diagonal entries; a negative diagonal
contributes 2 beta. Taking absolute values of a Rayleigh vector justifies
PSD from the nonnegative Schmidt tests for this matrix with nonpositive
off-diagonal entries. At bounded c and large m, aI-P is positive definite.
The exact rank-one condition and nonnegative inverse-walk expansion give

    c>=[kappa m^2 a/(m-1)] K_a(P),
    K_a(P)=1^T(aI-P)^(-1)1-m/a.                              (19)

Keep the retained positive p on an edge, or negative beta on a diagonal,
and fill EVERY other original witness slot with all omitted anomalies.
The positive and negative slot lists are distinct within their own lists;
an edge can carry one mass from each sign, as the original witness permits.
The prefix uses only two or one vertices. No disjoint-tail construction
or bound on tail count is needed. Monotonicity of every walk retains the
whole prefix and the first rest walk, proving

    c>=C_s(kappa,u)+g(kappa)tau,
    C_+(kappa,p)=2 kappa m^2 p/[(m-1)(2+kappa-p)],
    C_-(kappa,beta)=2 kappa m^2 beta/[(m-1)(2+kappa-2beta)],
    g(kappa)=2 kappa m^2/[(m-1)(2+kappa)].                   (20)

Let c_0 be the unique root c_0=C_s(t-c_0/m^2,u), kappa_0=t-c_0/m^2.
For the retained compact mass sets, 0<c_0<m^2 t and c_0 is uniformly
bounded. Indeed F(c)=c-C_s(t-c/m^2,u) is negative at zero and positive
at m^2 t; its derivatives are

    F'_+(c)=1+2p(2-p)/[(m-1)(2+kappa-p)^2],
    F'_-(c)=1+4beta(1-beta)/[(m-1)(2+kappa-2beta)^2].            (21)

Both exceed one; the denominators stay uniformly away from zero. Also
c_0<=C_s(t,u), whose compact limit is c_s(u). Uniformly at the bounded
c values in question, F'<=1.1 and g>=1.8 eventually. Thus (20) implies

    c>=c_0, c-c_0>=1.6 tau.                                  (22)

These inequalities have NO additive errors. Solving the positive root
gives z=2p/(2+kappa_0-p); solving the negative root gives
z=2beta/(2+kappa_0-2beta). Both yield the contrast (7), and respectively
the masses p,beta in (7). Their z tends to the corresponding critical
z in (4), uniformly. In particular every retained boundary z is in
I_alpha eventually.

For completeness, the boundary state is sufficient for the ORIGINAL APPT
definition, even if its middle body has not yet been made an endpoint.
Let theta have the fixed top R/bottom K values from Section 3 and set

    u_i(r)=1+r theta_i+p 1_(i=1)            (positive),
    u_i(r)=1+r theta_i-beta 1_(i=D)         (negative).          (23)

At r=kappa_0 every negative witness eigenvalue is paired with a top-R
raw value, every positive witness eigenvalue with a bottom-K value, and
the remaining D-m^2 witness eigenvalues are zero. The rearrangement
inequality makes this the adverse assignment over EVERY global unitary.
At the positive boundary P is a single p edge; direct inversion gives

    1^T(aI-P_edge)^(-1)1=m/a+2p/[a(a-p)]=(m+z)/a.

At the negative diagonal boundary P=2beta e_i e_i^T and

    1^T(aI-P_diag)^(-1)1=m/a+2beta/[a(a-2beta)]=(m+z)/a.

In each case aI-P is positive definite and kappa_0(m+z)/a=1, so (18)
is PSD by the exact rank-one criterion, including equality. A negative
head may instead occupy a positive edge; its cost is

    K_a(P_negative-edge)=2beta/[a(a-beta)]
                     <2beta/[a(a-2beta)]=K_a(P_diag).           (24)

That assignment also has a positive definite base and satisfies the same
rank-one PSD test. Relabeling covers every edge/diagonal position. These
are all adverse patterns. Zero Schmidt coordinates are included in PSD.
Thus u(kappa_0)/Tr u(kappa_0) is actual APPT for EVERY middle body (23).
The counts R,K are feasible because D>=m^2; their intervals are disjoint.

## 5. Relative entropy removal and strict finite improvement

We now compare the actual spectrum with (23) at its OLD contrast kappa.
Changed coordinates exclude the retained head. Their signed sum d obeys
|d|<=tau, their absolute sum is tau, and their squared mass is <=eta tau.
Every changed base is q=1+kappa for a removed positive and 1 for a
removed negative. In particular no expansion at the retained negative
coordinate or at zero is needed.

Define the exact residual on the changed coordinates

    H_rest=sum_other-positive[psi_alpha(1+kappa+p_i)-psi_alpha(1+kappa)]
                               +sum_other-negative psi_alpha(1-beta_j).

Taylor bounds near one, psi'_alpha(1+kappa)=O_alpha(kappa), and the tail
energy bound give

    |H_rest|<=C_alpha(eta+kappa)tau.                           (25)

For alpha!=1, let W=D^-1 sum u_i(kappa)^alpha and s=D^-1 Tr u(kappa).
All retained raw coordinates stay in a compact positive interval, so
W=1+O_alpha(kappa+1/D), s=1+O(kappa+1/D). The exact increments are

    sum x_i^alpha-sum u_i(kappa)^alpha=alpha d+(alpha-1)H_rest,
    Tr x-Tr u(kappa)=d.

Subtract their exact normalized logarithms first. Expansion of ONLY the
increments, of size O_alpha(tau/D), yields

    D(e_x-e_u)=[(alpha d+(alpha-1)H_rest)/W-alpha d/s]/(alpha-1)
                                                        +O_alpha(tau^2/D).

The identity

    W-s=(alpha-1)[s-1+D^-1 sum psi_alpha(u_i(kappa))]

makes the uncanceled linear d contribution O_alpha((kappa+1/D)tau).
Together with (25), this proves the RELATIVE upper

    D[e_alpha(x/Tr x)-e_alpha(u(kappa)/Tr u(kappa))]
              <=[C_alpha eta+C_alpha(kappa+1/D+tau/D)]tau.      (26)

At alpha=1 put A_1=sum u_i log u_i. The raw log-moment increment is
d+H_rest. Subtract exactly

    D(e_x-e_u)=(d+H_rest)/(s+d/D)
                     +A_1[1/(s+d/D)-1/s]-D log(1+d/(D s)).

Since A_1/D=O(kappa+1/D), the same cancellation proves (26). This
separate argument covers von Neumann entropy. The bounds are for each
FIXED alpha, not uniform as alpha grows with the dimensions.

Holding theta and the retained mass fixed throughout kappa<=r<=kappa_0,
direct differentiation of (1) gives

    d/dr e_alpha(u(r)/Tr u(r))
                     =alpha r sigma^2+O_alpha(r^2+1/D).        (27)

Here is the expansion behind this estimate. The body power sum is
D[1+alpha r mu+alpha(alpha-1)r^2 nu/2+O_alpha(r^3)] and its derivative
is D[alpha mu+alpha(alpha-1)r nu+O_alpha(r^2)]. The single retained
coordinate adds a uniformly bounded term and derivative. The exact trace
is D(1+r mu)+h, where h=p or -beta is constant. Subtracting alpha times
the trace logarithmic derivative cancels alpha mu and leaves
alpha r(nu-mu^2)+O_alpha(r^2+1/D). At alpha=1 the log-moment is
D[r mu+r^2 nu/2+O(r^3)] plus the bounded head correction, and differentiation
of A_1/Tr u-log(Tr u/D) gives r(nu-mu^2)+O(r^2+1/D).
The head/body coordinates are uniformly positive, including the retained
negative head; these differentiations do not use a singular endpoint.

By Section 3, sigma^2->1/4 uniformly and r~2/m throughout this interval.
Thus (27) is >=alpha r/8 eventually. Define g_alpha=alpha d_alpha/8>0.
Since D kappa/(8m^2)->d_alpha/4, integration gives, for all sufficiently
large m in the ENTIRE band,

    D[e_alpha(u(kappa_0)/Tr u(kappa_0))
                    -e_alpha(u(kappa)/Tr u(kappa))]
                           >=g_alpha(c-c_0).                 (28)

Choose eta small enough that C_alpha eta<=g_alpha/4, then choose m large
enough to make the remaining bracket in (26) <=g_alpha/4. Combining
(22), (26), (28) proves

    D[e_alpha(rho)-e_alpha(u(kappa_0)/Tr u(kappa_0))]
                        <=g_alpha tau/2-g_alpha(c-c_0).       (29)

If tau>0 this is strictly negative. If tau=0 it is strictly negative
whenever c>c_0. The right comparator is actual APPT by Section 4.
Every actual optimizer is potentially profitable because bulk is feasible.
Consequently every optimizer with c>0 has EXACTLY

    tau=0, c=c_0.                                             (30)

This argument retains errors proportional to the removed mass. Replacing
them with an additive o(1) would not exclude finite mass such as exp(-m^2).
We also do not claim that every potentially profitable state itself already
has (30); it has a strictly better physical comparator unless (30) holds.

## 6. Every body endpoint and every matrix equality

After (30), keep the retained mass, exact boundary contrast, first R and
last K endpoint coordinates fixed, and vary every middle coordinate in
[1,1+kappa_0]. The entire raw cube consists of actual APPT vectors by
Section 4. A raw point is a convex combination sum w_v v of raw vertices,
but its normalized density vector is

    x/Tr x=sum_v [w_v Tr v/Tr x] (v/Tr v).                     (31)

These are TRACE-WEIGHTED convex coefficients, not w_v. Distinct raw
vertices remain distinct after normalization, since at least one fixed
positive raw coordinate is shared (the bottom endpoint, or the retained
negative head). For alpha>1 the power sum of a normalized nontrivial
mixture is strictly below the weighted power sums; for 0<alpha<1 it is
strictly above them. The sign of 1/(alpha-1) in (1) makes e_alpha strictly
less than the largest vertex deficit in both cases. At alpha=1 strict
convexity of negative entropy gives the same result.

An optimizing raw point must therefore be a vertex. Its upper endpoint
count is an ACTUAL integer rank k, R<=k<=D-K. It is exactly (8). This
also proves all the matrix equalities, rather than merely constructing
a few maximizing spectra. At c=0, (12) gives T=0 and the same normalized
interval-vertex argument identifies precisely the winning bulk states.
Unitary invariance of the ORIGINAL feasible set and of entropy includes
every conjugate. No nonendpoint equality or omitted degeneracy remains.

## 7. Explicit scalar evaluation and exact integer selection

For fixed z and sign let h=p or -beta, and set

    Q=q^alpha-1,
    H_+=(q+p)^alpha-q^alpha, H_-=(1-beta)^alpha-1,
    S=D+kappa k+h, A=D+Q k+H_s.                               (32)

For alpha!=1 the exact deficit is

    f_s(z,k)=[log(A/D)-alpha log(S/D)]/(alpha-1),
    k_s^*=[Q(D+h)-alpha kappa(D+H_s)]/[(alpha-1)kappa Q].      (33)

Q is nonzero at every alpha>0,z in I_alpha. The real-rank derivative is

    partial_k f_s=kappa Q(k_s^*-k)/(A S).                      (34)

Thus it increases until k_s^* and decreases afterwards for BOTH alpha<1
and alpha>1. Do not drop the factor alpha-1 when making this comparison.

At alpha=1 set L=q log q,

    H_+=(q+p)log(q+p)-q log q,
    H_-=(1-beta)log(1-beta),
    f_s(z,k)=(kL+H_s)/S-log(S/D),
    k_s^*=[(L-kappa)(D+h)-kappa H_s]/kappa^2,
    partial_k f_s=kappa^2(k_s^*-k)/S^2.                       (35)

For either sign, uniformly on compact z in I_alpha,

    k_s^*/D=1/2+O_alpha(kappa)+O_alpha(1/(D kappa))
                       =1/2+O_alpha,A(1/m).                  (36)

For example, subtracting the head-free rank gives an O_alpha(1/kappa)
correction: the numerator's head part is Qh-alpha kappa H_s=O_alpha(kappa),
while its denominator is a nonzero constant times kappa^2. At alpha=1
(L-kappa)h-kappa H_s=O(kappa). The head-free rank is D times

    theta_alpha=[Q-alpha kappa]/[(alpha-1)kappa Q],
    theta_1=[q log q-kappa]/kappa^2,

which equals 1/2+O_alpha(kappa). This proves (36). Since D~d_alpha m^3
and R,K=O(m^2), floor(k_s^*),ceil(k_s^*) are physical ranks in
[R,D-K] eventually. Those one or two integers form L_s(z). Directly
compare their EXACT deficits, retaining both when equal.

Every family value is continuous in z at each fixed physical rank. The
maximum over the finitely many ranks R<=k<=D-K is continuous on the
compact I_alpha, and equals the floor/ceiling expression by (34)-(36).
This proves attainment even across rank switches. Every candidate is
actual APPT and every actual optimizer was classified in Sections 3-6,
so (9) follows with no relaxed upper/lower gap. An inactive critical sign
may be omitted eventually: otherwise optimizing states of that sign
would contradict the uniform critical localization in Section 3.

## 8. The half-order negative transition, with exact sign separation

At alpha=1/2, psi_(1/2)(y)=(sqrt(y)-1)^2. Write
v=sqrt(1-beta), 0<v<1. The negative ratio in (2) is

    r_-(beta)=2v^2(1-v)/(1+v).                               (37)

Its derivative vanishes inside this interval exactly when v^2+v-1=0;
the endpoint values vanish, and the derivative changes from positive
to negative at v_*=(sqrt(5)-1)/2. Since 1-v_*^2=v_*, beta_*=v_*,
its maximum is 2v_*^5=5sqrt(5)-11, and c_*=2/v_*=1+sqrt(5).
Also z_*=1/v_*=(1+sqrt(5))/2.

For the positive ratio write u=sqrt(1+p), 1<u<sqrt(3). Then

    r_+(p)=(3-u^2)(u-1)/(u+1)<9/50.                         (38)

The last inequality is equivalent to
P(u)=50u^3-50u^2-141u+159>0. Its cubic discriminant is -7765800<0,
so it has exactly one real root. P(0)=159>0 and its leading coefficient
is positive; the root is negative, and P is positive for every u>=0.
Finally sqrt(5)>559/250 because 5-(559/250)^2=19/62500>0, hence
5sqrt(5)-11>9/50. This is an exact strict separation, not a numerical
plot of selected spectra. It proves all of (10), including uniqueness
of the nonempty critical profile and the absence of a positive branch.
Here (4) becomes I_(1/2)=[(1+sqrt(5))/4,1+sqrt(5)]. The exact finite
negative family in (8), with (33), covers the entire window (6).

## 9. Credited inputs, collision screen, and limits

The credited ordinary proof inputs are C0-C4 in
../appt-cubic-entropy-20261014/PAPER.md and E0-E4 in
../appt-exact-cubic-bulk-20261014/PAPER.md. Their full-list bounds,
critical compactness, and relative trace-normalized comparison are used
as theorems, with their original review status. The single-positive
finite deformation at alpha=2 was previously proved in W0-W3 in
../appt-critical-purity-optimizer-20261014/PAPER.md. The present manuscript
extends that finite classification to EVERY fixed positive entropy order,
both critical signs, all ties, and von Neumann entropy; it does not
recount the purity case as a separate new conjecture solution.

Before the new manuscript, the bounded 15 October primary collision screen
checked current abstracts/version metadata for Ahiable--Kothakonda--Winter,
arXiv:2608.03390v2 (18 September), and Tran, arXiv:2609.18568v1
(16 September), plus targeted primary-index searches. Existing families,
spectral criteria, and numerical eventual-bulk observations are credited
in the input packets. Their full papers were not newly re-audited here.
This bounded screen found no examined statement matching H0-H4; it is
neither an exhaustive literature search nor a priority certificate.

This is an eventual finite theorem on (6), not a solution of all finite
dimensions, all cubic ratios, arbitrary dimension growth, or varying
entropy order. Away from the critical ratio below order two, multiple
anomalies can win, as the C0 paper explains. No general exact ceiling for
the minimal final N_alpha, no effective M_(alpha,A), and no general ASEP
claim is made. The irrational half-order threshold in (10) does not inherit
the purity quarter-lattice gap; finite dimension coincidences and all
ties are kept. Finite symbolic/numerical controls check stated identities
and adversarial mistakes; the general mathematical proof is Sections 3-8.

No new formalization, old audit-root expansion, independent author-external
peer review, submission, email, DOI, or Release is part of this packet.
Promotion to the already-proved repository table remains pending the
inherited separate independent ordinary-review gate. The author manuscript
and its self-audit are retained transparently in the research-draft index.

Personal independent research, no external funding. AI assistance by OpenAI
assistants is disclosed. Original authorship and all rights reserved;
existing third-party inputs retain their own attribution and licenses.
