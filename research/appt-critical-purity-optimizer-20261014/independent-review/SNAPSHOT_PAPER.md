# Every exact APPT purity optimizer in the finite critical window

Ordinary written proof, 14 October 2026. Proposed; complete review pending.
The feasible set is the original complex all-global-unitary APPT set.
No new Lean execution, audit root, or absolute-separability assertion.

## 1. Full finite statement

Fix any A>0. There exists M_A such that for all integers m>=M_A, n>=m,

    |n-m^2/4|<=A m, D=mn,                              (1)

the actual maximum purity is the exact finite variational value below.
Let t=2/(m-1), and P_G be the exact integer-rank q-body maximum, q=1+t.
For z in the COMPACT interval [1,3], define

    kappa_z=2/(m-1+z), a_z=2+kappa_z,
    p_z=a_z z/(z+2),
    B_z=D(1+kappa_z)-kappa_z p_z-p_z^2,
    k_*(z)=D/a_z-p_z(a_z+2kappa_z+2p_z)/(a_z kappa_z),
    J_z={floor(k_*(z)),ceil(k_*(z))},
    Q(z,k)=[D+(2kappa_z+kappa_z^2)k
                   +2(1+kappa_z)p_z+p_z^2]
                           /(D+kappa_z k+p_z)^2.        (2)

When floor=ceil the rank set has a single member. For all large m the
ranks in J_z satisfy R<=k<=D-K uniformly in z, where
R=m(m-1)/2,K=m(m+1)/2. Define

    V_m,n=max_(z in [1,3], k in J_z) Q(z,k).             (3)

**Theorem W0-W3.** On the ENTIRE actual APPT set,

    P_max(m,n)=max{P_G(m,n),V_m,n}.                     (4)

All equality matrices are exactly the following winning families.

* If P_G is maximal, every q-body matrix is
  (I+t Pi)/(D+t k), k=ceil((m-1)n/2), Pi any rank-k projection.
* If V_m,n is maximal, take EVERY pair (z,k) attaining (3), any rank-k
  orthogonal projection Pi, and any unit v in its range. The matrix is

    rho=(I+kappa_z Pi+p_z |v><v|)/(D+kappa_z k+p_z).     (5)

Every matrix in either winning family attains the actual maximum, and
there are no other equality matrices. All genuine parameter/rank ties
within (3) are retained. The compact maximum is attained.

The previously reviewed eventual onset is

    N_2(m)=ceil((m^2+5m+7)/4).                          (6)

Within (1), if n>=N_2(m), ONLY the q family wins; if n<N_2(m), ONLY
the one-positive-head family (5) wins. Thus below onset every finite
optimizer has exactly one positive anomaly, no negative anomaly, an
exactly saturated physical protection constraint, and an endpoint body.
This is an exact finite assertion, not solely convergence to that shape.

We credit the immutable ordinary C0-C4 cubic correction, E0-E4 coarse
exact onset, and Q0-Q3 exact eventual onset manuscripts. Their reading
and review scopes stay separate. The new step is an actual relative
deformation eliminating every nonzero tail and every protection slack
even when either is arbitrarily tiny, followed by exact body optimization.

## 2. Full critical localization with no finite-head hypothesis

Use the original physical coordinates from C0/E0/Q0:

    b=lambda_(D-K+1)>0, x_i=lambda_i/b,
    kappa=x_R-1, c=m^2(t-kappa),
    p_i=x_i-1-kappa (i<=R), beta_j=1-x_(D+1-j) (j<=K),
    T=sum p_i+sum beta_j, E=sum p_i^2+sum beta_j^2.        (7)

Exact bounds are 0<=kappa<=t, T<=c/2, E<=34. Clip x to [1,1+kappa].
E0 coercivity bounds c for every potentially profitable state P(rho)>=P_G
uniformly in (1). Its RELATIVE comparison gives

    D[e_2(rho)-G_2]<=c^2/4-delta_m c+C c/m,
    e_2=log(D P), G_2=log(D P_G), delta_m=n/m^2.          (8)

Thus for large m no such state with c>0 can have c<=1/4. For ANY actual
sequence in (1), delta_m->1/4. C0 bounds its maximum additive deficit
profit by a quantity tending to F_2(1/4)=0. Every potentially profitable
sequence is therefore C4-near-maximizing. The critical maximizing set is
empty with c=0 or exactly one p=1,beta=0,c=4. The empty branch is ruled
out at c>0 by (8). Sequential contradiction makes the conclusion UNIFORM:

    p:=p_1->1, c->4, tau:=T-p->0, J_m->0,               (9)

over all potentially profitable states with c>0 in the ENTIRE band (1).
Here J_m=D[B_2(kappa)-e_2(y/Tr(y))] is the exact clipped-body loss and
B_2(kappa) is its continuous-rank deficit maximum. This covers a growing
number of positive or negative heads and tails of arbitrary tiny mass.

For use in the deformation, write

    theta_i=(y_i-1)/kappa in [0,1],
    Y=sum theta_i, Z=sum theta_i^2, sigma^2=Z/D-(Y/D)^2. (10)

All first R theta_i equal one and all last K equal zero. At c bounded,
kappa~2/m and D~m^3/4. Uniform expansion in bounded moments gives

    e_2(y/Tr(y))=kappa^2 sigma^2+O(kappa^3),
    B_2(kappa)=kappa^2/4+O(kappa^3).                     (11)

Divide J_m by D kappa^2, which tends to infinity on this band, and use
J_m->0. It follows that sigma^2->1/4 UNIFORMLY over these states.
Only this uniform variance conclusion, rather than a quantitative
rate for J_m, is needed below.

## 3. Exact finite protection of every omitted head

For every assignment of the entire original top/bottom anomaly lists,
the necessary physical Schmidt matrix is

    (2+kappa)I-kappa 11^T-P>=0.                        (12)

At bounded c the inverse aI-P is positive definite, a=2+kappa. The
credited exact rank-one/walk identity, selecting just the p edge and
filling every other slot, gives

    c>=C_eff(kappa,p)+g_eff(kappa)tau,
    C_eff=2 kappa m^2 p/[(m-1)(2+kappa-p)],
    g_eff=2 kappa m^2/[(m-1)(2+kappa)].                  (13)

In particular ALL omitted anomaly mass is retained. Let c_0=c_0,m(p)
be the unique root c_0=C_eff(t-c_0/m^2,p), kappa_0=t-c_0/m^2.
It is bounded uniformly for p near one. As established directly in Q0,

    1<=d/dc[c-C_eff(t-c/m^2,p)]<=1.1,
    g_eff>=1.8, c>=c_0, c-c_0>=1.6 tau                 (14)

for all large m and the potentially profitable states under consideration.
There are no additive errors in (13)-(14). Every remaining anomaly is
eventually at most eta=1/100, so its total square energy is at most eta tau.

## 4. A physically feasible relative deformation

Keep the SAME theta_i from (10) and the SAME p. For any k in the interval
[kappa,kappa_0] define a one-head raw vector

    u_i(k)=1+k theta_i+p*1_(i=1).                       (15)

The notation k in this section denotes a real contrast, not an integer
rank. Its endpoint kappa_0 has precisely top R values 1+kappa_0 (with
the one extra p) and bottom K values 1; all others lie between those
endpoints. Thus their adverse Schmidt pairing is (12) with a single edge.
At c_0 that edge has EXACT boundary rank-one equality. In detail there
is a unique z>0 with

    kappa_0=2/(m-1+z), p=(2+kappa_0)z/(z+2),
    1^T[(2+kappa_0)I-P_edge]^(-1)1=(m+z)/(2+kappa_0),
    kappa_0(m+z)/(2+kappa_0)=1.                        (16)

Since p<2+kappa_0, the inverse base is positive definite and the whole
Schmidt matrix is PSD. Spectral rearrangement and all edge permutations
prove actual APPT for u(kappa_0)/Tr(u(kappa_0)), even with its nonendpoint
middle body. No assumption that this new state already optimizes is used.

We now compare ACTUAL trace-normalized purities with errors proportional
to the removed mass. At the OLD contrast kappa, the difference x-u(kappa)
has positive anomalies p_i for i>=2, negative anomalies -beta_j, total
absolute mass tau, signed sum d, and energy E_rest<=eta tau. Its square
sum increment is exactly

    sum x_i^2-sum u_i(kappa)^2=2d+2kappa sum_(i>=2)p_i+E_rest. (17)

There is no cross term with the retained p, since the changed coordinates
exclude i=1. Let S_u=sum u, A_u=sum u^2. Both are comparable to D and
A_u-S_u=O(D kappa+1), uniformly. Subtracting the exact logarithms,

    D[e_2(x/Tr(x))-e_2(u(kappa)/Tr(u(kappa)))]
       <=[eta+C kappa+C tau/D+C/D]tau.                 (18)

To see the relative bound explicitly, the difference is
D log(1+(2d+2kappa sum_(i>=2)p_i+E_rest)/A_u)
-2D log(1+d/S_u). Expand these two increments, of size O(tau/D),
after subtraction. The linear d discrepancy is
2D d(1/A_u-1/S_u)=O((kappa+1/D)tau); the rest is at most
eta tau(1+O(kappa+1/D))+O(kappa tau)+O(tau^2/D).
This proves (18), even for mass smaller than every power of 1/m.

For the one-head vector (15), its exact square and trace are

    A_u(k)=D+2k Y+k^2 Z+2(1+k)p+p^2,
    S_u(k)=D+kY+p.

Uniform differentiation and Taylor expansion give

    d/dk e_2(u(k)/Tr(u(k)))
       =A'_u/A_u-2S'_u/S_u
       =2k sigma^2+O(k^2+1/D).                         (19)

By (9)-(11), sigma^2->1/4, and k~2/m throughout the bounded protection
interval. Hence the derivative in (19) is at least k/4 for all large m.
Integration over kappa<=k<=kappa_0 gives, uniformly in (1),

    D[e_2(u(kappa_0)/Tr(u(kappa_0)))
                  -e_2(u(kappa)/Tr(u(kappa)))]
       >=(c-c_0)/10.                                  (20)

Indeed the lower coefficient is D kappa/(4m^2)->1/8, so 1/10 is valid.
For sufficiently large m the bracket in (18) is at most 1/50. Combining
(18)-(20) and (14),

    D[e_2(rho)-e_2(u(kappa_0)/Tr(u(kappa_0)))]
       <=tau/50-(c-c_0)/10.                            (21)

This is strictly negative if tau>0. If tau=0 it is strictly negative
whenever c>c_0. Every actual purity maximizer with c>0 is potentially
profitable, so its maximality forces EXACTLY

    tau=0, c=c_0.                                      (22)

This eliminates every other positive or negative anomaly and every
protection slack at each finite dimension in the eventual band. It is
stronger than the limiting shape conclusion (9).

## 5. Exact finite endpoint body and integer ranks

Once (22) holds, fix p,kappa_0 and the top R/bottom K endpoint entries.
Each remaining middle raw coordinate can vary independently in
[1,1+kappa_0]. Every point in this body cube is actual APPT by (16): the
adverse top/bottom pairing does not change. A raw cube point is a convex
combination of its endpoint vertices. After trace normalization it is
a convex combination with weights multiplied by the vertex traces and
divided by the current trace, exactly as in E0 Section 2.

Purity is strictly convex on density matrices. Distinct body vertices
normalize to distinct matrices, since their retained positive-head raw
entry is identical and positive, forcing any common rescaling to be one.
Thus a body with any interior coordinate has strictly smaller purity
than some feasible endpoint vertex. Every optimizer must have an endpoint
body with an ACTUAL integer upper count k, R<=k<=D-K.

By (9) and (16) its z tends to 2, so for all sufficiently large m every
nonbulk optimizing parameter lies strictly inside [1,3]. Conversely
EVERY z in [1,3] with these endpoint counts gives an actual APPT matrix
(5) by (16). Its exact purity is Q(z,k) in (2).

For fixed z put S=D+kappa_z k+p_z. Endpoint saturation gives the exact
quadratic chord expression (a_z S-B_z)/S^2. Its derivative in S has just
one sign change, and its real optimum is S_*=2B_z/a_z, with real rank
precisely k_*(z) in (2). Only floor/ceil(k_*(z)) can be the integer winners.
Those two ranks lie in [R,D-K] for all large m uniformly in z: k_* /D
=1/2+O(1/m), while R/D,K/D=O(1/m). Every real/parameter/rank tie is kept
by taking the maximum of the two ACTUAL branch values.

Attainment can equivalently be seen as maximizing the finitely many
continuous Q(z,k), R<=k<=D-K, over compact z in [1,3]. Restricting the
winners to J_z leaves its value unchanged. This also resolves the apparent
floor/ceiling discontinuities in (3). The q family supplies all c=0
optimizers. Compactness of the actual density set guarantees a true
maximum; every optimizer with c>0 has the shape just proved. This proves
(4) and the full equality classification, with both lower families
genuinely physical.

## 6. Strict finite phase selection within the whole band

For n>=N_2(m), Q0-Q3 already proves that only q matrices optimize. The
one-head family here has c>0, so its value is strictly below P_G.

For n<N_2(m) in (1), take the rational boundary parameter z=2+8/m from
Q0. Its real trace crossing h_m(z) satisfies

    h_m(z)=(m^2+5m+7)/4+O(m^-1),
    h_m(z)-n>=1/8                                      (23)

for all sufficiently large m, since the quadratic's fractional part is
always 1/4 or 3/4. All estimates are uniform in (1), and D~m^3/4. The
real trace maximum beats the continuous q-body bound by at least
a/(m^2 D^2)>0, a fixed constant; choosing an actual nearest integer rank
loses only O(kappa_z^2/D^3)=O(m^-11). Thus this physical one-head state
strictly beats P_G. The earlier proof at n=N_2-1 extends in this way
to every smaller n still in (1), with the same uniform estimates.
Only the family (5) can optimize there. This proves the finite phase
statement without assuming global monotonicity in n.

## 7. Scope and status

All quantifiers in this theorem cover the original actual APPT set but
only the stated fixed-width O(m) critical window. A may be arbitrarily
chosen in advance; its M_A is not effective. Equation (3) is an explicit
exact finite compact scalar/rank formula, not an elementary closed form
for every winning scalar parameter. The equality description retains
that maximizing set without claiming unique z or excluding genuine ties.

The broader finite-dimension purity problem, complete entropy axis,
varying-order spectral classification, and APPT/ASEP relationship are
not solved here. Previous manuscripts/audits are unchanged. This new
ordinary proof requires its own complete source-bound independent review;
finite controls do not replace that review or provide a Lean certificate.
