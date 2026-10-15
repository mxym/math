# The coupled APPT entropy profile at linear Rényi order

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. ORCID 0009-0000-3864-3536;
mxymmxym1@gmail.com. 14 October 2026, Asia/Shanghai.
No external funding. OpenAI AI assistants assisted research and writing.
Copyright 2026 Yongxian Zhang; all rights reserved for original material.

This note closes the previously excluded all-aspect range where the positive
Rényi order is comparable to the smaller local dimension. The finite physical
projection/spike family is an existing input. The new step is a necessary
physical coupling between the actual spectral peak and the middle interval,
followed by matching optimization. Everything stated here is an ordinary
mathematical proof; there is no additional Lean coverage or priority claim.

## 1. The sharp scalar profile and its quantifiers

Use the objects of [PAPER.md](PAPER.md): 2<=m<=n, D=mn, actual APPT densities,
normalized eigenvalues y_i=D lambda_i, and for alpha>1

    M*_alpha=max_APPT (1/D) sum_i y_i^alpha,
    E_alpha=log D-min_APPT S_alpha=log M*_alpha/(alpha-1).

For c>0, r>=0, 0<=L<=2 and 0<=theta<=1 define

    g_c(L)=2cL^2/[3(2-L)]              if L<2,
    exp[-g_c(2)]=0,

    F(c,r;L,theta)
      =exp(-cL theta)
         [1+theta(exp(cL)-1)+r exp(-g_c(L))],

    F_*(c,r)=max_(0<=L<=2, 0<=theta<=1) F(c,r;L,theta).    (L1)

The convention at L=2 is continuous. At L=0 the value is 1+r, independent
of theta. F is continuous on every compact c,r parameter rectangle, including
both width endpoints; its maximum is attained and is continuous in c,r.

**Theorem L1 (linear orders, every aspect ratio).** For every fixed pair
0<c_-<=c_+<infinity,

    sup_(n>=m, c_-m<=alpha<=c_+m)
      |M*_alpha/F_*(alpha/m,3^alpha/D)-1| ->0.              (L2)

Moreover, uniformly on the same set,

    E_alpha ~ log F_*(alpha/m,3^alpha/D)/(alpha-1),
    (alpha-1)E_alpha-log F_*(alpha/m,3^alpha/D) ->0.         (L3)

These statements allow arbitrary diverging or oscillating aspect ratios and
all peak-to-bulk competition windows. In particular if alpha/m->c>0 and
3^alpha/D->r in [0,infinity), then

    M*_alpha ->F_*(c,r),
    m E_alpha ->log F_*(c,r)/c.                            (L4)

If instead 3^alpha/D->infinity, M*_alpha~3^alpha/D. The range of Theorem L1
has alpha/D<=c_+/m; replacing u_D=3D/(D+2) by 3 in this note is therefore
justified uniformly. This replacement is not valid in an arbitrary-order
theorem with no alpha/D control.

**Theorem L2 (all positive orders up to linear growth).** Let C>0 be fixed.
Let P_alpha be the explicit equivalent U0 in [UNIFORM_PROFILE.md](UNIFORM_PROFILE.md).
Define, for all sufficiently large m,

    P^lin_alpha = P_alpha                         if 0<alpha<=sqrt(m),
    P^lin_alpha = log F_*(alpha/m,3^alpha/D)/(alpha-1)
                                                  if sqrt(m)<alpha<=Cm.

Then

    sup_(n>=m, 0<alpha<=Cm) |E_alpha/P^lin_alpha-1| ->0.    (L5)

The split at sqrt(m) is only a convenient way to display one uniform
approximant. It is not a physical transition or an additional assumption.

## 2. A necessary physical coupling, without a spectral ansatz

For m>=3 retain the actual notation

    R=m(m-1)/2, S=m(m+1)/2, j=D-S+1,
    b=lambda_j>0,
    g_i=(lambda_i-lambda_(D+1-i))/b, i<=R.

Section 2 of PAPER.md and the actual quantum rearrangement in
SHARP_ASPECT_RATIO.md A4 show that every placement of these nonnegative
decreasing gaps on the edges of K_m has adjacency matrix at most 2I.
This uses actual all-global-unitary Schmidt witnesses, with distinct
eigenvalue slots. It is not an assumed characterization of arbitrary lists.

Place g_1 on edge {1,2} and let w=g_R. Replacing all other edges by w can
only decrease the Perron eigenvalue: each matrix is nonnegative and the
entrywise inequality bounds every nonnegative Rayleigh vector. Compress
the resulting weighted clique to the orthonormal pair-average vector and
the average of its remaining m-2 vertices. The compression is

    [ g_1                     sqrt(2(m-2)) w ]
    [ sqrt(2(m-2)) w          (m-3) w       ]  <=2I.

The uniform-vector test also gives 0<=w<=2/(m-1). Thus
2-(m-3)w>=4/(m-1)>0, and the determinant inequality gives

    g_1 <=2-eta_m(w),
    eta_m(kappa)=2(m-2)kappa^2/[2-(m-3)kappa].             (L6)

eta_m is increasing on [0,2/(m-1)]: differentiating kappa^2/(2-(m-3)kappa)
gives a nonnegative numerator kappa[4-(m-3)kappa].

Set the actual middle interval endpoints

    A=D lambda_j, B=D lambda_R, kappa=B/A-1>=0.

Since lambda_(D+1-R)<=b, w>=kappa. Since lambda_D>=0,
lambda_1/b<=g_1+1. Hence every actual APPT state satisfies the exact coupling

    0<=kappa<=2/(m-1),
    y_1 <= A[3-eta_m(kappa)].                             (L7)

The right side is positive throughout the indicated interval. This
inequality is the upper-bound bridge missing from an independent-peak plus
independent-bulk estimate.

## 3. The actual upper bound in bounded critical peak mass

Fix c_-,c_+ as in L2 and first restrict

    r_m=3^alpha/D<=R_0

for any fixed R_0>0. This forces D>=3^(c_-m)/R_0. In particular
m^k/D->0 uniformly for every fixed k. All arguments in this section use
this implication explicitly.

The actual middle set Bset={R,...,j} has N=D-m^2+2 entries. Its complement
has m^2-2 entries and includes the largest eigenvalue for all large m.
Since every normalized eigenvalue lies in [0,3], the actual middle mean mu
satisfies

    mu=(D-sum_(i outside Bset)y_i)/N,
    |mu-1|<=2(m^2-2)/N=O(m^2/D).                         (L8)

If kappa>0 put theta=(mu-A)/(B-A), so 0<=theta<=1 and
A=mu/(1+kappa theta). If kappa=0 put theta=0; this last identity still holds.
Convexity of x^alpha on [A,B] gives the genuine-state secant estimate

    (1/D) sum_(i in Bset)y_i^alpha
      <=(N/D) A^alpha[1+theta((1+kappa)^alpha-1)].          (L9)

By PAPER.md G13, y_2<=v_m->1+sqrt(2)<3. All exceptional entries other
than the largest contribute at most

    m^2 v_m^alpha/D
      <=R_0 m^2(v_m/3)^alpha ->0                         (L10)

uniformly. No unknown exceptional multiplicity or purity error is hidden
in the moment estimate.

To pass to the compact scalar limit, take any sequence of such actual states
and, after subsequences, let

    alpha/m->c in [c_-,c_+], r_m->r in [0,R_0],
    m kappa->L in [0,2], theta->theta_0 in [0,1].

Compactness of m kappa follows from L7. Equations L8-L9 and
alpha log mu=O(m^3/D)->0 show that the middle contribution has limsup at most

    exp(-cL theta_0)[1+theta_0(exp(cL)-1)].                 (L11)

If L<2, the exact protection term satisfies

    alpha eta_m(kappa) -> 2cL^2/(2-L),
    alpha log[1-eta_m(kappa)/3] -> -2cL^2/[3(2-L)].        (L12)

This includes L=0, where the protection tends to zero after multiplication
by alpha. Applying L7 and A=mu/(1+kappa theta), the largest moment term
has limsup at most

    r exp(-cL theta_0-g_c(L)).                            (L13)

If L=2, the denominator 2-(m-3)kappa tends to zero, whereas
m eta_m(kappa)=2(1-2/m)(m kappa)^2/[2-(m-3)kappa] tends to infinity.
Thus alpha eta_m(kappa)->infinity, and
(1-eta_m(kappa)/3)^alpha<=exp[-alpha eta_m(kappa)/3]->0.
The largest contribution tends to zero, exactly as prescribed at L=2.
The factor A^alpha is bounded by mu^alpha->1, so it cannot undo this limit.

Adding L10-L13 proves limsup M_alpha<=F_*(c,r) for every such subsequence.
This is an upper bound on the original quantum optimization, not solely on
the projection/spike family.

## 4. Every scalar competitor has an actual finite lower state

First fix 0<L<2 and 0<=theta<=1. Put kappa=L/m. For large m define

    eta=eta_m(kappa), d=2-kappa-eta,
    k=max(1,min(D-1,floor(theta D))).

One has kappa<=2/(m-1), d>=0, because

    d[2-(m-3)kappa]=[2-(m-1)kappa](2+kappa)>=0.           (L14)

Let P be a rank-k orthogonal projection and v a unit vector in its range.
The matrix I+kappa P+d vv* is positive definite. Normalize it by

    Z=D+kappa k+d, rho=(I+kappa P+d vv*)/Z.               (L15)

The actual Schmidt SOS G26 in PAPER.md applies with c there equal to
kappa and q there equal to 2-(m-3)kappa. Its full protection coefficient
is precisely eta. Thus rho is APPT after every global unitary; arbitrary
rank-k P and v in its range exist in the actual D-dimensional space.
No sampled-unitary test or new unproved spectral criterion is used.

With theta_D=k/D and z=1+kappa theta_D+d/D, the exact normalized spectrum is

    (3-eta)/z             once,
    (1+kappa)/z           k-1 times,
    1/z                   D-k times.                    (L16)

For the bounded-r_m range of Section 3, alpha/D->0 and
theta_D=theta+O(1/D). Consequently on every c,r limiting path the moment
of this actual state tends to F(c,r;L,theta).

The two width endpoints are also physically attained in the limit:

* L=0: the exact pure spike (I+2vv*)/(D+2) has moment
  [D/(D+2)]^alpha[r_m+(D-1)/D]->1+r.
* L=2: take the projection-only state proportional to I+[2/(m-1)]P,
  with the same integer rank choice. For every unit Schmidt vector,
  sum_(i<j)s_i s_j<= (m-1)/2. The usual contraction bound for P on the
  negative Schmidt subspace therefore proves its actual APPT property.
  Its two-level moment tends to F(c,r;2,theta), whose peak term is zero.

To make the bounded-r assertion uniform, suppose a bad dimension/order
sequence existed. Extract convergent c_m,r_m and a maximizing scalar
pair at their limit. If that pair has 0<L<2, use L15; for an endpoint use
the corresponding state above. The matching limit contradicts a strict
lower shortfall. For the upper side choose an actual maximizing state
(compactness guarantees one), extract the interval parameters in Section 3,
and use its upper bound. Continuity of F_* then gives, uniformly for
r_m<=R_0,

    M*_alpha-F_*(alpha/m,r_m) ->0.                        (L17)

## 5. Unbounded peak mass and the entropy conclusion

The exact endpoint y_1<=u_D and the actual middle bound G11 give, uniformly
for the entire range c_-m<=alpha<=c_+m,

    M*_alpha <=r_m+o(1)r_m+K_(c_+),
    M*_alpha >=r_m [D/(D+2)]^alpha=r_m[1+O(1/m)].         (L18)

Here the non-largest exceptional contribution is bounded by
r_m m^2(v_m/3)^alpha=o(r_m). The middle contribution is at most
(1+delta_m)^alpha<=K_(c_+) since delta_m=O(1/m). The lower bound is the
pure spike; alpha/D<=c_+/m justifies its uniform multiplicative estimate.

The scalar formula independently has

    1+r_m<=F_*(alpha/m,r_m)<=r_m+K'_(c_+).                (L19)

Its peak factor is at most one, and its bulk factor is at most exp(2c_+).
For r_m>=R_0, L18-L19 bound the relative discrepancy by
o(1)+O(1/R_0). Combine with L17 and then let R_0 tend to infinity.
This proves the fully uniform L2.

The competitor L=2,theta=1/2 gives F_*(c,r)>=cosh c. In particular
log F_*>=log cosh c_->0 uniformly in Theorem L1. The relative moment
estimate makes log M*-log F_* tend uniformly to zero; division by this
positive logarithmic lower bound proves both statements in L3. This also
establishes L4 and the unbounded-r conclusion without suppressing the
first nonzero entropy deficit in the bulk-dominated range.

## 6. Explicit reduction, pure bulk, and connection to smaller orders

For a fixed 0<L<=2 set K=cL, B=exp(K)-1 and
C_0=1+r exp[-g_c(L)]. The scalar objective is exp(-K theta)(C_0+B theta).
Its derivative has the sign of B-K C_0-KB theta. At theta=1 it is strictly
negative, since B-K(1+B)=exp(K)(1-K)-1<0. Hence its maximizing mixing
parameter and value are exactly

    theta_*=0, value=C_0                         if B<=K C_0;
    theta_*=1/K-C_0/B,                           otherwise,
    value=(B/K) exp[-1+K C_0/B].                          (L20)

The second theta_* lies strictly between zero and one. Thus computing F_*
requires only a one-dimensional compact width maximization. This formula
is analytic, not a claim that a grid search proves optimality.

When r=0, for fixed theta the bulk objective is the exponential moment
of a mean-zero two-point variable with width L. It increases with L:
its derivative in K is theta(1-theta) exp(-K theta)(exp(K)-1)>=0.
The maximum is therefore at L=2. Formula L20 gives the closed expression

    F_*(c,0)=[(exp(2c)-1)/(2c)]
                exp[-1+2c/(exp(2c)-1)].                 (L21)

The optimizing bulk upper-level fraction is
1/(2c)-1/(exp(2c)-1), rather than 1/2 except in the c->0 limit.

As c->0, uniformly for all r>=0,

    F_*(c,r)-1 ~ r+c^2/2.                                (L22)

Indeed, the bulk mean-zero two-point variable has absolute value at most
2 and variance L^2 theta(1-theta)<=1. Its exponential Taylor expansion
uniformly bounds the bulk increment by (c^2/2)[1+O(c)]; the peak is at most
r. Conversely take L=2-sqrt(c),theta=1/2. Its bulk increment is
(c^2/2)[1+O(sqrt(c))], and its peak factor is 1+O(sqrt(c)), since both
cL theta and g_c(L)=O(sqrt(c)). This lower bound has relative error
O(sqrt(c)) against r+c^2/2, independently of r. This proves L22.

For diverging alpha with alpha/m->0 and alpha<=Cm, the older G1 gives

    M*_alpha-1 ~ u_D^alpha/D+alpha(alpha-1)/(2m^2)
                ~3^alpha/D+(alpha/m)^2/2.

The last replacement is uniform because alpha/D<=C/m, and alpha->infinity
removes the difference between alpha(alpha-1) and alpha^2. Equation L22
therefore gives relative agreement of the moment excesses, and hence of
their positive logarithms, even when both excesses vanish. Together with
Theorem L1, a compact-subsequence argument proves the growing-order branch
of L5. For alpha<=sqrt(m), U2 already gives the required uniform equivalent.
These two branches prove Theorem L2.

## 7. Scope of the advance

The profile at linear order is a coupled peak/bulk maximum. Adding separately
maximized peak and bulk terms generally does not give its sharp value.
The upper bound proves this coupling on the actual APPT set; the lower
states prove that it is attainable to the stated leading accuracy.

Theorem L2 extends U2 from o(m) to every fixed multiple of m for arbitrary
n>=m. U1 still supplies every positive order without an upper bound when
n/m is bounded. The all-aspect absolute-error theorem M1 remains valid
for arbitrary diverging orders. A first nonzero relative equivalent for
arbitrary aspect with alpha/m->infinity, fixed-m moving-order optimization,
exact finite minima outside the proved small positive-order band, absolute
separability and complete formalization remain unresolved here.

The original physical family and fixed-order inputs are credited in the
companion map. The relevant current primary entropy papers were checked
for their actual stated ranges; no matching linear-order all-aspect profile
was located in those read sections. This is not a global priority certificate.
There is no new Release, DOI, aiXiv submission, or external peer-review claim.
