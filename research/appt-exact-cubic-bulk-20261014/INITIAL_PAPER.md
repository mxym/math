# The minimal exact APPT entropy bulk onset has cubic scale

Research draft, 14 October 2026. Not yet independently reviewed. All orders
are fixed finite alpha>0; all logarithms are natural. This is ordinary
mathematics, without new Lean execution or a change in any old audit scope.

## 1. Complete statement on the original physical set

Let D=mn, 3<=m<=n, t=2/(m-1), q=1+t. For actual complex density matrices
that remain PPT after EVERY global unitary, let E_alpha(m,n) be the maximum
of log D-S_alpha(rho), with the von Neumann value at alpha=1. Let

    G_alpha(kappa,D)=max_(integer 0<=k<=D) e_alpha(k/D,kappa),
    e_alpha(theta,kappa)=
      {log[1+theta((1+kappa)^alpha-1)]
                       -alpha log(1+kappa theta)}/(alpha-1),     (1)

using the continuous alpha1 value. Thus G_alpha(t,D) is the exact best
integer-rank q projection spectrum. Every q projection is actual APPT.

Put psi_alpha(y)=[y^alpha-1-alpha(y-1)]/(alpha-1), with
psi_1(y)=y log y-y+1 and psi_alpha(0)=1. Define the positive constant

    d_alpha=max{
      max_(0<p<2) (2-p)psi_alpha(1+p)/(2 alpha p),
      max_(0<beta<1) (1-beta)psi_alpha(1-beta)/(alpha beta)}.        (2)

It is the full delta_crit(alpha) of the reviewed cubic-scale C2 theorem;
both signs are included even below order two. The maxima are attained
strictly inside their intervals. In particular d_2=1/4.

**Theorem E0-E4.** For each fixed alpha>0 there exist constants A_alpha>0
and M_alpha such that, for every integer m>=M_alpha and EVERY integer n>=m
with

    n>=d_alpha m^2+A_alpha m,                            (3)

the actual entropy maximum is EXACTLY G_alpha(t,mn). Every equality
matrix, and only such a matrix, is

    rho=(I+t Pi)/(D+t k),                               (4)

where Pi is any orthogonal rank-k projection and k is an exact winning
integer in (1). All winning-rank ties are retained.

For each m>=3 define the MINIMAL eventual onset

    N_alpha(m)=min{integer N>=m: EVERY integer n>=N
                                    has E_alpha(m,n)=G_alpha(t,mn)}.

It exists and satisfies

    N_alpha(m)=d_alpha m^2+O_alpha(m).                   (5)

In particular N_2(m)=m^2/4+O(m), with exactly the same equality spectra for
the purity maximum. This is an asymptotic formula for the minimal onset,
not an exact value of every finite N_alpha, nor its next coefficient.
No assertion is made on the exact critical line within the O(m) band.

## 2. The EXACT integer interval maximum and every equality

For kappa>=0, let raw values y_i lie in [1,1+kappa] and normalize by their
actual sum. A cube point has a convex decomposition y=sum_v a_v v into
endpoint vertices v, with a_v>=0 and sum a_v=1. Therefore

    y/Tr(y)=sum_v [a_v Tr(v)/Tr(y)] v/Tr(v).             (6)

The bracketed weights sum to one. For alpha>1 the power moment is strictly
convex; for 0<alpha<1 it is strictly concave, with the negative logarithmic
divisor reversing the inequality; for alpha1 the deficit is strictly
convex. Consequently deficit at a nontrivial mixture of distinct normalized
vertices is strictly smaller than the largest vertex deficit. Hence

    e_alpha(y/Tr(y))<=G_alpha(kappa,D),                  (7)

with equality ONLY at a winning normalized vertex. This is an exact finite
claim, retaining the actual integer rank, not the continuous-rank bound.
At kappa=0 the single normalized point is uniform. For kappa>0 and D>=2
the maximum is positive and occurs at a nonuniform endpoint vertex.

For small positive kappa the real maximum in theta is unique; its location is

    theta_*=[(1+kappa)^alpha-1-alpha kappa]
              /[(alpha-1)kappa((1+kappa)^alpha-1)]       (alpha!=1),
    theta_*=[(1+kappa)log(1+kappa)/kappa-1]/kappa        (alpha=1).

Its expansion is theta_*=1/2+O_alpha(kappa). The derivative in theta has a
linear numerator with exactly one sign change, so the winning integers are
among floor(D theta_*) and ceil(D theta_*); endpoint clipping applies if
needed outside the small-kappa range. The winning fraction is thus
1/2+O_alpha(kappa)+O(1/D).

Each integer-branch function is analytic in kappa near zero, including
alpha1. A finite maximum is locally Lipschitz and absolutely continuous.
At almost every point its derivative equals that of an active branch.
Uniform Taylor expansion for theta in [0,1] gives

    partial_kappa e_alpha(theta,kappa)
        =alpha theta(1-theta)kappa+O_alpha(kappa^2).

At an active branch this implies

    G'_alpha(kappa,D)=alpha kappa/4
                           +O_alpha(kappa^2+kappa/D^2),          (8)

uniformly for 0<kappa<=t once m is large and D>=delta_0 m^3 with any
fixed delta_0>0. Thus G'>=alpha kappa/8 eventually on the whole [0,t].
If c=m^2(t-kappa) is bounded by B, integration of (8) also proves

    D[G_alpha(t,D)-G_alpha(kappa,D)]
        >=alpha delta_m c/2 (1-C_alpha,B/m),
    delta_m=D/m^3, D>=delta_0 m^3.                      (9)

The constant in the RELATIVE error does not depend on D or its upper size.
Indeed t+kappa=4/m+O_B(m^-2) in this case. All statements remain valid across
arbitrarily many changes or ties of the winning integer; absolute continuity
justifies the integration without differentiating a chosen global branch.

## 3. Actual spectra, anomalies, and the trace budget

Use the exact physical notation from the reviewed cubic paper. For any actual
APPT spectrum lambda in decreasing order put

    R=m(m-1)/2, K=m(m+1)/2, b=lambda_(D-K+1)>0,
    x_i=lambda_i/b, kappa=x_R-1,
    p_i=x_i-1-kappa (i<=R), beta_j=1-x_(D+1-j) (j<=K),
    c=m^2(t-kappa), T=sum p_i+sum beta_j.                (10)

The maximally entangled actual Schmidt witness gives

    0<=kappa<=t, T<=R(t-kappa)<=c/2, T<=m.              (11)

The paired-gap graph and row bounds give

    sum p_i^2+sum beta_j^2<=34, 0<=x_i<=3.              (12)

These are finite inequalities for EVERY actual APPT spectrum, with no bound
on the number of anomalies. They were proved in the inherited cubic paper
Section 4 from the original arbitrary-unitary Schmidt tests, not from a
finite-exception hypothesis. The raw mean is s=D^-1 sum x_i=1+O(1/m),
uniformly here; this also follows directly from (11), the clipping below,
and D>=delta_0 m^3. We use no new formal audit of these inputs.

Clip x into [1,1+kappa], obtaining y, of mean s_0. Then s_0 in [1,1+kappa]
and D(s-s_0)=Delta:=sum p_i-sum beta_j, with |Delta|<=T. The positive
changes are EXACTLY from 1+kappa to 1+kappa+p_i; the negative ones are
EXACTLY from 1 to 1-beta_j.

## 4. Subtract entropy BEFORE expanding: a relative comparison

Let H=sum psi_alpha(1+p_i)+sum psi_alpha(1-beta_j). For fixed alpha>0,
there is a constant C_alpha such that

    |D[e_alpha(x/Tr(x))-e_alpha(y/Tr(y))]-H|
                         <=C_alpha(kappa T+T^2/D),      (13)

uniformly for the actual spectra above and large m. This bound remains true
before assuming c is bounded. It includes all trace normalization losses.
For any beta in [0,1], psi_alpha(1-beta)<=C_alpha beta^2, by continuity of
the quotient at beta=0 and beta=1; similarly the positive gain is bounded
by C_alpha p^2 for p in [0,2]. Thus H is bounded by (12), while also H<=C T.

Here is a direct proof of (13), including the possibly singular negative
heads. For alpha!=1 set W=D^-1 sum y_i^alpha and

    H_kappa=sum[psi_alpha(1+kappa+p_i)-psi_alpha(1+kappa)]
                                             +sum psi_alpha(1-beta_j).

The positive-base derivative is bounded on [1,3], so
H_kappa=H+O_alpha(kappa T), and the raw power-sum increment is exactly

    D(W_x-W)=(alpha-1)H_kappa+alpha Delta.               (14)

Both this increment and Delta are O_alpha(T). Subtract the exact power/mean
logarithms before expanding them. Since W=1+O_alpha(kappa),
s_0=1+O(kappa), and T/D is small,

    D(e_x-e_y)
      ={[(alpha-1)H_kappa+alpha Delta]/W
                          -alpha Delta/s_0}/(alpha-1)+O_alpha(T^2/D).

The exact identity

    W-s_0=(alpha-1)[s_0-1+D^-1 sum psi_alpha(y_i)]

makes the apparent linear-trace discrepancy O_alpha(kappa T). Also
H_kappa/W=H+O_alpha(kappa T). This proves (13). No derivative at 1-beta=0
is used: all negative power increments in (14) are retained EXACTLY.

For alpha1 use W_1=sum y_i log y_i. The increment is Delta+H_kappa, with
the analogous psi1 definition. Subtract exactly

    D(e_x-e_y)=(Delta+H_kappa)/s
                              +W_1(1/s-1/s_0)-D log(s/s_0).

Here W_1/D=O(kappa), log(s/s_0)=Delta/(D s_0)+O(T^2/D^2), and
Delta(1/s-1/s_0)=O(T^2/D). The same (13) follows. This proof explains why
the estimate is uniform even when D/m^3 is UNBOUNDED: no uncanceled
baseline moment-log error of order D/m^4 appears.

## 5. Coercivity uniform for ALL larger dimensions

Suppose an actual state has nonnegative profit e_alpha(rho)>=G_alpha(t,D),
and assume D>=delta_0 m^3. Equations (7), (12)-(13), T<=m and kappa<=t
give

    D[e_alpha(rho)-G_alpha(t,D)]
      <=C_alpha-D[G_alpha(t,D)-G_alpha(kappa,D)].

The global derivative lower bound following (8) implies

    D[G_alpha(t,D)-G_alpha(kappa,D)]
        >=alpha D(t^2-kappa^2)/16>=alpha delta_m c/8.

Thus c<=B_alpha,delta0, uniformly for EVERY D>=delta_0 m^3, including
unbounded delta_m. Consequently T<=c/2 and the error in (13) is at most
C_alpha,B c/m. This is a RELATIVE estimate, valid for arbitrarily small c.

## 6. Full head gain bounded by the critical linear protection budget

For any assignment of positive p_i to distinct negative Schmidt edges and
negative beta_j to positive edge or diagonal slots, the exact actual witness
matrix is

    M=(2+kappa)I-kappa 11^T-P,                           (15)

where P is symmetric nonnegative with its assigned off-diagonal weights
and diagonal 2 beta. Taking absolute values of a Rayleigh vector proves the
copositive condition equivalent to M being PSD. Thus every such assignment
is an actual necessary consequence of the original all-unitary APPT set.

At bounded c, kappa>0 for large m. A=aI-P, a=2+kappa, is positive definite,
and the exact rank-one condition gives

    c>=f_m K_a(P), f_m=kappa m^2 a/(m-1)=4+O_B(1/m),
    K_a(P)=1^T(aI-P)^(-1)1-m/a.                         (16)

This is the finite identity from the reviewed cubic Section 6. The walk
expansion K_a=sum_(l>=1) a^(-l-1)1^T P^l1 has nonnegative terms. At bounded
c, every rho(P) stays below 2-epsilon_B for large m: for a unit Perron
vector v>=0, v_i<=1 implies 1^T P^l1>=rho(P)^l, and hence
K_a>=rho(P)/[a(a-rho(P))]. This spectral gap is uniform in matrix size.

Let L=floor(m/3). Put the first L positives on mutually disjoint edges,
and the first L negatives on mutually disjoint diagonals, also disjoint
from those edges. Zero padding is allowed. The prefix uses at most 3L<=m
vertices. Fill every remaining original witness slot with all omitted
anomalies. All slot counts fit, since the original top/bottom lists have
R and K entries. The matrix P has this prefix P_0 plus a nonnegative rest.
Keeping all prefix walks and only the first rest term proves

    K_a(P)>=K_a(P_0)+2 T_tail/a^2.                      (17)

For a single disjoint positive edge p the prefix contribution is
2/(a-p)-2/a; for a single negative diagonal beta it is
1/(a-2beta)-1/a. Their values at a=2, multiplied by four, are

    c_+(p)=4p/(2-p), c_-(beta)=2beta/(1-beta).            (18)

The protected spectral gap bounds p and 2beta below 2-epsilon_B. The exact
ratios of their K_a contributions to their K_2 contributions are
2(2-p)/[a(a-p)] and 4(1-beta)/[a(a-2beta)], respectively. Both are
1+O_B(kappa), uniformly also as the corresponding anomaly tends to zero.
Therefore (16)-(17) give

    c>=(1-C_B/m) sum_prefix[c_+(p)+c_-(beta)]
                                      +(2-C_B/m)T_tail.          (19)

There is no error proportional to L: isolated-vertex contributions cancel
in K_a, and the error is relative to the anomaly costs themselves.

Because both decreasing lists have total mass T, their omitted squared mass
is at most T^2/(L+1). Tail kernel gain is thus O_alpha(T^2/L)=O_alpha,B(c/m).
Definition (2) gives prefix gain <=alpha d_alpha/2 times the prefix cost
sum in (19). Dropping the nonnegative tail-cost term now proves the FULL
head bound

    H<=alpha d_alpha c/2+C_alpha,B c/m.                 (20)

Every one of the original R+K anomalies is accounted for. In particular,
no fixed small-head ansatz or alpha>=2-only argument has been substituted
for the all-positive-order target.

## 7. Exact large-n upper and every equality matrix

Choose delta_0=d_alpha/2>0 and restrict to D>=delta_0 m^3. Any potentially
winning actual state has bounded c by Section 5. Combine (7), (9), (13) and
(20) to obtain

    D[e_alpha(rho)-G_alpha(t,D)]
      <=-{alpha delta_m(1-C_1/m)/2
                              -alpha d_alpha/2-C_2/m}c.          (21)

All constants depend only on the fixed alpha, not on n. Select A_alpha so
large that alpha A_alpha/2-alpha d_alpha C_1/2-C_2>0. For all sufficiently
large m, the bracket in (21) is positive whenever
delta_m>=d_alpha+A_alpha/m, even if delta_m is arbitrarily large.
The small O(m^-2) contribution at the lower endpoint can be absorbed by
choosing the strict constant margin larger. Thus c>0 gives strictly negative
profit, contradicting potential maximality.

If c=0, (11) gives T=0 and kappa=t. The entire raw spectrum lies in [1,q].
Equation (7), including its strict equality classification, proves exactly
(3)-(4). Conversely every matrix (4) with a winning k is actual APPT and
attains G. This establishes the full finite equality statement for all
larger n, with no exception for integer rank ties.

## 8. A matching actual lower within an O(m) onset band

Pick a single sign and an interior parameter attaining d_alpha in (2).
Its single-pattern cost c_* is c_+(p_*) or c_-(beta_*), is positive and
finite, and its gain satisfies

    H_*=alpha d_alpha c_*/2.                            (22)

For a positive head there is only one edge pattern up to relabeling. For a
negative head there are two patterns: a diagonal and an edge; its maximum
cost is the diagonal c_-(beta_*). Keep the parameter fixed and choose

    c_m=c_*+B_*/m, kappa=t-c_m/m^2,                     (23)

with a fixed sufficiently large positive B_*. For either pattern, the
exact right side of (16), computed on its fixed finite support and isolated
remaining vertices, equals its limiting cost plus O(1/m), uniformly for
bounded c_m. First use the fixed budget interval [c_*,c_*+1] to bound these
errors, choose B_* greater than those constants, and then take m>=B_*.
This avoids any dependence of the chosen error bound on B_* itself.
Then (16) holds for EVERY pattern at large m. The matrix test is sufficient
for all global unitaries in this finite-head construction, by the original
spectral rearrangement argument in reviewed cubic Section 7.

Use raw values 1+kappa+p_* for a positive head, or 1-beta_* for a negative
head; all other values are endpoints 1 or 1+kappa. Choose the total upper
rank to be an EXACT maximizing integer for G_alpha(kappa,D), and normalize
by the actual trace. For n/m^2 in a compact positive neighborhood of d_alpha,
the upper rank exceeds R and the lower rank exceeds K eventually, so (10)
has precisely the intended head. The clipped state attains G_alpha(kappa,D)
EXACTLY, without a rounding remainder. This is a genuine all-unitary APPT
state at every sufficiently large dimension pair considered below.

The two-sided version of (8)-(9) and the relative identity (13) give for
this actual state, uniformly on that compact neighborhood,

    D[e_alpha(rho)-G_alpha(t,D)]
                     =H_*-alpha delta_m c_m/2+O_alpha(1/m).       (24)

Let n=floor(d_alpha m^2-A_* m), with A_*>0 sufficiently large. Then
delta_m=d_alpha-A_*/m+O(m^-2). Using (22)-(23), the right side of (24) is

    [alpha c_* A_*/2-alpha d_alpha B_*/2+O_alpha(1)]/m,

which is strictly positive when A_* exceeds the fixed error bound and
the displayed protection penalty. Obtain that error bound first on the
fixed interval delta_m in [d_alpha/2,3d_alpha/2]; after choosing A_* take
m large enough to be in this interval. Thus for every large m an actual state
beats bulk at this n. It follows that N_alpha(m)>n, yielding the lower
bound in (5). The upper from (3) gives the other bound.

For existence of N_alpha(m) at every fixed m>=3, use the already complete
fixed-m eventual all-order theorem: its lower hole/bulk crossing tends to
zero, its upper bulk/pole crossing tends to infinity, so each FIXED finite
positive alpha is eventually in bulk. This credited input is not a new
fixed-m result. Equation (5) and all statements E0-E4 now follow.

## 9. Scope and separation from previous results

The reviewed C0-C4 variational paper gave a zero LIMITING correction above
d_alpha. That alone could not exclude tiny actual profitable anomalies or
classify exact finite equality matrices. The present new relative proof
does both, for ALL larger n, and supplies the O(m) onset band.
It retains exact integer ranks and actual trace normalization throughout.
At alpha2 minimizing Renyi entropy is precisely maximizing purity, so the
onset m^2/4+O(m) and equality matrices transfer without a new quantum model.
No constant-order universality for growing alpha, every finite dimension,
exact finite minimum onset, next-order onset coefficient, or ASEP bulk
classification is implied. Old manuscripts and their audits are unchanged.
This draft remains unpromoted until an independent full proof review.
