# The coupled entropy-order and dimension transition for actual APPT states

Yongxian Zhang (张永贤), South China University of Technology.
15 October 2026, Asia/Shanghai. Complete author manuscript, independent
ordinary review pending. This new moving-order target is not certified
automatically by the separately reviewed fixed-order H/I/J manuscripts.

## 1. Complete original-domain statement

APPT(m,n) denotes the ORIGINAL complex positive semidefinite trace-one
matrices on C^m tensor C^n remaining PPT after EVERY global unitary.
Put D=mn, E_alpha=max_APPT(log D-S_alpha), with von Neumann at alpha=1,
and G_alpha(m,D) the exact integer-rank q_m projection bulk, q_m=1+2/(m-1).
N_alpha(m) is the minimal integer N>=m such that E_alpha(m,n)=G_alpha(m,mn)
for EVERY integer n>=N. For a given m, the alpha in this definition is
held fixed while n ranges over all larger integers.

Let alpha_0 be J's unique positive/negative critical crossing, d_0 its
common critical value, and z_+,z_- its two unique nondegenerate critical
parameters. The proven bounds 1/2<alpha_0<1 allow a compact neighborhood
J of alpha_0 contained in (0,1). I defines the two analytic linear
coefficient functions a_s(alpha,z), s in {+,-}. Write

    A_s=a_s(alpha_0,z_s), sigma_s=D'_s(alpha_0),
    sigma_+>0, sigma_-<0,
    L_s(u,a)=alpha_0 z_s(A_s+sigma_s u-a).                    (1)

These are exact definitions by the reviewed scalar formulas, not numerical
approximations to alpha_0. Take any fixed U,A>0 and all integer m<=n and
real u satisfying

    |u|<=U, alpha=alpha_0+u/m,
    a=(n-d_0 m^2)/m, |a|<=A.                               (2)

**K0.** For all sufficiently large m, UNIFORMLY in (2), every actual
optimizer is integer bulk or exactly one positive/negative boundary
anomaly, with no other anomaly mass, exact protection equality, endpoint
body and a truly winning adjacent integer rank. All matrix, sign,
parameter and integer ties remain. A fixed compact z interval covering
both critical parameters suffices for the complete exact scalar formula.

**K1.** On the original feasible set the uniform value law is

    m D [E_alpha(m,n)-G_alpha(m,D)]
               =max{0,L_+(u,a),L_-(u,a)}+O_(U,A)(1/m).       (3)

**K2.** Every nonbulk optimizing anomaly of sign s has

    |z-z_s|<=C_(U,A)/m.                                    (4)

If one of the three expressions in (3) exceeds the other two by a fixed
positive gap, then every actual optimizer belongs to that family eventually,
uniformly under that gap condition. This is no guess about an exact finite
winner where limiting expressions tie or their gaps vanish.

**K3.** The minimal FINAL onset for the same moving order satisfies,
uniformly for |u|<=U,

    N_(alpha_0+u/m)(m)
       =d_0 m^2+max{A_++sigma_+u,A_-+sigma_-u}m+O_U(1).      (5)

It also has a two-ceiling enclosure with real center uncertainty O_U(m^-3)
using the exact compact crossing envelope defined in Section 5. The two
integer ceilings can differ; no unconditional single-ceiling formula is
asserted. The affine onset frontier has a unique intersection at
u_c=(A_--A_+)/(sigma_+-sigma_-). No exact algebraic value or unproved sign
of u_c is needed. Formula (3) is an actual entropy transition law, not a
calculation on a substituted restricted quantum feasible set.

## 2. Uniform physical coercivity and moving-kernel critical localization

We prove the needed uniformity rather than substituting a moving alpha
into the fixed-alpha H theorem. All physical coordinates below are the
same as C/E/H: R=m(m-1)/2, K=m(m+1)/2, b=lambda_(D-K+1)>0,
x=lambda/b, kappa=x_R-1, c=m^2(t-kappa), t=2/(m-1), and full anomaly
lists p_i=x_i-1-kappa at the top R and beta_j=1-x_(D+1-j) at the bottom K.
Let T=sum p+sum beta and y=clip(x,[1,1+kappa]). Exact physical bounds are

    0<=kappa<=t, T<=c/2, T<=m,
    sum p_i^2+sum beta_j^2<=34, 0<=x_i<=3.                   (6)

Choose the compact order neighborhood J inside (0,1), bounded away from
both zero and one. Every kernel bound in E's relative comparison is then
uniform on J: the quotients psi_alpha(1+p)/p^2 and
psi_alpha(1-beta)/beta^2 extend continuously, including p=0 and beta=0,1.
For positive-base derivatives the arguments stay in [1,3]. Hence the
exact subtract-before-expand proof gives

    |D[e_alpha(x/Tr x)-e_alpha(y/Tr y)]-H_alpha|
                            <=C_J(kappa T+T^2/D),
    H_alpha=sum psi_alpha(1+p)+sum psi_alpha(1-beta),         (7)

with one C_J. The interval-rank derivative has uniform leading term
alpha kappa/4 and a uniform smaller remainder, since the real winning
fraction is 1/2+O_J(kappa) and the actual rank is adjacent to it. The same
E coercivity proof therefore bounds c uniformly for every potentially
profitable actual state when D/m^3>=d_0/2. This proof uses alpha>=min J>0,
the uniform kernel bound in (6), and the global interval derivative lower;
it does not assume a uniform cutoff from a pointwise theorem.

For bounded c, (7) and the integrated interval derivative give uniformly

    D[e_alpha(rho)-G_alpha(m,D)]
                 <=C_J c^2-alpha(D/m^3)c/2+C_J c/m.          (8)

Thus there is a fixed c_small>0 excluding every profitable state with
0<c<=c_small. The error is proportional to c, even for arbitrarily tiny c.

For any sequence of potentially profitable nonbulk states in (2), alpha
tends to alpha_0 and D/m^3 tends to d_0. The bounded-c resolvent gap keeps
the largest negative anomaly away from one, independently of alpha.
The exact cubic decomposition, with constants uniform on J, is

    D[e_alpha(rho)-G_alpha(m,D)]
       =H_alpha-alpha(D/m^3)c/2-J_alpha+o(1),
    J_alpha=D[B_alpha(kappa)-e_alpha(y/Tr y)]>=0.             (9)

The finite-prefix inverse-walk and tail-mass bounds are physical and
independent of entropy order. For every fixed prefix, bounded costs stay
away from their inverse singularities. Every kernel gain after rank L
is bounded by C/(L+1), uniformly on J. At the limiting alpha_0,d_0,
prefix gains are at most alpha_0 d_0/2 times their full graph costs;
the exact first omitted walk charges an additional 2*T_tail to c.
Consequently, along any bounded-c subsequence, (9) implies

    0<=limsup profit <=C/(L+1)
                        -alpha_0 d_0 liminf T_tail-liminf J_alpha.

The gain kernels converge on each prefix as alpha->alpha_0; their uniform
quadratic bound controls every omitted gain. Letting L increase forces
uniform vanishing tail mass and J_alpha->0. The resulting l1-convergent
subsequences have limiting gain-cost value zero and full graph cost at
most their budget. C2 at alpha_0,d_0 therefore identifies every limit:
empty/c=0, or exactly the positive z_+, or exactly the negative z_-.
The empty case is excluded by (8) at positive c. The strict interaction
cost in C2 excludes every two-anomaly limit, even one from each sign.

Sequential contradiction makes this localization uniform over (2).
This argument is the moving-kernel version of C4's proof; it does not
assert the fixed-alpha C4 theorem for an unproved varying-order regime.
From J_alpha->0 and the uniform body expansions

    B_alpha(kappa)=alpha kappa^2/8+O_J(kappa^3),
    e_alpha(y/Tr y)=alpha kappa^2 Var(theta)/2+O_J(kappa^3),
    theta_i=(y_i-1)/kappa,

we obtain Var(theta)->1/4 uniformly, since D*kappa^2~4d_0 m diverges.

## 3. Uniform exact finite tail removal and every equality

The retained mass is now uniformly near one of two interior critical
masses, so all root denominators stay protected. For either retained
sign, the physical inverse-walk identity gives EXACTLY

    c>=C_s(kappa,retained)+g(kappa)tau,
    g(kappa)=2kappa m^2/[(m-1)(2+kappa)],
    C_+=2kappa m^2 p/[(m-1)(2+kappa-p)],
    C_-=2kappa m^2 beta/[(m-1)(2+kappa-2beta)],               (10)

where tau is ALL omitted anomaly mass. The unique root c_0 and contrast
kappa_0=t-c_0/m^2 obey c>=c_0 and c-c_0>=1.6tau eventually, without
additive error. This is physical algebra independent of entropy order.
The retained positive edge or negative diagonal/edge patterns yield
actual APPT at kappa_0 for EVERY unchanged clipped middle body, including
the exact PSD boundary; H's rearrangement/rank-one proof is unchanged.

All changed coordinates exclude the retained head and have bases one or
1+kappa. The same exact power/trace subtraction as H, on compact J,
gives an error bound [C_J eta+C_J(kappa+1/D+tau/D)]tau after removal,
where all omitted anomalies are eventually <=eta. Holding the same body
and retained mass, the contrast derivative is

    partial_r e_alpha=alpha r Var(theta)+O_J(r^2+1/D).

The uniform variance conclusion above and min J>0 make its integrated
gain at least g_0(c-c_0) for a fixed g_0>0. First choose eta small and
then m large; removal loss is <=g_0 tau/2. Every tau>0, or tau=0,c>c_0,
has a strictly better ACTUAL comparator. Thus every nonbulk optimizer
has exactly zero tail mass and exact protection equality.

Trace-weighted convex decomposition of the middle raw cube and strict
power concavity for alpha in J give the endpoint body and all integer
rank equalities. Distinct normalized vertices share a fixed positive
coordinate. The real rank formula has k_star/D=1/2+O_J(1/m), so its
two adjacent integers are physical. Every family member is actual APPT.
Choose I_0=[min(z_+,z_-)/2,2max(z_+,z_-)]; all actual optimizing boundary
z lie there eventually by uniform localization. The exact actual formula
is therefore integer bulk or the maximum of the two full families on
I_0, including all parameter/rank/sign ties and all unitary orbits.
This proves K0, with the required moving-order uniformity.

## 4. Uniform entropy law and all optimizing anomaly parameters

I's exact normalized real-rank identity applies algebraically to every
alpha in J and z in I_0:

    f_s^real=B_alpha(r)-log(1-g_s(alpha,r,z)/D),
    r=2/(m-1+z),
    nu_s,m(alpha,z)=g_s/{m[1-exp(B_alpha(r)-B_alpha(t))]}.      (11)

All these functions are jointly analytic near the compact order/parameter
set after the displayed removable small-r factors are canceled. In
particular I's scalar expansion and its z derivatives are uniform:

    nu_s,m(alpha,z)=m^2 d_s(alpha,z)+m a_s(alpha,z)+O_J(1).

Set epsilon=1/m, alpha=alpha_0+u epsilon, D=(d_0+a epsilon)/epsilon^3,
t=2epsilon/(1-epsilon), r=2epsilon/[1+(z-1)epsilon]. Multiplying the
exact difference in (11) by D cancels the leading negative powers of
epsilon: B_alpha(r)-B_alpha(t)=O(epsilon^3) and g_s/D=O(epsilon^3).
Taylor expansion is therefore uniform, together with two z derivatives,
and has the form

    m D[f_s^real-B_alpha(t)]
                  =m Q_s(z)+R_s(u,a,z)+O_(U,A)(1/m),
    Q_s(z)=alpha_0 z[d_s(alpha_0,z)-d_0].                    (12)

Q_s<=0 has its unique zero at z_s. Its second derivative there is
alpha_0 z_s partial_z^2 d_s(alpha_0,z_s)<0 by J. Outside a fixed small
neighborhood of z_s, compactness gives a strict negative gap. In that
neighborhood R_s is uniformly Lipschitz, so maximization can improve
R_s(u,a,z_s) by at most max_v[-c m v^2+C v]=O(1/m).

To evaluate this coefficient, at z_s the crossing expansion in (11) is

    nu_s,m(alpha,z_s)
          =d_0 m^2+[A_s+sigma_s u]m+O_U(1),

where the anomaly derivative of d_s vanishes, so its alpha derivative
is D'_s(alpha_0). The exact n derivative of f_s^real-B_alpha(t) is
-g_s/[m n^2(1-g_s/(mn))]. At the critical point g_s tends to
psi_alpha0(head_s)=alpha_0 z_s d_0. The mean-value comparison at its
crossing consequently yields

    R_s(u,a,z_s)=alpha_0 z_s[A_s+sigma_s u-a]=L_s(u,a).       (13)

Head and bulk integer losses are O_J(r^2/D^2)=O(m^-8), which become
O(m^-4) after multiplying by mD. Thus they are smaller than the O(1/m)
remainder in (12). The exact feasible-set formula from K0 and compact
scalar maximization now prove the full value formula (3), not just its
values on prescribed test states.

For parameter localization, the continuous family score in (12) has
strictly negative second derivative of size m near z_s, and its derivative
there is m Q'_s+O(1). Its unique maximum is therefore z_s+O(1/m),
uniformly. Its discrete-family maximum differs uniformly in score by
O(m^-4). Every discrete winning z of that family lies within O(m^-5/2)
of its continuous maximum by the quadratic loss. This proves (4) for
EVERY actual nonbulk optimizer. A fixed positive gap between the three
limiting expressions dominates the uniform error and excludes all other
families eventually, proving the remaining K2 statement. Genuine gapless
regions retain the exact K0 comparison; no finite winner is declared there.

## 5. The uniform minimal FINAL onset

The all-larger-n E0 estimate also has a uniform neighborhood version,
which we justify explicitly. The relative power/trace estimate (7),
coercivity and integrated body derivative were already made uniform on J.
The disjoint-prefix inverse-walk proof of E's full head bound is physical;
its entropy constants are uniform kernel quadratic bounds on J. It gives

    H_alpha<=alpha d_alpha c/2+C_J c/m

uniformly at bounded c, including all omitted mass. Combining with the
relative body penalty, exactly as E's proof does, supplies constants A_J,M_J
such that all alpha in J and all m>=M_J have actual bulk equality for
EVERY n>=d_alpha m^2+A_J m. In the resulting coefficient of c the term
proportional to D/m^3 is kept rather than bounded by a constant, so this
holds even when n/m^2 is unbounded. No pointwise dependence M_alpha was
silently maximized over an arbitrary collection of cutoffs.

On the coupled neighborhood, define the exact envelope

    nu_m^*(u)=max_(s in {+,-},z in I_0) nu_s,m(alpha_0+u/m,z).

The uniform scalar expansion is

    nu_s,m=m^2 d_s(alpha_0,z)
          +m[a_s(alpha_0,z)+u partial_alpha d_s(alpha_0,z)]+O_U(1).

Each sign has a unique nondegenerate leading maximum z_s. Its quadratic
leading loss and uniformly Lipschitz next coefficient imply

    nu_m^*(u)=d_0 m^2
                  +max{A_++sigma_+u,A_-+sigma_-u}m+O_U(1).   (14)

This holds even if the two next coefficients are equal. The real-rank
integer errors and the n derivative in (11) have uniform constants of
orders m^-8 and m^-5. K0 throughout a fixed sufficiently wide linear
window and the uniform E estimate for all still larger n give exactly

    ceil(nu_m^*(u)-C_U m^-3)<=N_(alpha_0+u/m)(m)
                           <=ceil(nu_m^*(u)+C_U m^-3).       (15)

For the lower, at ceil(nu_m^*(u)-C_U m^-3)-1 use a parameter attaining
the full envelope and its actual adjacent integer rank. For the upper,
control every family throughout the window and then all still larger n.
The strict constant margin absorbs the TWO rounding losses. Each ceiling
differs from the real center by at most 1+C_U m^-3, so (14) proves (5)
with the original all-larger-n definition. This completes K3.

## 6. Inputs and limitations

The C0-C4, E0-E4 and H/I/J sources remain unchanged. Their physical
inequalities, fixed-order theorems and review scopes are credited inputs;
Sections 2-3 and 5 supply the extra uniformity needed for this NEW coupled
regime. The bounded prior APPT/Renyi critical-window source screens are
not an exhaustive prior-work or priority certificate.

Only |u|<=U and a fixed linear dimension window are covered. There is no
arbitrary moving-order theorem, effective dimension cutoff, exact finite
transition count, universal single-ceiling formula, ASEP bulk claim or
Lean theorem. All true sign/rank/parameter ties are kept by the exact
formula, and the limiting three-expression law does not choose finite
winners where its gaps vanish. Finite controls support the analytic
proof, not a full numerical enumeration of the quantum feasible set.
Independent ordinary review of this K manuscript is pending.

Yongxian Zhang, SCUT; no external funding; OpenAI AI assistants assisted.
Original material all rights reserved, third-party notices retained.
No new major-conjecture count, external submission, email, Release or DOI.
