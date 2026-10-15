# Optimal entropy order for the earliest final APPT bulk onset

Yongxian Zhang (张永贤), South China University of Technology.
15 October 2026, Asia/Shanghai. Complete ordinary written proof. A separate
independent AI-agent read covers all L0-L2 on the bound mathematical source.
L_REVIEW.md/json and FINAL_STATUS_BINDING.json bind the read and status edits.
No new Lean or old audit expansion.

## 1. Original domain and full variational statement

APPT(m,n) consists of the actual complex positive semidefinite trace-one
matrices on C^m tensor C^n which remain PPT after EVERY global unitary.
Let D=mn, E_alpha=max_APPT(log D-S_alpha), and G_alpha(m,D) be the exact
integer-rank q_m projection bulk, q_m=1+2/(m-1). At alpha=1 use von Neumann.
For every m and alpha>0 define the extended integer-valued final onset

    N_alpha(m)=min{N>=m integer: E_alpha(m,n)=G_alpha(m,mn)
                                      for EVERY integer n>=N},       (1)

with value +infinity when this set is empty. An order is held fixed while
n ranges over all those larger integers. Let alpha_0,d_0,z_+,z_-,A_s,
sigma_s be the exact constants of the reviewed J/K results, so

    sigma_+>0>sigma_-,
    u_c=(A_--A_+)/(sigma_+-sigma_-),
    a_c=A_++sigma_+u_c=A_-+sigma_-u_c.                      (2)

Fix ANY compact interval I=[ell,r] with 0<ell<alpha_0<r<infinity. Put
M_I(m)=min_(alpha in I) N_alpha(m). For sufficiently large m:

**L0.** A single constant C_I gives, for EVERY alpha in I,

    N_alpha(m)>=d_alpha m^2-C_I m.                         (3)

This includes any orders depending on m inside I and any infinite N.

**L1.** M_I(m) is finite and attained; its minimizing set is nonempty
and closed in I.

**L2.** The actual integer minimum and EVERY minimizing order satisfy

    M_I(m)=d_0 m^2+a_c m+O_I(1),
    alpha=alpha_0+u_c/m+O_I(m^-2).                         (4)

For every fixed B>=0, the second conclusion holds with O_(I,B)(m^-2)
for EVERY alpha in I with N_alpha(m)<=M_I(m)+B. No uniqueness of a finite
minimizing order is asserted. The exact integer threshold, not a continuous
crossing or a surrogate subset optimum, is being minimized.

## 2. A uniform actual-state lower barrier on an arbitrary compact order interval

We need only a LOWER barrier outside K's coupled band, not a uniform
classification of all actual optimizers for arbitrary alpha in I.
J proves that each sign's full leading critical ratio has a unique interior
nondegenerate maximum z_s(alpha), analytic in alpha. Hence these parameters
range over a compact subset of (0,infinity) on I. The exact same is true
of all their limiting positive/negative head masses, with negative mass
bounded strictly below one. The analytic values D_s(alpha)>0 are bounded
above and away from zero; d_alpha=max(D_+,D_-) has these bounds too.

Use I's (the crossing-envelope paper's) exact normalized real-rank family
identity, for either sign and parameters in the preceding compact set:

    f_s^real=B_alpha(kappa)-log(1-g_s/D),
    kappa=2/(m-1+z), t=2/(m-1),
    nu_s,m(alpha,z)=g_s/[m(1-exp(B_alpha(kappa)-B_alpha(t)))].  (5)

For clarity, the removable singularities can be canceled explicitly.
Let psi_alpha(y)=[y^alpha-1-alpha(y-1)]/(alpha-1), continued at alpha=1
as y log y-y+1. Put w=psi_alpha(1+kappa)/kappa,
v=(alpha-1)w/alpha, and ell(v)=log(1+v)/v with ell(0)=1. For signed h
and base b=1+kappa (positive head) or b=1 (negative head), put
DeltaPsi=psi_alpha(b+h)-psi_alpha(b). Direct algebra gives

    B_alpha(kappa)=w*ell(v)-log(1+w),
    g_s=(DeltaPsi-h*w)/(1+w).                              (5a)

These identities follow from Q=alpha*kappa+(alpha-1)psi_alpha(1+kappa).
All bases at the retained head are uniformly positive. psi has a second
order zero at y=1, so w is jointly analytic even at kappa=0; (5a) removes
alpha=1 entirely. All denominators are protected on the compact set for
small kappa. Thus the defining functions are jointly analytic near the
compact order/parameter set, including alpha=1. This explicit algebra
was supplied during independent review and is credited in REVIEW_HISTORY.md.
Taylor's theorem therefore gives one uniform remainder in

    nu_s,m(alpha,z_s(alpha))
       =D_s(alpha)m^2+a_s(alpha,z_s(alpha))m+O_I(1).         (6)

The two coefficient functions in (6) are bounded on I. This is a common
estimate from the explicit analytic identity, not a maximum of unknown
pointwise theorem cutoffs. The same compact expansions prove uniformly
g_s=alpha*z_s*D_s+O_I(1/m)>c_I>0, and for n comparable to m^2,

    partial_n[f_s^real-B_alpha(t)]
       =-g_s/[m n^2(1-g_s/(mn))],                         (7)

whose absolute value lies between positive constants times m^-5.

For each alpha choose either sign s attaining d_alpha. Choose one fixed
large B_0 so B_0+a_s(alpha,z_s(alpha))>=2 for both signs and every alpha
in I. Set n=floor(d_alpha*m^2-B_0*m). It is >=m for large common m.
Equations (6)-(7), and the exact real crossing at nu_s,m, imply

    f_s^real(m,n,z_s(alpha))-B_alpha(t)>=c_I*m^-4.          (8)

The continuous-rank maximizer is 1/2+O_I(1/m) as a fraction of D, so its
two adjacent integer ranks lie in the physical interval
[m(m-1)/2,D-m(m+1)/2]. Rounding to the better of these integers loses
at most C_I*kappa^2/D^2=O_I(m^-8). The bulk integer maximum is <=B_alpha(t).
Every rounded state used here is actual all-unitary APPT by the physical
boundary-family proof, independently of entropy order. Thus (8) produces
an ACTUAL state strictly beating the exact integer bulk at this n.
Failure of bulk equality at n forces N_alpha(m)>n under the full FINAL
definition (1), even when equality may hold at some earlier dimensions.
Since n+1>d_alpha*m^2-B_0*m, this proves (3) with one constant on I.
If N is infinite the same lower barrier is automatic. This proves L0.

## 3. Closed sublevel sets and actual attainment

For fixed m,n the actual APPT set is nonempty and compact: it is the
trace-one PSD compact set intersected with all global-unitary PPT closed
conditions. Entropy deficit is jointly continuous in the order alpha>0
and the density matrix, including singular matrices and alpha=1. Indeed
finite spectral power sums are continuous uniformly on compact positive
order intervals, x^alpha log x extends continuously at x=0 uniformly
away from alpha=0, and the alpha=1 logarithmic quotient has its usual
continuous continuation. Maximum over this fixed compact feasible set
is therefore continuous in alpha. G_alpha is a finite maximum of
continuous projection-vertex values and is continuous as well.

For every integer N>=m the final-onset sublevel set is exactly

    {alpha in I: N_alpha(m)<=N}
      =intersection_(integer n>=N){alpha in I: E_alpha(m,n)=G_alpha(m,mn)}.

It is closed, even though the intersection is infinite. K3 at the single
order alpha=alpha_0+u_c/m supplies, for all large m, a finite upper bound

    N_(alpha_0+u_c/m)(m)<=d_0*m^2+a_c*m+C,                  (9)

and that order lies in the interior of I. Hence the nonempty set of finite
integer values taken by N on I has a least member, which is attained by
definition of that value set. Its minimizing set is the corresponding
closed sublevel set (there is no smaller value). This proves L1 while
retaining the all-larger-n quantifier and allowing other orders to have
infinite onset. No compact-uniform upper theorem for every order was needed.

## 4. Localization of EVERY minimizing and bounded-gap order

J's strict order derivatives give a common slope barrier on I:

    d_alpha>=d_0+c_I*abs(alpha-alpha_0), c_I>0.             (10)

To justify the common constant, on the left of alpha_0 use d_alpha=D_-
and the positive minimum of -D_-' on the compact left subinterval; on
the right use D_+ and the positive minimum of D_+'. Integrate these
derivative bounds. The derivative values are continuous and strictly
signed on the full fixed compact subintervals.

Fix B>=0 and take ANY alpha with N_alpha(m)<=M_I(m)+B. The upper candidate
(9), the lower barrier (3), and (10) imply

    c_I*m^2*abs(alpha-alpha_0)
       <=(C_I+abs(a_c))*m+C+B.

Thus |alpha-alpha_0|<=U_(I,B)/m with one U_(I,B). This is the necessary
first localization; it was not assumed from the limiting cusp. Put
u=m(alpha-alpha_0). K3 now applies UNIFORMLY to all these orders and gives

    N_alpha(m)=d_0*m^2+m*V(u)+O_(I,B)(1),
    V(u)=max{A_++sigma_+u,A_-+sigma_-u}.                   (11)

The two lines have opposite strictly signed slopes, meet only at u_c,
and there equal a_c. Consequently, for all real u,

    V(u)-a_c>=min(sigma_+,-sigma_-)*abs(u-u_c).            (12)

For an actual minimizer, (9), (11) and (12) show both
M_I=d_0*m^2+a_c*m+O_I(1) and |u-u_c|<=C_I/m. For a bounded-gap order,
the same comparison includes the additional fixed B and yields
|u-u_c|<=C_(I,B)/m. Dividing by m proves all of (4) and its bounded-gap
extension. Every minimizing/near-minimizing order was arbitrary; no
subsequence, chosen differentiable branch or unique finite minimizer
was imposed. Integer threshold ties remain fully allowed.

## 5. Precise scope

This is minimization over ANY preassigned FIXED compact positive-order
interval containing alpha_0 in its interior. It is NOT a minimization
over all alpha>0, nor a theorem for growing intervals or orders tending
to zero/infinity. Its constants and sufficiently large dimension are
non-effective. It does not claim an exact finite M_I, exact minimizing
set or unique minimizing order. The original feasible set and actual
integer ranks are used in both the lower barrier and final-onset theorem.

Inputs are the independently read J critical-point theorem, I normalized
crossing identity and actual boundary families, and K0-K3's moving-order
uniform FINAL onset. This new optimization target passed a separate source-bound independent
ordinary read of all L0-L2; earlier PASS records did not automatically
certify it. The completed report retains its actual scope and history.
The bounded primary-source screen of the existing APPT critical-window
line supplies context, not an exhaustive search or priority claim.

No new major-conjecture count, formal proof, old audit expansion,
external human peer review, submission, email, Release or DOI.
Yongxian Zhang, SCUT; no external funding; OpenAI AI assistants assisted.
Original material all rights reserved; third-party notices retained.
