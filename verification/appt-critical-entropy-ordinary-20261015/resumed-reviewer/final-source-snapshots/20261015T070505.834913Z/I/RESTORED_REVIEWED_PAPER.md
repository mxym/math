# Exact critical crossing envelopes and the linear APPT entropy onset

Yongxian Zhang (张永贤), South China University of Technology.
15 October 2026, Asia/Shanghai. Complete author manuscript, independent
ordinary review pending, including the new H0-H5 dependency. No new Lean.

## 1. Original object and complete target

For the ORIGINAL complex density matrices on C^m tensor C^n which remain
PPT after EVERY global unitary, write D=mn and

    E_alpha(m,n)=max_APPT [log D-S_alpha(rho)],
    t=2/(m-1),
    G_alpha(m,D)=max_(integer k) e_alpha((I+t Pi_k)/(D+t k)),
    N_alpha(m)=min{integer N>=m: E_alpha(m,n)=G_alpha(m,mn)
                                             for EVERY integer n>=N}.

Each alpha is FIXED, finite, and positive before taking m to infinity.
Alpha=1 means von Neumann entropy. Existence of N at fixed m>=3 is the
credited fixed-m eventual theorem; the all-larger-n E0 theorem supplies
N=d_alpha m^2+O_alpha(m). The H0-H4 manuscript supplies the complete actual
optimizer classification in every fixed linear critical window. These
are input theorems, not replaced here by calculations on chosen families.

Use its explicit critical constant d_alpha, positive and negative critical
sets P_alpha,B_alpha, and compact interval I_alpha defined from all their
z values. Namely

    psi_alpha(y)=[y^alpha-1-alpha(y-1)]/(alpha-1),
    psi_1(y)=y log y-y+1,
    d_alpha=max{max_(0<p<2) (2-p)psi_alpha(1+p)/(2alpha p),
                max_(0<beta<1) (1-beta)psi_alpha(1-beta)/(alpha beta)},
    z_+(p)=2p/(2-p), z_-(beta)=beta/(1-beta),
    I_alpha=[min(critical z)/2,2 max(critical z)].               (1)

All these critical values are interior; both signs are retained. For
z in I_alpha put

    r=2/(m-1+z), q=1+r,
    p=(2+r)z/(z+2), beta=(2+r)z/[2(1+z)].                     (2)

The raw positive family is I+r Pi+p vv*, v in ran Pi; the negative
family is I+r Pi-beta vv*, v in ker Pi. Each is actual all-unitary APPT
at the exact boundary, with physical integer rank R<=k<=D-K,
R=m(m-1)/2, K=m(m+1)/2. Their traces are D+r k+p and D+r k-beta.
These physical sufficiency/equality facts come from H0-H4.

Let B_alpha(r) be the real-rank body deficit maximum at contrast r.
For each sign define g_s(r,z) by (5)-(6) below and

    nu_s,m(z)=g_s(r,z)/{m[1-exp(B_alpha(r)-B_alpha(t))]},
    nu_alpha,m^*=max_(s in {+,-}, z in I_alpha) nu_s,m(z).      (3)

This uses only a compact scalar optimization and elementary powers/logs.
It contains no remaining optimization over quantum matrices.

**I0-I3.** For every fixed finite alpha>0 there are C_alpha,M_alpha such
that for every integer m>=M_alpha,

    ceil(nu_alpha,m^*-C_alpha m^-3)<=N_alpha(m)
                              <=ceil(nu_alpha,m^*+C_alpha m^-3).  (4)

An explicit coefficient a_alpha given in (15) satisfies

    N_alpha(m)=d_alpha m^2+a_alpha m+o_alpha(m).

All critical sign/parameter ties are included in a_alpha. No uniqueness
or nondegeneracy is assumed. The two ceilings in (4) need not coincide;
no separation of their center from the integer lattice is proved. No
effective M_alpha or all-finite-dimensional formula is asserted.

## 2. Exact trace at the real-rank optimum, including alpha=1

Fix sign and z, and regard the upper rank k as real temporarily. Write
h=p for the positive family and h=-beta for the negative family. At
alpha!=1 set

    Q=q^alpha-1,
    H_+=(q+p)^alpha-q^alpha, H_-=(1-beta)^alpha-1,
    A=D+Q k+H_s, S=D+r k+h.

The exact raw-to-normalized deficit is
f=[log(A/D)-alpha log(S/D)]/(alpha-1). Stationarity gives Q S=alpha r A,
and the unique real maximizer is

    k_s^*=[Q(D+h)-alpha r(D+H_s)]/[(alpha-1)r Q].

Consequently

    S_*=s_alpha(r)D+u_s,
    s_alpha(r)=alpha(Q-r)/[(alpha-1)Q],
    u_s=alpha(Qh-rH_s)/[(alpha-1)Q],
    g_s(r,z)=-u_s/s_alpha(r)=(r H_s-Qh)/(Q-r),
    f_s^real=B_alpha(r)-log(1-g_s(r,z)/D),
    B_alpha(r)=log(Q/(alpha r))/(alpha-1)-log s_alpha(r).      (5)

Here Q-r is nonzero for fixed alpha!=1 and small r: it has the sign of
alpha-1. The quantity s_alpha is positive, near one. The formula for
B follows by putting h=H_s=0 in the SAME stationary formula. Thus no
body approximation or missing normalization occurs in (5).

At alpha=1 put L=q log q and

    H_+=(q+p)log(q+p)-q log q,
    H_-=(1-beta)log(1-beta),
    k_s^*=[(L-r)(D+h)-r H_s]/r^2.

The exact trace and real optimum are

    S_*=(L/r)D+(L/r)h-H_s,
    s_1(r)=L/r, g_s(r,z)=r H_s/L-h,
    f_s^real=B_1(r)-log(1-g_s(r,z)/D),
    B_1(r)=L/r-1-log(L/r).                                  (6)

Indeed stationarity says r(sum x_i log x_i)=(L-r)S; substitution into
the exact von Neumann deficit proves (6). This avoids any division
by alpha-1 at alpha=1. The limits in (5) agree with (6), but continuity
alone is not substituted for its direct calculation.

In (5) the multiplicative constant inside the logarithm is Q/(alpha r),
since stationarity is Q S=alpha r A. Reversing this ratio would leave
a large spurious constant and fails the head-free body check.

## 3. The whole compact crossing and actual integer onset

The physical masses in (2) stay in compact interior intervals uniformly
on I_alpha for all large m. From (5)-(6), or the expansion in Section 4,
g_s(r,z) tends uniformly to the positive psi_alpha(1+p_0) or
psi_alpha(1-beta_0), respectively. Thus g_s is bounded above and bounded
away from zero. Also B'_alpha(r)=alpha r/4+O_alpha(r^2)>0 for these small
positive contrasts. Since 0<r<t, (3) is positive and continuous, and its
maximum is attained. For real n of cubic size the exact equivalence is

    f_s^real>B_alpha(t) iff n<nu_s,m(z).                     (7)

This is a real-rank comparison only; actual integer errors are treated next.
The H0-H4 real-rank formula gives k_s^*/D=1/2+O_alpha(1/m), uniformly on
I_alpha in any fixed linear window. Therefore its adjacent integers
are physical ranks R<=k<=D-K eventually. The head-free body has the same
interior property. Differentiating either rank function near its optimum
shows, uniformly,

    |partial_k^2 f_s|<=C_alpha r^2/D^2,
    0<=f_s^real-max_integer f_s<=C_alpha r^2/D^2,
    0<=B_alpha(t)-G_alpha(m,D)<=C_alpha t^2/D^2.               (8)

One can see the first estimate directly from
partial_k f_s=r Q(k_s^*-k)/(A S) for alpha!=1 and
partial_k f_s=r^2(k_s^*-k)/S^2 for alpha=1; Q=O_alpha(r)
and A,S are comparable to D. Taylor's theorem at the optimum proves
the adjacent-integer bound. Both adjacent integers are compared exactly.
On n~d_alpha m^2 these losses are O_alpha(m^-8).

The dimension derivative at fixed m,z and sign, from (5)-(6), is

    partial_n(f_s^real-B_alpha(t))
               =-g_s/[m n^2(1-g_s/(mn))].                  (9)

It lies between negative constants times m^-5 throughout the window,
uniformly on the whole compact parameter set and both signs.

The next section proves nu_alpha,m^*=d_alpha m^2+O_alpha(m). Choose a
fixed A large enough to contain its whole linear band and the upper band
in the E0 all-larger-n theorem. H0-H4 says that EVERY actual optimizer
within that window is bulk or one of these two boundary families.

Let C be larger than the integer-loss constant in (8) divided by the
derivative lower constant in (9), with a strict margin. For every integer
n>=ceil(nu_alpha,m^*+C m^-3) inside the band, all real family values are
below B_alpha(t) by more than the bulk's integer loss. Hence every actual
family value is strictly below G and the actual optimum is bulk. E0
supplies bulk for all still larger integers outside the band.

For the lower direction take n_-=ceil(nu_alpha,m^*-C m^-3)-1 and a sign
and parameter attaining nu_alpha,m^*. At this actual integer dimension
its real profit over B_alpha(t) exceeds the head's integer loss. A physical
adjacent-integer member therefore beats even the real bulk bound, and
hence the actual bulk. It follows N>n_-. This proves (4) for the original
all-larger-n definition, including possible later rank switches or ties.

Inactive critical signs can be kept in (3) harmlessly: all their members
are actual feasible states, and H0-H4 covers every actual optimizing sign.
No auxiliary family has been used as a replacement feasible set.

## 4. Uniform scalar expansion and the full linear coefficient

For fixed z define the limiting signed mass and its base derivative by

    h_+(z)=2z/(z+2), b'_+=1,
    h_-(z)=-z/(1+z), b'_-=0,
    y_s=1+h_s(z), P_s(z)=psi_alpha(y_s).

Both finite signed masses in (2) are h_s(z)(1+r/2). The positive raw
head has base 1+r, whereas the negative raw head has base 1. Write

    J_s(z)=(b'_s+h_s/2)psi'_alpha(y_s)
                              -alpha h_s/2-alpha P_s/2,
    d_s(z)=P_s/(alpha z),
    a_s(z)=2J_s/(alpha z)+3P_s/(2alpha).                    (10)

At alpha=1 use psi'_1(y)=log y; these expressions are regular because
y_s stays in a compact subset of (0,infinity). For alpha!=1 expand
Q=alpha r+alpha(alpha-1)r^2/2+O_alpha(r^3). If H_s is the raw head
power increment in (5), then

    H_s(0)=y_s^alpha-1,
    H'_s(0)=alpha[(y_s^(alpha-1)-1)b'_s
                                      +y_s^(alpha-1)h_s/2].

Substitution into the exact quotient (5) gives

    g_s(r,z)=P_s(z)+J_s(z)r+O_alpha(r^2).                   (11)

In particular J_s=(H'_s(0)-alpha^2 h_s/2)/(alpha-1)-alpha P_s/2,
which simplifies to (10). Expanding (6) directly proves the same formula
at alpha=1; it also follows from smooth integral representations of psi
near alpha=1. All errors and a fixed finite number of z derivatives are
uniform on I_alpha, since the defining functions have no singularity there.

The continuous body maximum has the universal small-contrast expansion

    B_alpha(r)=alpha r^2/8-alpha r^3/8+O_alpha(r^4).           (12)

For a direct justification its exact optimal fraction is
1/2+O_alpha(r); in the logarithmic contrast u=log(1+r), the body optimum
is invariant under u->-u by swapping the two endpoint proportions.
Its analytic expansion is therefore alpha u^2/8+O_alpha(u^4).
Since u^2=r^2-r^3+O(r^4), (12) follows. Analyticity near zero can also
be read directly from (5)-(6); their apparent removable factors have
nonzero first coefficients. Expansion through fourth order, with the
fourth-order term canceling to higher order in the contrast difference,
gives, for epsilon=1/(m-1),

    B_alpha(t)-B_alpha(r)
       =alpha z epsilon^3-alpha(3z^2/2+3z)epsilon^4
                                                       +O_alpha(epsilon^5).

Therefore

    m[1-exp(B_alpha(r)-B_alpha(t))]
       =alpha z epsilon^2[1-(3z/2+2)epsilon+O_alpha(epsilon^2)].

Using r=2epsilon+O(epsilon^2) in (11) and converting m-1 to m proves
the uniform full-family expansion

    nu_s,m(z)=d_s(z)m^2+a_s(z)m+O_alpha(1).                  (13)

The functions d_s are exactly the positive/negative critical ratios in
(1) under their respective z changes. Thus the compact critical set is

    Z_alpha={(s,z): z in I_alpha, d_s(z)=d_alpha}.             (14)

Every global critical point is in this set; none is lost by the compact
restriction. Uniform (13) first gives nu_alpha,m^*=d_alpha m^2+O_alpha(m).
It also shows that every maximizing sequence (s_m,z_m) approaches
Z_alpha in distance: a fixed positive leading gap would cost order m^2
and cannot be compensated by the bounded linear coefficient.

Set

    a_alpha=max_((s,z) in Z_alpha) a_s(z).                    (15)

Then compactness and continuity imply

    nu_alpha,m^*=d_alpha m^2+a_alpha m+o_alpha(m),
    N_alpha(m)=d_alpha m^2+a_alpha m+o_alpha(m).               (16)

For the upper, at any maximizer subtract d_alpha m^2 and divide by m
in (13). The leading difference m(d_s(z_m)-d_alpha) is nonpositive,
and every limit of a_s(z_m) is at most a_alpha. The lower is obtained
by evaluating a critical point attaining a_alpha. This proves the
claimed asymptotic without nondegeneracy or uniqueness assumptions.

If every maximizing point of d_s is isolated with strictly negative
second derivative, compactness gives quadratic leading losses around
the finite critical set. The a_s are Lipschitz there, so
-b m^2 distance^2+C m distance is O(1). The same argument upgrades
the o(m) in (16) to O(1). This last refinement is conditional on the
stated curvature condition; it is not silently used for arbitrary alpha.

## 5. Consistency cases and scope

At alpha=2, P=p^2, psi'=2p and the complete critical set is the positive
p=1,z=2. Equation (10) gives J=1 and a_2=5/4. This agrees with the
previously reviewed exact purity onset ceil((m^2+5m+7)/4). The existing
quarter-lattice theorem is an additional fact, not inferred from (4).

At alpha=1/2, the H4/H5 critical set is negative,
beta=(sqrt(5)-1)/2, z=(1+sqrt(5))/2. Equation (15) gives
a_(1/2)=(27-11sqrt(5))/2, consistent with the H5 author algebra, whose
independent ordinary review is separately pending. Its nondegenerate
critical maximum gives O(1) remainder.
This is a recovery of the half-order follow-up, not a separate result count.

The credited inputs are C0-C4 and E0-E4 in the unchanged 14 October
research packets, and H0-H4 in the 15 October critical-entropy manuscript.
Before this full follow-up, the resumed bounded primary screen searched
APPT/Renyi critical-window and bulk-threshold terms in current primary
indexes; the relevant returned item was Tran arXiv:2609.18568. Its abstract
has no matching crossing-envelope theorem. This bounded screen is not
an exhaustive literature review or historical-priority certificate.

All statements concern each fixed finite positive alpha and sufficiently
large m. They do not solve every finite dimension, yield effective
cutoffs, allow alpha to grow with m, classify ASEP bulk, prove a single
exact ceiling formula, or add a new formal theorem or audit root.
Finite symbolic/high-precision checks support the mathematical proof;
they do not exhaust the original quantum feasible set. Independent
ordinary review and its final-source binding are pending.

Personal independent research, no external funding; OpenAI AI assistants
assisted. Original material all rights reserved; third-party inputs keep
their own attribution and licensing. No submission, email, Release or DOI.
