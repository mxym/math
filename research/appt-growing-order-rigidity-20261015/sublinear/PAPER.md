# All-aspect spectral rigidity at growing sublinear APPT orders

Author: Yongxian Zhang (张永贤), South China University of Technology.
ORCID 0009-0000-3864-3536; mxymmxym1@gmail.com. 15 October 2026.
Author manuscript, pending independent ordinary review. No external funding.
OpenAI AI assistants assisted research and writing. Copyright 2026 Yongxian
Zhang; original material all rights reserved, third-party notices retained.
No new Lean coverage, priority certificate, submission, or new-major count.

## 1. Original quantum problem and the uncovered spectral range

Consider EVERY sequence of original complex PSD trace-one densities rho on
C^m tensor C^n which remain PPT after EVERY global unitary conjugation, with
integers 2<=m<=n and real orders satisfying

    m->infinity,       alpha->infinity,       alpha/m->0.           (1.1)

There is no aspect-ratio restriction. Write D=mn,gamma=n/m, sorted actual
eigenvalues lambda_i, and y_i=D lambda_i. For alpha>1 put

    M_alpha(rho)=D^-1 sum_i y_i^alpha,
    M*_alpha=max_actual_APPT M_alpha,
    e_alpha(rho)=log D-S_alpha(rho)=log M_alpha(rho)/(alpha-1),
    E_alpha=max_actual_APPT e_alpha=log M*_alpha/(alpha-1).

The eventual alpha>1 domain follows from (1.1) and is explicitly retained.
All logarithms are natural. Compactness and continuity supply the maxima.
Jensen gives M_alpha>=1. Nearoptimality below always uses the FIRST NONZERO
deficit scale; raw M_alpha/M*_alpha can be vacuous when both tend to one.

The credited G1 theorem of research/appt-growing-renyi/PAPER.md already
determines the full all-aspect value in (1.1). Its G3 spectral criterion
is restricted to bounded aspect. The credited FAST_ORDER_SPECTRA theorem
has alpha/m->infinity, while the actual-spectrum theorem S has alpha/m
tending to a positive finite constant. Fixed-m eventual exact all-order
papers do not give uniform growing-m spectral rigidity. The later global
value syntheses are explicitly credited and are not new results here.
The captured complete local read/range map is in SOURCE_INPUTS.json.

This note supplies necessary AND sufficient criteria for every actual
state sequence in (1.1), including all peak/bulk ratios and oscillations.
It is independent of the four still-being-reviewed phase-4 scalar geometry
manuscripts. It uses the credited physical inequalities and value G1,
not an assumption that arbitrary lists satisfying those inequalities are APPT.

## 2. Actual peak and middle-body defects

Set

    u=u_D=3D/(D+2),           a_alpha=alpha(alpha-1)/2,
    U=u^alpha,               V=a_alpha gamma,
    w_p=U/(U+V),             w_b=V/(U+V),
    chi=log(U/D),            chi_plus=max(chi,0),
    h=alpha log(u/y_1)>=0.                                      (2.1)

The nonnegativity of h uses the exact physical largest-eigenvalue bound,
not a caller-supplied peak target. The value G1 is

    M*_alpha-1 ~ (U+V)/D,
    E_alpha ~ log[1+(U+V)/D]/(alpha-1).                          (2.2)

Retain the actual middle quantities used by the credited physical proofs:

    R_m=m(m-1)/2, K_m=m(m+1)/2, j=D-K_m+1,
    I_mid={R_m,...,j}, N=D-m^2+2,
    A=y_j>0, A_plus=y_(R_m), kappa=A_plus/A-1,
    mu=N^-1 sum_(I_mid)y_i,
    theta=(mu/A-1)/kappa if kappa>0, otherwise theta=0,
    L=(m-1)kappa in [0,2],
    z_i=(m-1)(y_i/A-1) in [0,L],
    J=N^-1 sum_(I_mid) z_i(L-z_i)>=0,
    d_b=(2-L)+|theta-1/2|+J.                                   (2.3)

If kappa=0, all z_i are zero and J=0. These are quantities computed from
the actual state. The width bound and positivity of the pivot are physical
consequences of the every-global-unitary APPT witnesses. J is an explicit
spread defect; matching width and mean without J is not sufficient.

## 3. Complete necessary-and-sufficient criteria

**Theorem A: sharp moment EXCESS.** For every sequence (1.1),

    [M_alpha(rho)-1]/[M*_alpha-1]->1

if and only if

    w_p min{1,h}+w_b min{1,d_b}->0.                            (3.1)

**Theorem B: relative entropy DEFICIT.** For every such sequence,

    e_alpha(rho)/E_alpha->1

if and only if

    w_p min{1,h/(1+chi_plus)}+w_b min{1,d_b}->0.                 (3.2)

The criteria are WEIGHTED SUMS. On a subsequence where both weights stay
positive, both physical contributions must saturate simultaneously. A minimum
between two branch defects would be wrong in this sublinear regime.

Thus if U/V tends to a number in (0,infinity), sharp moment and entropy
nearoptimality are both equivalent to h->0 and d_b->0. If U/V->0, they
are both equivalent to d_b->0. If U/V->infinity, the moment criterion is
h->0 and the entropy criterion is h/(1+chi_plus)->0. The weighted forms
also cover arbitrary oscillation among these cases and across chi signs.

**Theorem C: body law on every retained-bulk subsequence.** Let

    nu_m=D^-1 sum_i delta_(m(y_i-1)),
    beta=(delta_-1+delta_1)/2.

On every subsequence with liminf w_b>0, one has gamma->infinity. On that
subsequence d_b->0 is equivalent to

    W_2(nu_m,beta)->0.                                        (3.3)

Consequently either bulk term in (3.1) or (3.2) may equivalently be replaced
by w_b min{1,W_2(nu_m,beta)} on arbitrary paths. This does not infer W_2
from bare weak convergence: the physical exceptional square-mass estimate
is explicitly used in its proof.

**Corollary D: the necessary width margin when both contributions matter.**
If both weights stay bounded below and either nearoptimality holds, then

    alpha eta_m(kappa)->0,
    (m/alpha)(2-L)->infinity,                                (3.4)

where eta_m is the actual physical peak/width protection function from L7.
Thus full-width convergence is compatible with a sharp physical peak only
through a controlled vanishing width margin. Formula (3.4) is necessary,
not a replacement for the actual peak defect h.

## 4. Credited physical estimates and an all-state moment identity

The captured complete ordinary G proof gives, uniformly over every actual
APPT density and every n>=m, for all sufficiently large m,

    0<=y_i<=3, y_1<=u, y_2<=v_m->1+sqrt(2)<3,
    |y_i-1|<=delta_m=O(1/m) for i in I_mid,
    Q_E=sum_(i outside I_mid)(y_i-1)^2<=C,
    Q=sum_i(y_i-1)^2<=zeta_m(gamma+8), zeta_m->1.             (4.1)

The constants are independent of n and the state. These are G11-G14;
their original every-unitary witness, graph and trace proofs are credited,
not rerun or declared part of a new Lean audit. Set Q_B=Q-Q_E.

For alpha>=2 the exact centered kernel identity G18 is

    D(M_alpha-1)=sum_i[y_i^alpha-1-alpha(y_i-1)].              (4.2)

On I_mid, alpha delta_m->0, so Taylor's integral formula uniformly gives

    sum_(I_mid)[y_i^alpha-1-alpha(y_i-1)]
       =a_alpha Q_B[1+o(1)].                               (4.3)

The formula includes Q_B=0 by bounding the absolute remainder by
o(1)a_alpha Q_B. Outside I_mid isolate the actual first eigenvalue. All
other exceptional kernels are nonnegative and bounded in total by
a_alpha C v_m^(alpha-2). The subtracted first-eigenvalue polynomial
has absolute value at most 1+2alpha. Since u>=8/3 and eventually v_m<=5/2,

    [(1+2alpha)+a_alpha C v_m^(alpha-2)]/U ->0.              (4.4)

Also (4.1) bounds a_alpha Q_B by O(V+a_alpha). Since a_alpha/U->0,
the accumulated errors divided by U+V tend to zero uniformly. Therefore
for EACH actual density,

    D(M_alpha-1)=y_1^alpha+a_alpha Q+o(U+V).                 (4.5)

Replacing Q_B by Q costs at most a_alpha C=o(U). This is a state-uniform
identity, not just the upper estimate G19 or a computation on a candidate.
Together with the existing value (2.2), it gives

    (M_alpha-1)/(M*_alpha-1)
       =w_p exp(-h)+w_b(Q/gamma)+o(1).                     (4.6)

The possibility Q/gamma>1 is controlled rather than silently dropped.
Indeed (4.1) yields

    w_b(Q/gamma-1)_+
      <=|zeta_m-1|+8zeta_m a_alpha/(U+V)->0.               (4.7)

Thus clipping Q/gamma at one changes (4.6) by o(1). Both remaining
losses are nonnegative, so (4.6) saturates if and only if

    w_p(1-exp(-h))+w_b(1-Q/gamma)_+->0.                   (4.8)

The first factor is comparable, with absolute positive constants, to
min{1,h}. To convert the second one into d_b requires the actual body
analysis in the next section. No nonnegative loss is canceled against
an uncontrolled variance overshoot.

## 5. Retained bulk weight, exact spread and the W_2 body law

Whenever w_b>=epsilon>0, V/U is bounded below, and hence

    gamma >= c_epsilon U/a_alpha ->infinity.              (5.1)

In this range N/D->1. The exact trace cancellation and Cauchy-Schwarz,
using Q_E<=C and at most m^2 exceptional slots, give

    N(mu-1)=-sum_(outside I_mid)(y_i-1),
    |mu-1|<=m sqrt(C)/N,
    m(mu-1)=O(1/gamma)->0.                               (5.2)

This is stronger than an uncentered count-times-maximum estimate and is
needed at the m scale. A=1+O(1/m) follows from (4.1). By the exact mean
of z_i and the definition of J,

    mean z_i=L theta,
    Var(z_i)=L^2 theta(1-theta)-J.

There is therefore an exact identity

    Q_B/gamma
      =(N/D)[m/(m-1)]^2 A^2[L^2 theta(1-theta)-J]
            +(m^2 N/D)(mu-1)^2.                          (5.3)

Equations (5.2),N/D->1,A->1 and Q_E/gamma->0 imply

    Q/gamma=L^2 theta(1-theta)-J+o(1)                    (5.4)

on every retained-bulk subsequence, uniformly in the state. Since L<=2,
theta in [0,1] and J>=0, saturation of this expression at one is
equivalent exactly to

    L->2, theta->1/2, J->0,

or d_b->0. If w_b tends to zero, either weighted bulk defect vanishes
automatically. A bad-subsequence argument using (5.1)-(5.4) thus proves
the equivalence of the weighted variance loss in (4.8) and w_b min{1,d_b}
on arbitrary oscillating paths. This completes Theorem A.

For the body law, J->0 forces the bounded middle z_i onto the endpoints
0 and L in mean squared distance; the mean L theta gives the endpoint
weights. From A=mu/(1+kappa theta) and (5.2),

    m(A-1)->-1,      m A kappa->2.

The middle scaled actual eigenvalues m(y_i-1) consequently converge to
beta in W_2. Their missing exceptional contribution has second moment

    D^-1 sum_(outside I_mid)[m(y_i-1)]^2=Q_E/gamma->0,

and its mass tends to zero. Adding those atoms preserves W_2 convergence.
Conversely W_2(nu_m,beta)->0 implies its second moment Q/gamma->1,
which implies d_b->0 by (5.4). This proves Theorem C. The weighted
whole-path reformulation follows by the same retained-weight subsequence
argument, with min{1,W_2} controlling vanishing-weight subsequences.

## 6. Entropy when the peak increment stays bounded

Put t=(U+V)/D. The sublinear assumption gives

    t=exp(chi)+a_alpha/m^2,
    a_alpha/m^2->0.                                       (6.1)

If chi is bounded above, t and hence M*_alpha-1 stay bounded above.
For 0<=s<=t<=R, the scalar implication

    log(1+s)/log(1+t)->1 iff s/t->1                     (6.2)

holds uniformly, including t->0. One proof uses compactness of
log(1+at)/log(1+t) on 0<=a<=1,0<=t<=R, with removable value a at t=0:
for a<=1-epsilon its maximum is strictly below one. Apply this to
s=M_alpha-1 and t=M*_alpha-1, which obey 0<=s<=t exactly. Thus relative
entropy optimality is equivalent to Theorem A on this regime. Since
1+chi_plus is bounded above and below by positive constants here,
replacing h by h/(1+chi_plus) leaves its weighted vanishing condition
unchanged. This proves Theorem B on all chi-bounded-above subsequences,
including chi->-infinity and every finite peak-to-bulk competition.

## 7. The unbounded-peak-log entropy regime

Assume chi->+infinity. By (6.1), w_p->1,w_b->0, and the optimum has

    log M*_alpha=chi+o(1).                                (7.1)

First prove that entropy nearoptimality forces y_1->3. Suppose instead
y_1<=3-epsilon on a subsequence. Apply the exact kernel bound to all
exceptional entries with the actual ceiling y_1, and to the middle
entries as in (4.3). From (4.1),

    M_alpha-1 <= C a_alpha y_1^(alpha-2)/D+O(a_alpha/m^2).

For a fixed eta>0 and all sufficiently late terms this gives

    M_alpha <=1+exp[chi-eta alpha+O(log alpha)]+o(1)
             <=1+exp[chi-(eta/2)alpha]+o(1).             (7.2)

Here u->3 and log(u/y_1) is bounded below positively. Since
chi<=alpha log3 and chi->infinity, taking logs in (7.2) bounds the ratio
log M_alpha/chi away from one (or by zero if the exponent is negative).
This contradicts nearoptimality and proves y_1->3.

When y_1->3, its actual power dominates all the OTHER exceptional kernels:
eventually y_1>=8/3 and v_m<=5/2, so their ratio is bounded by a constant
times alpha^2(15/16)^alpha. The subtracted peak polynomial is also
negligible relatively. The whole middle increment is O(alpha^2/m^2)=o(1).
Thus (4.2) now yields the stronger state-dependent reduction

    M_alpha=1+[y_1^alpha/D][1+o(1)]+o(1),
    log M_alpha=log[1+exp(chi-h)]+o(1).                 (7.3)

The second equality holds uniformly relative to 1+y_1^alpha/D, whether
that actual peak contribution tends to zero, stays finite or diverges.
It has not been inferred by taking logarithms of the coarse o(U+V)
error in (4.5), which would be invalid for small actual contributions.

Equations (7.1)-(7.3) show that entropy nearoptimality is equivalent to
h/chi->0. Conversely that condition implies h/alpha->0 because
chi/alpha<=log3; hence y_1=u exp(-h/alpha)->3 and (7.3) applies, proving
nearoptimality. This is exactly (3.2) on chi->+infinity. Every arbitrary
chi sequence has a further subsequence bounded above or tending to
infinity. These cases prove both directions of Theorem B on all paths,
including infinite oscillations across critical scales.

## 8. Physical peak/width compatibility in the two-contribution regime

Retain the exact necessary physical inequality L7, valid for every actual
APPT density:

    y_1<=A[3-eta_m(kappa)],
    eta_m(kappa)=2(m-2)kappa^2/[2-(m-3)kappa].             (8.1)

If both weights stay positive, (5.1) gives gamma->infinity and (6.1)
actually gives exp(chi)=O(alpha^2/m^2)->0. Both entropy and moment
nearoptimality therefore force h->0 and d_b->0. Since alpha log A=o(1)
by (4.1), and alpha log(1+2/D)=o(1), (8.1) implies

    0<=alpha[-log(1-eta_m/3)]
         <=h+alpha log A+alpha log(1+2/D)->0.

Bounding the right side above by h+O(alpha/m)+O(alpha/D) makes the last
step valid regardless of the sign of log A. Thus alpha eta_m->0.
Write delta=2-L->0. The exact expression is

    eta_m=2(m-2)L^2/[(m-1)(4+(m-3)delta)],
    eta_m[4+(m-3)delta]->8.

As alpha->infinity, alpha eta_m->0 forces
(m/alpha)delta->infinity, proving Corollary D. The retained actual peak
loss is essential. This proof does not silently attach a peak to an
unprotected full-width spectrum.

## 9. Actual witnesses against two wrong extensions

The credited G1 integer projection/protected-spike construction attains
(2.2) uniformly and hence makes the criteria nonvacuous, including when
both contributions are comparable. Its all-unitary APPT sufficiency,
trace normalization and integer ranks remain credited; they are not
replaced by a formal unphysical list.

First, a minimum of branch defects would be wrong. Choose any integer
alpha->infinity, m=alpha^2 and integer n nearest above

    2m 3^alpha/[alpha(alpha-1)].

Then gamma->infinity, U~V, w_p,w_b->1/2 and t->0. The exact physical
pole rho=(I+2vv*)/(D+2) has h=0 and d_b bounded away from zero. Its
moment-excess and entropy-deficit ratios tend to 1/2, not one. Thus
min{h,d_b}->0 is not a valid criterion. Both positive contributions
must be saturated as a weighted sum requires.

Second, dropping J would be wrong. Put alpha even, m=alpha^2 and choose
n=m 3^(2alpha), so w_b->1. Divide the D coordinates into proportions
1/4,1/2,1/4, and let X have respective eigenvalues 0,1/2,1. Set

    t_m=2/(m-1),       rho=(I+t_m X)/Tr(I+t_m X).

This is an ACTUAL all-global-unitary APPT density. For any unit-vector
partial-transpose witness W and any 0<=X<=I,
Tr(XW)>=sum_(negative eigenvalues of W) eigenvalue>=-(m-1)/2;
thus Tr[(I+t_m X)W]>=0 after every global conjugation. Positivity and
trace normalization are immediate. In its actual middle spectrum,
L->2,theta->1/2 but J->1/2 and Q/gamma->1/2. Its moment-excess and
entropy ratios tend to 1/2. Width and mean alone would falsely accept
it. This is a physical counterexample, not a simulated scalar proposal.

The entropy/moment distinction is also genuine within (1.1). Take
integer alpha=k,m=n=k^2 and the actual reduced-strength pole

    rho=[I+(2-alpha^(-1/2))vv*]/[D+2-alpha^(-1/2)].

Its h~sqrt(alpha)/3 diverges, whereas chi~alpha log3 and h/chi->0;
w_b->0. It is entropy nearoptimal but its normalized moment excess tends
to zero. The underlying physical separation principle is already present
in G3; this example records it inside the present sublinear range.

## 10. Exact scope, attribution and remaining work

All necessary physical inequalities and the optimized value are credited
existing complete ordinary proofs. The new statements concern every actual
state, with the explicit spectral defects h,L,theta,J, the weighted sum,
the distinct entropy tolerance and all oscillating paths. Exceptional
trace contributions and variance overshoot are controlled explicitly.
No eigenbasis rigidity or exact finite optimizer follows.

The theorem handles (1.1) in full. Fixed positive limiting orders at
unbounded aspect, other zero-order rigidity windows outside previously
stated finite parameters, fixed-m relative synthesis, and every remaining
changing-dimension regime are not claimed here. The all-positive-order
VALUE theorem is already credited and is not re-proved as a new closure.
No APPT=ASEP inference, complete Lean, enlarged old audit, historical
priority, external human peer review, preprint, email, Release or DOI.

The complete manuscript, exact source/range map and author controls must
receive a new independent ordinary read before any proved index or reviewed
status changes. The earlier phase-4 scalar review does not cover this new
sublinear spectral scope.
