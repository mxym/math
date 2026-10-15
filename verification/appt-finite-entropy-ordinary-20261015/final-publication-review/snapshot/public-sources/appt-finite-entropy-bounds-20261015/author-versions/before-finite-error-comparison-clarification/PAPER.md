# Finite APPT entropy bounds and a simpler superlinear relative formula

Yongxian Zhang (张永贤), South China University of Technology.
15 October 2026, Asia/Shanghai. Complete author manuscript; independent
ordinary review pending. Same APPT research direction, no new major count.

## 1. Original problem and relation to the existing all-order theorem

Let APPT(m,n) be the actual complex positive semidefinite trace-one matrices
on C^m tensor C^n remaining PPT under EVERY global unitary. Integers satisfy
2<=m<=n, D=mn. Natural logarithms are used and

    E_alpha=max_APPT(log D-S_alpha), alpha>0,

with the continuous von Neumann interpretation at alpha=1. A maximum exists
by compactness. This paper concerns m->infinity, uniformly in n>=m and in
all positive real orders; it does not assert the same relative statement
with a fixed smaller dimension merely from D->infinity.

The existing ALL_ORDER_VARIATIONAL.md already proves a relative equivalent
for ALL positive orders and ALL n>=m as m grows, by a calibrated finite
scalar profile, with the stronger moment comparison at large orders.
This manuscript does NOT first close that range. Its contributions are
the explicit finite bound R0, an elementary maximum of two branches in
the superlinear regime, and an alternative entropy-only simplification.
The initial local literature screen missed that later companion and
incorrectly framed the range as open; the original source and correction
are retained. No mathematical error in the displayed bounds was found
by that discovery, but the initial novelty/range-closure framing was false.

Put q=(m+1)/(m-1), t=q-1 and, for alpha>1, a=alpha-1. Define

    H(m,D,alpha)=max{log q, log3-logD/a}.                  (R1)

**R0 (stronger finite upper bound).** For EVERY integer 3<=m<=n and
EVERY real alpha>=2, on the full original quantum domain,

    E_alpha <= H+log27/a+4m/(D-m).                        (R2)

Also, whenever alpha*t>=2 and D/(alpha*t)>=2, an actual APPT projection
state of integer rank floor(D/(alpha*t)) gives

    E_alpha >= log q-[log(2alpha*t)+1]/a.                 (R3)

These are finite inequalities, not eventual bounds. They sharpen the
upper estimate and adapt the lower rank to the width t, respectively.

**R1 (all superlinear orders, every aspect).** Whenever m->infinity,
n>=m and alpha/m->infinity, without ANY additional order/dimension or
aspect restriction,

    E_alpha ~ H(m,D,alpha).                              (R4)

Equivalently, for every real sequence V_m->infinity,

    sup_(n>=m, alpha>=m V_m) |E_alpha/H-1| ->0.           (R5)

H is strictly positive even when the peak branch is negative. This is a
relative first-order result, including when H and E_alpha tend to zero;
the earlier uniform absolute growing-order formula alone did not imply it.

## 2. An alternative entropy profile on an already proved range

The credited linear-order manuscript defines, for c>0,r>=0,

    g_c(L)=2cL^2/[3(2-L)] (0<=L<2), exp[-g_c(2)]=0,
    F_*(c,r)=max_(0<=L<=2, 0<=theta<=1)
       exp(-cL theta)[1+theta(exp(cL)-1)+r exp(-g_c(L))].  (R6)

This is a genuine compact scalar maximum, not a claim that a sampled grid
optimizes the physical set exactly. Its dependence on c,r is continuous.
For 0<alpha<=sqrt(m), let P_alpha be the EXISTING explicit profile U0 in
research/appt-growing-renyi/UNIFORM_PROFILE.md, restated here with
B=max(4,n/m) and u_D=3D/(D+2):

    P_alpha = D^-1 max{1,1-m^(-alpha)+(alpha/2)B}, 0<alpha<1/2;
    P_alpha = D^-1[2alpha+(alpha/2)B],             1/2<=alpha<=2;
    P_alpha = a^-1 log[1+(u_D^alpha-1-2alpha)/D
                              +alpha*a*B/(2D)], 2<alpha<=sqrt(m).

For sufficiently large m, define the single approximant

    A_alpha(m,n)=P_alpha,                     0<alpha<=sqrt(m);
    A_alpha(m,n)=a^-1 log F_*(alpha/m,3^alpha/D), alpha>sqrt(m). (R7)

**R2 (all positive orders, unrestricted aspect).**

    sup_(n>=m, alpha>0) |E_alpha/A_alpha-1| ->0
    as m->infinity.                                      (R8)

The supremum includes tiny, fixed, sublinear, linear and arbitrarily
superlinear orders, alpha>D, and oscillations among all these regimes.
It retains the first nonzero relative size. It uses a two-variable scalar
profile rather than a finite-dimensional exact optimizer formula. No
interchange of nonuniform limits or claim about all finite equality
spectra is implicit in R8. This range was already proved by the calibrated
V_* theorem. Here the same uncalibrated limiting F_* is used at every
large order, at the ENTROPY scale only. No unrestricted-order relative
MOMENT statement with 3^alpha replacing u_D^alpha is claimed; that stronger
statement would fail when alpha is much larger than D.

## 3. Credited physical inputs and a dimension-free power remainder

For a sorted actual spectrum use the exact notation of P0-P2:

    R=m(m-1)/2, K=m(m+1)/2, b=lambda_(D-K+1)>0,
    x_i=lambda_i/b, kappa=x_R-1, v=1+kappa,
    p_i=x_i-v>=0 (i<=R), s=D^-1 sum_i x_i.

The existing finite quantum witnesses and graph estimates give

    1<=v<=q<=2 (m>=3), 0<=x_i<=3,
    x_i<=v (i>R), sum_(i<=R)p_i<=m,
    sum_(i<=R)p_i^2<=8, s>=1-m/D.                       (R9)

These are necessary inequalities for every actual all-unitary APPT
density. Their full physical derivation is credited to SHARP_ASYMPTOTIC
Sections 2-4 and the cubic-entropy manuscript Section 4, as read for P0-P2.
No arbitrary list satisfying R9 is presumed physically sufficient.

For alpha>=2 and v in [1,2], the divided Taylor remainder

    J_v(p)=[(v+p)^alpha-v^alpha-alpha*v^(alpha-1)*p]/p^2

is nondecreasing for p>=0. Indeed its continuous value at zero and its
values for positive p equal

    alpha*(alpha-1) integral_0^1 (1-u)(v+u*p)^(alpha-2) du,

whose integrand is nondecreasing in p. Since 0<=p_i<=3-v and 3-v>=1,

    J_v(p_i)<=J_v(3-v)<=3^alpha/(3-v)^2<=3^alpha.         (R10)

For every top term add its exact linear Taylor term; every other term is
at most v^alpha. R9/R10 yield the finite moment inequality

    D^-1 sum x_i^alpha
       <=v^alpha+(alpha*m/D)v^(alpha-1)+8*3^alpha/D
       <=(1+alpha*m/D)q^alpha+8*3^alpha/D.               (R11)

The constant eight is independent of alpha. Unlike an epsilon-counting
bound, R11 introduces no polynomial-in-alpha factor on the peak term.

The exact normalized deficit of any such density is

    [log(D^-1 sum x_i^alpha)-alpha log s]/a.

The logarithm in R11 is at most

    max{alpha logq, alpha log3-logD}+log(9+alpha*m/D).

Use log(9+z)<=log9+z for z>=0, alpha/a<=2, logq<=log3,
and -log s<=m/(D-m). Dividing by a gives

    E_alpha<=H+log27/a+2m/D+2m/(D-m),

which proves R2 with all trace factors retained.

## 4. An actual integer-rank width-adapted lower bound

Under the two finite conditions in R0, k=floor(D/(alpha*t)) satisfies
1<=k<D and theta=k/D lies between 1/(2alpha*t) and 1/(alpha*t).
For ANY rank-k orthogonal projection P,

    rho=(I+tP)/(D+t*k)

is actual all-global-unitary APPT: the negative trace of a partial-
transposed unit-vector projector is at most (m-1)/2=1/t, so its pairing
against any projection is at least -1/t. Testing every unit vector and
every global unitary proves positivity after partial transpose.

The exact normalized moment is

    [1+theta(q^alpha-1)]/(1+t*theta)^alpha.

Its numerator is at least theta*q^alpha, and
alpha log(1+t*theta)<=alpha*t*theta<=1. Hence

    E_alpha>=[alpha logq-log(2alpha*t)-1]/a
            >=logq-[log(2alpha*t)+1]/a,

proving R3. Here k is the projection rank; rho has full matrix rank D.
The existing actual pole rho_v=(I+2vv*)/(D+2) separately gives, for
every alpha>=2,

    E_alpha>=log3-logD/a-4/D.                            (R12)

This last finite estimate was proved in P0-P2 with exact normalization.

## 5. Superlinear relative accuracy, including a vanishing deficit

Consider ANY sequence m->infinity, n>=m, alpha/m->infinity. Then
alpha->infinity and logq~2/m. Write tau=log3-logD/a, H=max(logq,tau).

First restrict to terms with tau>=log3/2. Then H is bounded below by
log3/2. The R2 upper error tends to zero: 1/a->0 and
m/(D-m)<=1/(m-1)->0. The physical pole lower R12 gives
E_alpha>=tau-o(1). Eventually logq<log3/2, so H=tau and E_alpha/H->1.

On all remaining terms tau<log3/2, and consequently

    D>exp[(log3/2)*a].                                  (R13)

Because m=o(alpha), every fixed power of m or alpha divided by D tends
to zero on these terms. Also alpha*t~2alpha/m->infinity and
D/(alpha*t)->infinity, so the finite conditions of R3 eventually hold.
The upper error in R2 divided by H>=logq~2/m is

    O(m/alpha)+O(m^2/D)->0.

For the lower bulk error, put c=alpha/m->infinity. Since alpha*t~2c,

    [log(2alpha*t)+1]/[a logq]=O(log c/c)->0.             (R14)

Thus the actual projection state gives E_alpha>=logq-o(logq), while
R12 gives E_alpha>=tau-o(logq), as m/D->0. Taking the larger of these
two actual lower bounds proves E_alpha>=H-o(logq)>=H-o(H). This and
the upper estimate establish R4 on the entire sequence.

If the supremum R5 failed, selecting a violating n_m,alpha_m would
give a sequence with alpha_m/m>=V_m->infinity, contradicting R4.
This proves the exact uniform quantifiers without an assumed aspect scale.

## 6. Large-c behavior of the coupled profile and uniform assembly

The credited linear-order proof explicitly optimized the theta variable.
Its pure-bulk width L=2 competitor gives, for every c>0,

    F_*(c,0)=[(exp(2c)-1)/(2c)]
                     exp[-1+2c/(exp(2c)-1)].            (R15)

For c>=1 this implies log F_*(c,0)>=2c-log(2c)-2. The L=0 competitor
has value 1+r. In the opposite direction, each bulk term in R6 is at
most exp(2c), and its peak term is at most r. Therefore, for EVERY r>=0,

    max{2c,log(1+r)}-log(2c)-2
       <=log F_*(c,r)<=max{2c,log(1+r)}+log2.            (R16)

Since the maximum in R16 is at least 2c, the relative log discrepancy
tends to zero as c->infinity, UNIFORMLY in r>=0.

Set c=alpha/m, r=3^alpha/D. The positive logarithm satisfies

    |a^-1 log(1+r)-max{0,tau}|<=(log3+log2)/a.

Also 2c/a~2/m~logq when m->infinity and c->infinity. Since H>=logq,
these comparisons and R16 give

    a^-1 log F_*(alpha/m,3^alpha/D) ~ H                 (R17)

on every superlinear sequence. Replacing 3 by u_D inside an alpha-th
power has NOT been assumed in an unrestricted moment theorem; the
comparison here is at the positive entropy logarithm scale.

Finally take any sequence m->infinity, n>=m and alpha>0. For
alpha<=sqrt(m), the existing U2 theorem applies to the sublinear cutoff
sqrt(m). For alpha>sqrt(m), pass to a subsequence on which c=alpha/m
is bounded or tends to infinity. In the bounded case choose a fixed C
containing the subsequence and use the complete existing linear-order
Theorem L2/L5, which has exactly R7 on this branch. In the diverging case
use R4 and R17. If R8 failed, a sequence with relative error bounded
below would yield one of these contradictory subsequences. This proves
the full supremum over EVERY positive real order and EVERY n>=m.

## 7. Dependencies, review and limitations

The finite quantum inputs are the source-bound P0-P2 manuscript and its
credited graph/witness derivation. The all-order sublinear theorem U2 and
the linear-order Theorems L1/L2 are the existing complete ordinary proofs
in research/appt-growing-renyi/UNIFORM_PROFILE.md and
LINEAR_ORDER_VARIATIONAL.md. R15 and the exact definition of F_* are also
from that same linear-order source; they are not new physical assumptions.
Their earlier reads retain their original byte/scope binding. This new
remainder inequality, superlinear relative theorem and all-order assembly
require their own independent complete read; that review is pending.

The older calibrated V1/V2 theorem already closed the all-order
relative-accuracy gap; its full manuscript and prior review are explicitly
credited and bound in CREDITED_INPUTS.json. The present finite estimate
and entropy-profile simplification do not replace its stronger relative
moment comparison. The earlier missed local source, original incorrect
scope framing and correction remain in author-versions/ and RESEARCH_LOG.md.

This supplies finite bounds and a simpler asymptotic corollary, not every exact finite
entropy extremum, its equality spectra, or full changing-dimension spectral
rigidity. It does not prove absolute separability of projection competitors
or general APPT=ASEP. The fixed-m small-order problem is not subsumed by
R8. Neither alpha=0 nor alpha=infinity is a substitution into a denominator
in R7. Their separately known exact endpoints stay separate.

Finite diagnostics can check the remainder and the actual projection/pole
algebra; no finite sampling proves the original universal optimization.
Current bounded primary abstract/query checks are context, not a priority
certificate or a new full-paper review. No complete Lean, enlarged old
audit, external human peer review, new major-conjecture count, submission,
email, Release or DOI. No external funding; OpenAI AI assistants assisted.
Original rights reserved and all third-party notices retained.
