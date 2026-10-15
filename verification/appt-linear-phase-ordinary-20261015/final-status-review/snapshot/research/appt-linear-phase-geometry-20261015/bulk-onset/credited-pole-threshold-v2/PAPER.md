# A sharp pole threshold and two parameter regimes of the APPT entropy profile

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. ORCID 0009-0000-3864-3536;
mxymmxym1@gmail.com. 15 October 2026, Asia/Shanghai.
No external funding. OpenAI AI assistants assisted research and writing.
Copyright 2026 Yongxian Zhang; all rights reserved for original material.

AUTHOR VERSION: complete ordinary argument awaiting an independent full
read. No result in this version has additional Lean coverage. The existing
linear-order value theorem and the actual spectral classification are
credited inputs, not new claims of this note. The full intermediate-parameter
phase diagram is not asserted here.

## 1. The credited quantum reduction and the new scalar questions

Let rho be an actual complex PSD trace-one APPT density on C^m tensor C^n:
partial transposition is positive after every global unitary. Let m<=n,
D=mn and y_i=D lambda_i with eigenvalues in decreasing order. For real
orders alpha>1 set

    M_alpha(rho)=D^-1 sum_i y_i^alpha,
    M*_alpha=max_APPT M_alpha,
    E_alpha=max_APPT(log D-S_alpha)=log M*_alpha/(alpha-1).

The previously proved linear-order theorem L1 states, for each fixed
0<c_-<=c_+<infinity, as m->infinity,

    sup_(n>=m, c_-m<=alpha<=c_+m)
      |M*_alpha/F_*(alpha/m,3^alpha/D)-1| ->0,           (T1)

where the continuous compact scalar optimization is

    G(L)=2L^2/[3(2-L)] for 0<=L<2,
    B(c,L,h)=exp(-cLh)[1+h(exp(cL)-1)],
    P(c,L,h)=exp[-c(Lh+G(L))] for L<2, P(c,2,h)=0,
    F(c,r;L,h)=B(c,L,h)+r P(c,L,h),
    F_*(c,r)=max_([0,2]x[0,1]) F(c,r;L,h).             (T2)

Here c>0 and r>=0. At L=0 one has B=P=1, so F=1+r.
The independent all-order value extension is also already complete; T1
is the part needed here. In particular no new all-order closure is claimed.

The prior actual-spectrum theorem S gives a necessary and sufficient
criterion for all actual near-optimizers when

    alpha/m->c in (0,infinity), 3^alpha/D->r<infinity.  (T3)

That criterion retains the FULL scalar argmax set. The present note
determines the exact threshold where the L=0 pole dominates, describes its
small-c geometry, and solves the entire scalar optimization for c>=10.
These conclusions are about the already justified asymptotic profile.
They do not give an exact finite-dimensional APPT entropy cutoff.

Put

    b(K)=(exp(K)-1)/K * exp[-1+K/(exp(K)-1)], K>0,
    h_bulk(c)=1/(2c)-1/(exp(2c)-1).

The credited pure-bulk calculation gives

    max_(L,h) B(c,L,h)=b(2c)>1,
    argmax B={(2,h_bulk(c))}.                          (T4)

## 2. An attained global pole threshold, including all ties

For L>0 define

    Q(c,L,h)=(B(c,L,h)-1)/(1-P(c,L,h)),
    Q(c,0,h)=0,
    r_crit(c)=max_([0,2]x[0,1]) Q(c,L,h).             (T5)

At L=2 this means Q=B-1. Jensen's inequality, applied to the
mean-zero two-point variable Z=L(X-h), X Bernoulli(h), gives B>=1.
For L>0 the denominator is strictly positive. Section 3 proves continuity
at L=0, uniformly for c in positive compact intervals; continuity at L=2
follows from P->0 uniformly in h on such intervals. Thus Q is jointly
continuous on each such compact rectangle. In particular r_crit is finite,
attained, positive and continuous in c. It is at least b(2c)-1.

**Theorem T2 (complete pole-onset criterion).** For each c>0:

* If r>r_crit(c), then F_*(c,r)=1+r and its scalar maximizers are
  precisely {0}x[0,1].
* If 0<=r<r_crit(c), then F_*(c,r)>1+r and all scalar maximizers
  have L>0 and 0<h<1.
* If r=r_crit(c), then F_*=1+r and its scalar argmax set is exactly

      ({0}x[0,1]) union argmax Q.                     (T6)

Every maximizer of Q has L>0 and 0<h<1. Every tie is retained; no
uniqueness of its positive width is assumed in this theorem.

Indeed for every L>0 the exact identity is

    F(c,r;L,h)-(1+r)=(1-P(c,L,h))[Q(c,L,h)-r].         (T7)

The claims follow by maximizing this identity; at h=0,1 one has Q=0,
whereas r_crit>0. At L=0 the original value is exactly 1+r.

This is a discontinuous scalar body transition. For a fixed c, any scalar
maximizer at r<r_crit satisfies Q>=r. If r increases to r_crit, these
maximizers stay a positive distance from L=0 and from h=0,1, since Q is
continuous and vanishes on those faces. Their limiting two-point body
laws have positive variance; the pole body law has variance zero.

There is also a strict kink in the optimized value. Write

    p_min(c)=min_{argmax Q} P(c,L,h)<1.

The one-sided r derivatives at r=r_crit are

    (d/dr)_- F_*=p_min(c), (d/dr)_+ F_*=1.             (T8)

For completeness, F_* is a maximum of affine functions of r on a compact
index set. Difference quotients from the left are bounded by the active
slopes at the threshold; subsequences of maximizers as r approaches the
threshold give the reverse bound and converge to active indices. Thus
the left derivative is the least active slope and the right derivative
the greatest. The active slopes are P on argmax Q together with 1 on
L=0. This proves T8. The corresponding derivatives of log F_* are
p_min/(1+r_crit) and 1/(1+r_crit).

## 3. A uniform small-c estimate which controls moving endpoints

Let

    A=Lh+G(L), B2=L^2 h(1-h)/2,
    f(L,h)=B2/A for 0<L<2,

and extend f by zero to L=0, L=2 and h=0,1. This extension is
continuous. For example f<=L(1-h)/2 at L=0; at L=2 use A>=G(L)
and B2<=1/2. These estimates also handle the corners uniformly.

The identity E Z=0 and the integral Taylor formula for exp(cZ), with
|Z|<=2, give the GLOBAL bounds

    exp(-2c)c^2 B2 <= B-1 <= exp(2c)c^2 B2.            (T9)

For every x>=0,

    x/(1+x)<=1-exp(-x)<=x.                            (T10)

Applying these to x=cA gives for 0<L<2

    exp(-2c) f <= Q/c <= exp(2c)(f+c B2).             (T11)

The boundary conventions extend the inequalities to the entire closed
rectangle. At L=2, T9 and 1-P=1 give Q/c<=exp(2c)c B2;
the lower bound is zero. At L=0 both sides of the required inequality
vanish. Since f<=1 and B2<=1/2, T11 proves

    sup_(L,h) |Q(c,L,h)/c-f(L,h)|=O(c) as c->0+.      (T12)

This proves a uniform global estimate, rather than interchanging an
interior Taylor expansion with a supremum. It also supplies the promised
continuity Q->0 at L=0 for c in positive compact intervals: the upper
bound in T11 is at most exp(2c)[L/2+c L^2/8].

## 4. The unique small-c coexistence point and its expansion

For 0<L<2 set a=2L/[3(2-L)], so L=6a/(2+3a). Then

    f(L,h)=L h(1-h)/[2(h+a)].                         (T13)

For each L the unique maximizing h is

    h=sqrt(a^2+a)-a in (0,1/2), a=h^2/(1-2h).

Substitution reduces its value to

    v(h)=3h^2(1-2h)/(3h^2-4h+2), 0<h<1/2,
    v'(h)=-6h(3h^3-8h^2+8h-2)/(3h^2-4h+2)^2.        (T14)

The cubic q(h)=3h^3-8h^2+8h-2 has q'(h)=9h^2-16h+8>0
on [0,1/2], q(1/3)<0 and q(3/8)>0. Thus it has a unique root
h0 in (1/3,3/8). Put

    a0=h0^2/(1-2h0), L0=6a0/(2+3a0),
    K0=v(h0)>0, A0=L0 h0+2L0^2/[3(2-L0)].            (T15)

The function f has a unique global maximizer (L0,h0) in (0,2)x(0,1).
It is nondegenerate. At its stationary h,

    f_hh=-L/(h+a)<0.

Also v''(h0)=-6h0 q'(h0)/(3h0^2-4h0+2)^2<0. The maximizing
h has strictly positive derivative in L: a'(L)=4/[3(2-L)^2]>0 and
dh/da=(2a+1)/(2sqrt(a^2+a))-1>0, since (2a+1)^2-4(a^2+a)=1.
Thus the optimized value as a function of L
has strictly negative second derivative there. Equivalently the Schur
complement f_LL-f_Lh^2/f_hh is negative. Together with f_hh<0 this
makes the full Hessian negative definite.

**Theorem T4 (small positive c).** There is an epsilon>0 such that for
every 0<c<epsilon the maximizer of Q is a unique interior pair
(L_c,h_c). This pair is real analytic in c down to c=0 and tends to
(L0,h0). In particular

    r_crit(c)=K0 c+K1 c^2+O(c^3),
    K1=K0[L0(1-2h0)/3+A0/2].                         (T16)

To prove uniqueness globally, use T12 and uniqueness of the global
maximizer of f: every maximizer of Q/c lies in an arbitrarily small fixed
neighborhood of (L0,h0) for sufficiently small c. Near that point Q/c
extends real analytically through c=0. Indeed its numerator divided by
c^2 and denominator divided by c are analytic, and the latter is A>0
at c=0. The nondegenerate implicit function theorem gives exactly one
critical point in a smaller neighborhood for all sufficiently small c.
It is a strict local maximum. The global localization just proved shows
that every global maximum is that critical point. This proves the claim.

For the coefficient in T16, write

    B3=L^3 h(1-h)(1-2h)/6.

The locally uniform analytic expansion is

    Q/c=f+c(B3/A+B2/2)+O(c^2).

The first derivative of f at its maximizing point is zero, so the
first change in the optimizing parameters contributes only at second
order to the optimized value Q/c. Its first correction is
B3/A+B2/2 at (L0,h0), which is K1 as displayed in T16.

For each such fixed small c, the positive-width scalar maximizer of F
is also unique and analytic in r for r just below r_crit(c). At the
threshold, at (L_c,h_c), differentiating T7 twice with respect to L,h
gives

    Hess_(L,h) F=(1-P) Hess_(L,h) Q,

which is negative definite for sufficiently small c. The implicit function
theorem therefore gives a unique local maximizing branch. If other global
maximizers for r increasing to r_crit stayed outside its neighborhood,
T7 and compactness would give a second maximizer of Q. If they approached
L=0, continuity of Q would contradict Q>=r_crit/2. Thus the local branch
contains every global maximizer for all r sufficiently close from below.

There is a genuine coupled phase for small c, in the precise sense that
the exact interval

    b(2c)-1 < r < r_crit(c)                            (T17)

is nonempty and on it

    F_*(c,r)>max{b(2c),1+r}.                          (T18)

Indeed b(2c)-1=c^2/2+O(c^3), whereas r_crit=K0 c+O(c^2).
On T17 the pole value already exceeds the pure-bulk value, and T2 says
the optimum is strictly greater than the pole. At coexistence the only
positive-width maximizer is (L_c,h_c); zero width is the other phase.

## 5. Exact solution of the whole scalar problem for every c>=10

**Theorem T5 (an explicit sufficient large-c regime).** For EVERY real
c>=10 and r>=0,

    r_crit(c)=b(2c)-1,
    F_*(c,r)=max{b(2c),1+r}.                          (T19)

Writing r0=b(2c)-1, the scalar argmax set is precisely

    {(2,h_bulk(c))}                       if r<r0;
    {(2,h_bulk(c))} union ({0}x[0,1])     if r=r0;
    {0}x[0,1]                            if r>r0.      (T20)

The constant 10 is a sufficient bound, not a claimed optimal or unique
transition parameter. The proof covers every interior width, not a finite
grid or just a local expansion near either endpoint.

First consider 0<L<=1 and 0<h<1. The same integral Taylor estimate,
now using |Z|<=L, and A>=Lh give

    B-1 <= c^2 L^2 h(1-h) exp(cL)/2,
    1-P >= cLh/(1+cLh),
    Q <= cL(1-h)(1+cLh) exp(cL)/2
       <= c(1+c)exp(c)/2.                            (T21)

The endpoint h values have Q=0, so this bound holds there too. On the
other hand, the competitor h=1/(2c) at L=2 gives

    b(2c)>=exp(2c)/(2 e c).                           (T22)

For c>=10,

    c(1+c)exp(c)/2 < exp(2c)/(2 e c)-1 <=b(2c)-1.     (T23)

Here are elementary constants for this strict comparison. The function
exp(c)/[c^2(1+c)] is increasing for c>=10, by logarithmic
differentiation. Since exp(2)>7 by its positive Taylor series,
exp(10)>7^5=16807>4*10^2*11. Thus exp(c)>4c^2(1+c) in this range.
Also e<3, and 2 e c exp(-c)<1 for c>=10. Consequently

    e c^2(1+c)+2 e c exp(-c)
       <3c^2(1+c)+1<4c^2(1+c)<exp(c),

which is exactly T23 after multiplication by the positive factors.
For example e<3 follows by comparing 1/k! with 1/2^(k-1) for k>=2,
strictly for k>=3; the bound on 2 e c exp(-c) follows from its monotonic
decrease for c>=1 and exp(10)>16807>60.

Next consider 1<=L<2, set delta=2-L in (0,1] and K=cL. The exact
logarithmic derivative is

    (log b)'(K)=1-1/K+2/(exp(K)-1)
                 -K exp(K)/(exp(K)-1)^2 >1/2, K>=3.  (T24)

Indeed K exp(K)/(exp(K)-1)^2 decreases for K>=1: its logarithmic
derivative is 1/K-1-2/(exp(K)-1)<0. Further e>163/60 from its
degree-5 Taylor polynomial with a positive remainder, and
163^3>20*60^3, so exp(3)>20. Since u/(u-1)^2 decreases for u>1,
the subtracted term at K=3 is <60/361<1/6. The remaining 1-1/K
is at least 2/3, and 2/(exp(K)-1) is positive. This proves T24.
Integration from K=cL to 2c gives

    b(K)/b(2c)<=exp(-c delta/2).                       (T25)

For c>=3 and delta in (0,1] one has the chain

    P <=exp[-2c/(3 delta)] <3 delta/(2c)
      <=c delta/(2+c)<=c delta/(2+c delta)
      <=1-exp(-c delta/2).                            (T26)

The first bound uses L>=1 in G=2L^2/(3 delta); the strict one is
exp(-x)<1/x for x>0. The next bound is precisely
3(c+2)<=2c^2, valid for c>=3. The last is T10. Combining T25-T26
shows P<1-b(K)/b(2c). Since B(c,L,h)<=b(K), at r0=b(2c)-1,

    F(c,r0;L,h)
      <b(K)+(b(2c)-1)[1-b(K)/b(2c)]
      =b(2c)-1+b(K)/b(2c)<b(2c).                    (T27)

The last inequality uses the strict increase of b on K>=3 and L<2.
Thus Q<r0 for every 1<=L<2. T21-T23 give the same strict conclusion
for 0<L<=1. At L=2, Q=B-1 has the unique maximizer h_bulk(c)
and maximum r0 by T4. This proves the exact threshold and its unique
positive-width maximizer.

At r=r0 the only active parameters are those in the middle line of T20.
At r=0 T4 gives only the bulk point. Since F is affine in r, interpolation
between these two values bounds F<=b(2c) on the entire interval
0<=r<=r0. Equality for 0<=r<r0 forces the unique r=0 bulk maximizer.
For r>r0, T2 gives exactly the zero-width parameters. This proves all
of T19-T20, including uniqueness and the coexistence equality case.

## 6. Consequences for the original APPT matrices

The quantum transfer is by the credited T1 and theorem S, with their
original definitions and hypotheses. For every fixed C>=10,

    sup_(n>=m, 10m<=alpha<=Cm)
      | M*_alpha/max{b(2alpha/m),1+3^alpha/D}-1 | ->0. (T28)

The corresponding logarithmic difference tends uniformly to zero, and
E_alpha is relatively equivalent to the logarithm of that maximum divided
by alpha-1. The positivity b(20)>1 bounds the reference logarithm away
from zero. C remains fixed: T28 is not an uncalibrated relative-moment
assertion for alpha/m->infinity or alpha comparable to D.

Here is the spectral meaning with complete quantifiers. Assume T3 and
actual near-optimality in the first nonzero entropy-deficit scale:

    (log D-S_alpha(rho_m))/E_alpha ->1.

Define, exactly as in S, R=m(m-1)/2, j=D-m(m+1)/2+1,
N=D-m^2+2, A_m=y_j, B_m=y_R, mu_m=N^-1 sum_(i=R)^j y_i,
kappa_m=B_m/A_m-1, L_m=(m-1)kappa_m, and

    h_m=(mu_m/A_m-1)/kappa_m if kappa_m>0, else 0,
    z_i=(m-1)(y_i/A_m-1),
    J_m=N^-1 sum_(i=R)^j z_i(L_m-z_i),
    PeakLoss_m=[A_m^alpha(3-eta_m(kappa_m))^alpha-y_1^alpha]/D,
    eta_m(k)=2(m-2)k^2/[2-(m-3)k].

Theorem S says that near-optimality is equivalent to distance of
(L_m,h_m) to the full scalar argmax set tending to zero, together with
J_m->0 and PeakLoss_m->0. Therefore T2, T6 and T20 supply explicit
necessary and sufficient conditions on the same original APPT states.
The losses must be retained; a bulk empirical law alone is not asserted
to be sufficient for r>0.

On a subsequence whose scalar parameters tend to (L,h), the FULL actual
empirical measure of m(y_i-1) converges in 1-Wasserstein distance to

    nu_(L,h)=(1-h)delta_(-Lh)+h delta_(L(1-h)).         (T29)

For r>r_crit(c) the only body law is delta_0. For r=r_crit(c) the
possible subsequential laws are exactly delta_0 and nu_(L,h) for
(L,h) in argmax Q. Each is attained by original APPT states, using the
physical constructions in S. At fixed c these nonzero laws have their
variance bounded away from zero. The set of possible laws need not be
convex: the scalar argmax characterization specifies the actual choices.
Alternating sequences among tied phases remain permitted.

For small c the positive law at coexistence is the unique
nu_(L_c,h_c), with limit nu_(L0,h0) as c->0. At r=r_crit(c)>0,
the pure pole and this interior mixed phase have respectively

    m(3-y_1)->0 and m(3-y_1)->3A(L_c,h_c),            (T30)

by the interior peak assertion of S. Both have y_1->3; the first
correction distinguishes them. The actual nonlargest normalized
eigenvalues tend uniformly to one in both cases. These are iterated
fixed-c then c->0 conclusions, not a new uniform joint limit theorem.

For c>=10, the explicit set T20 says the body law is pure bulk below
the threshold and delta_0 above it; at equality these are the only two
subsequential body laws. On a bulk branch L=2, theorem S gives
y_1^alpha/D->0. No finite first-order expansion T30 is asserted at L=2;
the protected-spike expansion is singular there.

## 7. What remains and how this version was screened

This note leaves open the optimal boundary of the large-c regime, the
complete scalar geometry for intermediate c, and whether there is a
unique transition c_* separating mixed and pure-envelope behavior.
It neither assumes those statements nor substitutes numerical evidence
for them. A separate depth researcher is addressing that intermediate
region; the present theorems do not rely on its unfinished calculations.

The actual all-aspect entropy VALUE and all-order equivalents were
already proved in the credited L/V notes. The new claims here are T2,
T4 and T5 and their justified consequences, not a second claim of that
closure. Complete all-order spectral rigidity, arbitrary finite exact
extrema, absolute separability, or a new major-conjecture solution are
not established by this scalar analysis.

Current PRIMARY abstract/version pages were checked for the entropy and
spectral papers arXiv:2609.18568v1 and arXiv:2608.03390v2; bounded
official-domain searches and a local manuscript search are documented
separately. No matching result was identified within the actually read
material. That limited screen is not a full-text priority certificate.
The proofs above use local credited theorems, not an unverified assertion
from a search snippet. Author controls and their source hashes are
separate from the forthcoming independent ordinary full read. No new
Lean audit, submission, email, Release, DOI or external human peer review.
