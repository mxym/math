# A relative APPT entropy equivalent uniform in both dimensions and every order

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. ORCID 0009-0000-3864-3536;
mxymmxym1@gmail.com. 15 October 2026, Asia/Shanghai.
No external funding. OpenAI AI assistants assisted research and writing.
Original material: all rights reserved; third-party attribution retained.
Author manuscript: independent ordinary mathematical review is pending.
No new Lean, external peer review, priority certificate, or major-result count.

## 1. Original quantities and the advance beyond the credited inputs

For integers 2<=m<=n put D=mn. APPT(m,n) consists of actual complex
positive semidefinite trace-one matrices whose partial transpose remains
positive after EVERY global unitary conjugation. Natural logarithms are
used. Let

    E_alpha(m,n)=log D-min_(rho in APPT(m,n)) S_alpha(rho).

For 0<alpha<infinity use spectral Renyi entropy and its continuous value
at alpha=1. Separately S_0=log rank and S_infinity=-log lambda_max.
For alpha>1, with y_i=D lambda_i, write

    M_alpha(rho)=D^-1 sum_i y_i^alpha,
    M*_alpha=max_APPT M_alpha,
    E_alpha=log M*_alpha/(alpha-1).

The all-order V theorem already gives relative accuracy uniformly in
n>=m and alpha>0 AS m TENDS TO INFINITY. The exact eventual A theorem
already gives every order at each FIXED m>=3. Neither is claimed new.
The fixed-m logarithmic window, loglog correction, and inverse-log
expansions were also already proved and are not re-proved here.

Here we give one specified profile with ONE total-dimension threshold
simultaneously for all dimension pairs and all orders, including paths
where m stays bounded, grows, or alternates, while alpha approaches zero
at an arbitrary rate. Its low-order part retains the finite-m bulk
function and the one-hole floor; its growing-m part retains the existing
multiscale head coefficient. The qubit part is a direct use of the known
Song--Chen extreme-point classification, not a new classification.

## 2. Scalar definitions without physical replacement assumptions

For m>=3 set

    q_m=(m+1)/(m-1), t_m=q_m-1,
    H_D=log[D/(D-1)], u_D=3D/(D+2),
    gamma=D/m^2, Z_(m,D)=max{4-gamma,0}.

For q>1 and 0<=theta<=1 define the two-level entropy deficit

    g_q(alpha,theta)
      ={log[1+theta(q^alpha-1)]-alpha log[1+(q-1)theta]}/(alpha-1)
                                                   (alpha>0, alpha!=1),
    g_q(1,theta)=theta q log q/[1+(q-1)theta]
                         -log[1+(q-1)theta].

Write

    B_m(alpha)=max_(0<=theta<=1) g_(q_m)(alpha,theta), alpha>0.

This maximum is positive. Its unique maximizing theta is the credited
closed scalar expression

    theta_alpha=[q_m^alpha-1-alpha t_m]
                  /[t_m(alpha-1)(q_m^alpha-1)]          (alpha!=1),
    theta_1=[q_m log q_m-t_m]/t_m^2.

The value at alpha=0, when needed in limits, is B_m(0)=0.
At alpha<1 the displayed maximum of deficits minimizes the moment;
at alpha>1 it maximizes the moment. The denominator is never interpreted
at alpha=1 by substitution.

For alpha>1 retain the EXACT previously calibrated finite profile

    eta_m(k)=2(m-2)k^2/[2-(m-3)k], 0<=k<=t_m,
    R_(D,alpha)=u_D^alpha/D,
    V_(m,D,alpha)=max_(0<=k<=t_m, 0<=theta<=1)
       [1+theta((1+k)^alpha-1)
           +R_(D,alpha)((3-eta_m(k))/3)^alpha]
                    /(1+k theta)^alpha.                (1)

The denominator in eta is positive on its entire interval. All powers
have positive bases, and V>=1+R>1. This is a continuous scalar maximum
on a compact rectangle. Its comparison with actual APPT optimization is
the content of the credited theorems, not a restriction in the definition
of the original quantum set.

For m>=3 define C_(m,D)(alpha) as follows. If alpha>sqrt(m), put

    C_(m,D)(alpha)=log V_(m,D,alpha)/(alpha-1).           (2)

If 0<alpha<=sqrt(m), use the following three cases:

    max{H_D, B_m(alpha)+(1-m^(-alpha))/D
                        +alpha Z_(m,D)/(2D)},          0<alpha<1/2;

    B_m(alpha)+2alpha/D+alpha Z_(m,D)/(2D),             1/2<=alpha<=2;

    log{ exp[(alpha-1)B_m(alpha)]
          +(u_D^alpha-1-2alpha)/D
          +alpha(alpha-1)Z_(m,D)/(2D) }/(alpha-1),     2<alpha<=sqrt(m).
                                                        (3)

The middle case is intersected with alpha<=sqrt(m); in particular for
m=3 its upper endpoint is sqrt(3), not 2. The third case is empty when
sqrt(m)<=2. The divisions .5, 2 and sqrt(m) organize approximants and are
not asserted physical phase boundaries. Finite jumps of approximants at
these divisions have vanishing relative size in the claimed limit.

Every value in (2)--(3) is strictly positive. In the last case
u_D>=27/11 for D>=9, so u_D^2-5>0, and the derivative of
u_D^alpha-1-2alpha is positive for alpha>=2. Thus its logarithm has
argument greater than one; there is no cancellation of a negative kernel.

The qubit definition is given explicitly in Section 3. It involves only
a finite union of compact one-dimensional scalar families. Finally set

    C_(m,D)(0)=H_D,
    C_(m,D)(infinity)=log u_D                           (4)

for every m. These endpoint definitions use separately known exact quantum
results, not substitution at singular denominators.

## 3. The credited qubit reduction, kept exact instead of asymptotically guessed

For m=2, D=2n with n>=3, let A(x), B_j(x), C_j(x) be the following
normalized lists of nonnegative eigenvalues. A bracket denotes actual
integer multiplicity, and 1<=j<=D-3; write ell=D-j-2>=1.

    A(x)=(1[D-2],1-2x,x^2)/(D-1-2x+x^2),
                                      0<=x<=sqrt(2)-1;
    B_j(x)=((1+2x)[j],1[D-j-1],x^2)/(D-1+2jx+x^2),
                                      0<=x<=1;
    C_j(x)=((1+2x)[j],x^2[ell],1[2])
                       /[j(1+2x)+ell x^2+2],
                                      1<=x<=1+sqrt(2).                (5)

For a normalized list p put e_alpha(p)=log D-S_alpha(p), with the
continuous von Neumann value at alpha=1. For every finite alpha>0 define

    C_(2,D)(alpha)=max{ max_x e_alpha(A(x)),
                      max_(j,x) e_alpha(B_j(x)),
                      max_(j,x) e_alpha(C_j(x)) }.       (6)

This is an explicit scalar reduction, not a maximum over unknown APPT
states. No unconstrained real rank is substituted for j. All intervals
and normalizations remain exactly as stated.

Song--Chen, Theorem 10 (arXiv:2409.14347v1; published in Physical Review
A 112, 022409, 2025), classifies every qubit--qudit extreme point: the
rank-two APPT boundary equality holds, every middle eigenvalue is one
of the top or third-bottom eigenvalues, and at least two of the four
distinguished values coincide. We use this published theorem as an
explicit ordinary external input, not as a new formalized theorem or a
claim to have independently audited their complete paper. Their source
statement and the transformations below are part of the new review scope.

Here is the algebra from those conditions to (5). Write the four
distinguished values as a>=c>=b>=d>=0, with a=b+2sqrt(cd).
The possible adjacent equalities reduce to:

* a=c: scale a=c to 1, put x=sqrt(d), and obtain b=1-2x,
  with d<=b exactly when x<=sqrt(2)-1. This gives A.
* c=b: scale c=b to 1, put x=sqrt(d), and obtain a=1+2x,
  0<=x<=1. Top multiplicity j gives B_j.
* b=d: scale b=d to 1, put x=sqrt(c), and obtain a=1+2x,
  1<=x<=1+sqrt(2), from c<=a. This gives C_j.

At the singular boundary d=0 the only spectrum is the one-hole list,
which is already A(0)=B_j(0). Degenerate intersections and permutations
cause no problem for a value formula. This also verifies positivity,
trace one and the qubit boundary equality in (5).

For completeness, Tr f(rho) is convex on actual PSD matrices for convex
scalar f, and concave for concave f: diagonalize a matrix mixture, apply
scalar Jensen to its diagonal entries, then apply scalar Jensen again to
the spectral expansions of the two component diagonal entries. Thus a
maximum of Tr rho^alpha for alpha>1, a minimum for 0<alpha<1, and a
minimum of von Neumann entropy can be attained at an extreme point of
the actual compact convex APPT set. This uses the ordinary finite-
dimensional extreme-point principle; it does not assume operator
convexity of x^alpha for alpha>2. Conversely (5) consists of the stated
actual APPT spectra. Therefore

    C_(2,D)(alpha)=E_alpha(2,n), 0<alpha<infinity.        (7)

The qubit equality is a direct corollary of the credited classification.
It is not a new finite optimizer classification or a new solved problem.
The finitely many D<9 are irrelevant to the total-dimension limit below;
no formula for n=2 is needed to assert that limit.

## 4. Main theorem and exact quantifiers

**Theorem X.** With the explicit scalar profile (1)--(6),

    lim_(N->infinity)
      sup_(2<=m<=n, mn>=N, 0<=alpha<=infinity)
        |E_alpha(m,n)/C_(m,mn)(alpha)-1| =0.             (8)

In particular the first nonzero entropy deficit has ONE relative
approximant uniformly over all dimensions and all positive orders.
The order and dimensions may vary or oscillate with no prescribed
relation. The exact rank and min-entropy endpoints are included through
(4), separately from their positive-order limits. An equivalent epsilon
statement has one total-dimension N for all m,n,alpha at once.

No effective N(epsilon), finite exact formula for every m>=3, full
changing-order nearoptimizer classification, or general APPT=ASEP
equivalence is asserted. The one- and two-dimensional scalar maxima in
the profile remain mathematical maxima, not finite sampling instructions.
The theorem is a synthesis in the same APPT direction, not a new
independent major-conjecture solution.

The proof and exact credited dependencies follow in Sections 5--8.

## 5. Two uniform facts about the finite-m bulk function

**Lemma X1 (small width, including orders arbitrarily near zero or one).**
As m tends to infinity,

    sup_(0<alpha<=sqrt(m))
      |B_m(alpha)/[alpha/(2m^2)]-1| ->0.                (9)

For 2<=alpha<=sqrt(m) this also gives

    exp[(alpha-1)B_m(alpha)]-1
       =[alpha(alpha-1)/(2m^2)](1+o(1))               (10)

uniformly on the indicated interval.

Proof. Fix theta and t=t_m. A mean-one variable X takes the values
1/(1+t theta) and (1+t)/(1+t theta), with upper probability theta.
Thus

    |X-1|<=t, |log X|<=log(1+t)<=t,
    v_theta=E(X-1)^2=t^2 theta(1-theta)/(1+t theta)^2.

For alpha>0, alpha!=1, Taylor's integral remainder gives

    [x^alpha-1-alpha(x-1)]/[alpha(alpha-1)]
      =(x-1)^2 integral_0^1 (1-s)[1+s(x-1)]^(alpha-2) ds.

All bases here lie in [1/(1+t),1+t]. With r=(alpha+2)t, the integral
lies between exp(-r)/2 and exp(r)/2. In particular, for theta in (0,1),

    E X^alpha=1+alpha(alpha-1)v_theta/2 * K,
    exp(-r)<=K<=exp(r).                               (11)

For theta=0 or 1 both sides of the increment identity vanish. On the
complete alpha<=sqrt(m) interval, r=O(m^-1/2) and
|E X^alpha-1|=O(1/m), uniformly in theta. For negative increments the
same log(1+z)/z=1+O(|z|) estimate applies; no inequality is divided by
alpha-1 without keeping its sign. Hence

    g_q(alpha,theta)=alpha v_theta/2 * [1+O(m^-1/2)]

uniformly, for theta in (0,1). Continuity gives the alpha=1 value with
the identical bounds. Direct differentiation of v_theta gives its
unique maximum at theta=1/(t+2), with

    max v_theta=t^2/[4(1+t)]=1/(m^2-1).

Taking maxima proves (9). Furthermore
(alpha-1)B_m(alpha)=O(1/m) for alpha<=sqrt(m), so exp(z)-1=z[1+O(z)]
proves (10). This proves uniformity even for alpha tending to zero
faster than any function of m; no fixed lower bound for alpha was used.

**Lemma X2 (relative lattice accuracy on the entire bounded-order interval).**
Fix m>=3 and a finite A>0. Let

    G_(m,D)(alpha)=max_(1<=j<=D-1)g_(q_m)(alpha,j/D).

There are constants c_(m,A),D0(m,A) such that, simultaneously for
0<alpha<=A and D>=D0,

    0<=B_m(alpha)-G_(m,D)(alpha)<=c_(m,A)alpha/D^2,
    B_m(alpha)>=c'_(m,A)alpha, with c'_(m,A)>0.         (12)

Proof. Put L=log q and t=q-1, and write

    J(alpha,theta)=log[1+theta(exp(alpha L)-1)]
                                      -alpha log(1+t theta).

This is real analytic near every compact rectangle [0,A]x[0,1]. Since
J(0,theta)=J(1,theta)=0, the quotient
J/[alpha(alpha-1)]=g_q(alpha,theta)/alpha has removable analytic
extensions at 0 and 1. In particular it and its first two theta
derivatives are bounded on that rectangle. At zero its value is

    log(1+t theta)-theta log q.

Its maximum is the positive constant

    C0(m)=log[t/log q]-1+(log q)/t>0,

at theta0=(t-log q)/(t log q) in (0,1). Strict scalar Jensen gives
B_m(alpha)>0 at every positive alpha, and the closed expression for its
unique theta maximum extends continuously to theta0. Consequently that
maximizer remains a positive distance from both endpoints on [0,A].
Also B_m(alpha)/alpha is continuous and strictly positive there.

For large D a nearest rank j/D is in [1/D,1-1/D], at distance at most
1/(2D) from the continuous maximizer. Taylor in theta, whose first
derivative vanishes at that maximizer, bounds the value loss by a
constant times alpha/D^2. The opposite inequality follows because the
integer grid is a subset of the continuous interval. This proves (12).
An absolute O(1/D) entropy estimate alone would not suffice here.

## 6. The growing-m comparison, with the head contributions retained

The previously proved V2 theorem supplies an explicit profile A_old:
for 0<alpha<=sqrt(m) it is the existing U0, namely

    D^-1 max{1,1-m^(-alpha)+(alpha/2)max(4,gamma)},  alpha<1/2;
    D^-1[2alpha+(alpha/2)max(4,gamma)],             1/2<=alpha<=2;
    log{1+(u_D^alpha-1-2alpha)/D
                 +alpha(alpha-1)max(4,gamma)/(2D)}/(alpha-1),
                                                 2<alpha<=sqrt(m).

For alpha>sqrt(m), A_old is exactly log V/(alpha-1), with (1).
Its proved assertion is

    sup_(n>=m, alpha>0)|E_alpha/A_old-1| ->0 as m->infinity.   (13)

All original density/APPT definitions, both actual moment normalization
and integer-rank lower constructions remain in that credited input.
We use its complete statement, not an inference from its finite controls.

We show uniformly that C/A_old tends to one. Above sqrt(m) they are
identical. Below it use

    gamma+Z_(m,D)=max(4,gamma),
    B_m(alpha)=alpha/(2m^2) * [1+epsilon_(m,alpha)],
    sup_(0<alpha<=sqrt(m)) |epsilon_(m,alpha)| ->0.

For alpha<1/2 the second entry of the new maximum differs from the old
second entry by epsilon alpha/(2m^2). The old maximum is at least
alpha/(2m^2). The first entry changes from 1/D to H_D=(1/D)[1+O(1/D)].
The inequality

    |max(a,b)-max(c,d)|<=max{|a-c|,|b-d|}

therefore bounds relative change by o(1)+O(1/D), uniformly even as
alpha tends to zero and the winning entry changes repeatedly.

For 1/2<=alpha<=2 exactly the same bulk replacement has relative error
o(1), since A_old>=alpha/(2m^2). Both head terms remain a SUM with the
bulk term. In particular the balanced alpha=2 coefficient is eight,
not the maximum of separately optimized head and body coefficients.

For 2<alpha<=sqrt(m), let T_old denote the old positive logarithmic
increment. Its bulk term alpha(alpha-1)/(2m^2) is replaced by
exp[(alpha-1)B_m(alpha)]-1. By (10) the replacement error has magnitude
o(1) times that bulk term, which is at most T_old. The other two terms
are positive and unchanged. Hence T_new/T_old tends uniformly to one.
For all x,y>0,

    min{1,x/y}<=log(1+x)/log(1+y)<=max{1,x/y},

by the monotonicity of log(1+x)/x. This proves the relative logarithm
comparison, even when T_old tends to zero or infinity.

It follows from (13) that

    sup_(n>=m, alpha>0)|E_alpha/C_(m,D)(alpha)-1| ->0
    as m->infinity.                                    (14)

This is explicitly an application of the existing growing-m all-order
theorem plus the uniform replacements just proved. It does not claim
that the growing-m range was previously unproved.

## 7. Fixed m: uniform relative control, including the vanishing-order layer

Fix an integer m>=3. The credited exact eventual all-order theorem A
gives one D0(m) for which, for EVERY positive alpha,

    E_alpha=max{H_D,G_(m,D)(alpha),p_D(alpha)},            (15)

where p_D is the deficit of the exact pole spectrum (3,1,...,1)/(D+2).
The exact theorem includes all ranks and all equality orbits; no such
new finite equality claim is being inferred for the new profile C.

On every fixed bounded interval 0<alpha<=A,

    0<=p_D(alpha)<=C_A alpha/D.                         (16)

To verify uniformity near both zero and one, use its exact log moment
J_D(alpha)=log[(3^alpha+D-1)/D]+alpha log[D/(D+2)].
It vanishes at alpha=0 and alpha=1. Its derivatives on a fixed compact
alpha interval are O_A(1/D). Dividing by the two removable factors
alpha and alpha-1, or their integral divided differences, bounds
J_D/[alpha(alpha-1)] uniformly by C_A/D. Pole entropy is at most log D,
so p_D>=0. This proves (16) without requiring alpha away from zero.

By (12), G>=c alpha/2 for all sufficiently large D. Thus p_D<G for
every positive alpha in [0,A] at once, and (15) becomes

    E_alpha=max{H_D,G_(m,D)(alpha)}.

Lemma X2 now gives the relative assertion

    sup_(0<alpha<=A)
       |E_alpha/max{H_D,B_m(alpha)}-1|=O_(m,A)(D^-2).    (17)

Indeed the absolute lattice error is O(alpha/D^2), whereas the denominator
is at least c' alpha and at least H_D. This bound remains meaningful for
alpha exponentially smaller than 1/D. It is the needed relative
fixed-local synthesis, not a conversion of a fixed absolute error.

Compare C with (17) on 0<alpha<=sqrt(m). Eventually gamma>4, so Z=0.
Below one half, 0<=1-m^(-alpha)<=alpha log m makes the added term at most
alpha log m/D. The denominator in (17) is at least c' alpha; thus its
relative effect is O_m(1/D). On [1/2,min(2,sqrt(m))], B has a positive
minimum, H_D is eventually smaller, and 2alpha/D changes relative value
only by O_m(1/D). On [2,sqrt(m)], when this interval is nonempty, the
extra kernel in (3) is O_m(1/D), and the logarithm argument is bounded
away from one by the positive minimum of B. The same conclusion holds.
We have proved

    sup_(0<alpha<=sqrt(m))|E_alpha/C-1| ->0 as n->infinity. (18)

For completeness we next verify the larger-order branch of C uniformly
at this fixed m, instead of substituting fixed m into a growing-m theorem.
Let F_q(alpha)=exp[(alpha-1)B_m(alpha)] for alpha>1. Directly from (1),

    max{F_q(alpha),1+R_(D,alpha)}
           <=V_(m,D,alpha)<=F_q(alpha)+R_(D,alpha).      (19)

For the lower bounds use k=t_m and k=0, respectively. For the upper
bound the peak term is at most R, while the normalized two-point moment
is increasing in k at fixed theta. The latter follows because its
logarithmic derivative has the sign of
(1-theta)[(1+k)^(alpha-1)-1]>=0. This proves (19) on the whole rectangle.

Consider any sequence alpha>sqrt(m). On a bounded subsequence extract
alpha->a>=sqrt(m)>1. R tends to zero uniformly on bounded alpha ranges,
so (19) gives V/F_q->1. Equation (17), with a suitable finite A, gives
E_alpha/B_m(alpha)->1, with B bounded away from zero. Thus E/C->1.

On an unbounded subsequence take alpha->infinity, then extract
alpha/log D->c in [0,infinity]. The known fixed-local growing-order
phase theorem S2 gives

    E_alpha -> max{log q_m,log3-1/c},                    (20)

where the peak entry is -infinity at c=0 and log3 at c=infinity.
The right side is always at least log q_m>0. This original theorem
requires both alpha->infinity and D->infinity; both hold here.

The closed two-level maximum gives

    log F_q(alpha)/(alpha-1) ->log q_m.

For example, the upper bound is q_m^alpha; the lower bound uses the
legitimate CONTINUOUS scalar fraction theta=1/[t_m(alpha-1)] for all
sufficiently large alpha and yields log F_q=alpha log q_m-O_m(log alpha).
This is a scalar bound, not a finite rank construction.
Also

    log R/(alpha-1)=alpha log u_D/(alpha-1)
                                  -log D/(alpha-1).

The maximum/sum squeeze (19), with logarithmic difference at most log 2,
therefore gives C converging to the SAME positive quantity in (20),
including c=0 and infinity. Consequently E/C tends to one. Compact-
subsequence contradiction with these bounded and unbounded alternatives
proves

    sup_(alpha>sqrt(m))|E_alpha/C-1| ->0                 (21)

at every fixed m>=3. Equations (18)--(21) establish complete fixed-local
relative control on all positive orders simultaneously.

## 8. One total-dimension threshold; endpoints and limitations

Suppose (8) failed for finite positive orders. There would be epsilon>0,
dimension pairs D_j=m_j n_j->infinity and orders alpha_j>0 with relative
error at least epsilon. If m_j is unbounded, take a subsequence m_j->infinity;
(14) contradicts the error. Otherwise take a subsequence with the fixed
integer m_j=m. For m=2, (7) gives zero error exactly. For m>=3,
(18) and (21) contradict the error. These alternatives include arbitrarily
many alternations between fixed and growing smaller dimensions; no
monotonicity or eventual aspect-ratio assumption has been made.

At alpha=0 the actual rank-two APPT condition

    lambda_1-lambda_(D-1)<=2sqrt(lambda_(D-2)lambda_D)

forces all nonzero eigenvalues equal when lambda_D=0, and rules out two
zeros. The actual state (I-P)/(D-1), rank P=1, is APPT under every global
unitary because every pure P has P^Gamma<=I. Thus E_0=H_D exactly.
At infinity the known actual peak bound lambda_1<=3/(D+2) is attained
by (I+2P)/(D+2), so E_infinity=log u_D exactly. They equal (4), completing
the extended-axis assertion (8).

The new assembly retains all original quantum definitions. It uses
previous fully proved upper bounds on EVERY actual APPT state and
previous actual integer-rank constructions, rather than assigning APPT
status from a scalar sample. The profiles are relative equivalents, not
unconditional finite optimizer formulae. In particular a tiny relative
error is not a statement about convergence of all nearoptimal spectra.
Dimension/order dependent spectral rigidity is still a separate task.

The attribution in this synthesis is precise: V2 supplies the entire
growing-m theorem, A supplies the eventual fixed-m exact classification,
S2 supplies the fixed-m diverging-order phase, and Song--Chen supplies
the qubit extreme points. X1, X2, the globally specified replacement
profile and the all-dimension uniform relative conclusion are the new
claims to be read here. The known fixed-m loglog correction is not a
new claim. All old source hashes, read scopes and failures remain intact.
There is no new Lean execution or extension of a kernel audit, external
human peer review, general ASEP conclusion, submission, email, Release,
DOI, independent major-conjecture count or historical-first claim.
