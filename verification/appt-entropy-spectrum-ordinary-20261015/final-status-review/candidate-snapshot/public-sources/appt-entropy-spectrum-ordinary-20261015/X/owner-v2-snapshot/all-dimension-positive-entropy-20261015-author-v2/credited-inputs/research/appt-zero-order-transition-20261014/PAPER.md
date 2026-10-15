# The exact zero-order transition and the complete eventual low-order APPT spectrum

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID0009-0000-3864-3536.14 October2026. No external funding.
OpenAI AI assistants assisted. All rights reserved for original material.
Natural logarithms. Ordinary mathematics in the same APPT programme.

## 1. Complete statements

Fixm>=3, let every integern>=m grow, and put

    D=mn, R=m(m-1)/2, K=m(m+1)/2,
    q=(m+1)/(m-1), t=q-1, L=lnq,
    theta0=(t-L)/(tL), l0=L/t, h0=qL/t,
    C0=ln(t/L)-1+L/t>0,
    C1=C0-theta0(1-theta0)L^2/2,
    beta_star=1/C0.                                      (Z0)

All states below are actual trace-one positive complex matrices on
C^m tensor C^n, APPT under EVERY global unitary conjugation. Write
e_alpha(rho)=lnD-S_alpha(rho), E_D(alpha)=max_(actualAPPT)e_alpha(rho).
For alpha>0 use spectral Renyi entropy, with its vonNeumann value at1;
S_0=ln rank. The maximum exists for positive orders by compactness and
continuity; the rank endpoint is attained explicitly below.

Let

    H_D=ln[D/(D-1)],
    g_r(alpha,theta)=
      [ln(1+theta(r^alpha-1))-alpha ln(1+(r-1)theta)]/(alpha-1),
    g_r(1,theta)=theta r lnr/[1+(r-1)theta]-ln[1+(r-1)theta],
    g_r(0,theta)=0,
    G_D(alpha)=max_(1<=k<=D-1)g_q(alpha,k/D).              (Z1)

For alpha>0 the continuous maximizing fraction is

    theta_alpha=(q^alpha-1-alpha t)/[t(alpha-1)(q^alpha-1)], alpha!=1,
    theta_1=(qL-t)/t^2,
    theta_alpha->theta0 as alpha->0.                     (Z2)

The maximizing integer ranks are the exactly winning members of
{floor(D theta_alpha),ceil(D theta_alpha)}, clipped to[1,D-1] if needed.
At the eventual dimensions used here no clipping is needed. Retain ties.

**Theorem Z1.** For each0<c<1/ln(m-1) there is D0(m,c) such that every
actualn withD>=D0 and EVERY real0<=alpha<=c lnD satisfy

    E_D(alpha)=max{H_D,G_D(alpha)}.                       (Z3)

All equality states are exactly the following, whenever their displayed
deficit attains that maximum:

    (I-P)/(D-1), rankP=1,                                deficitH_D;
    (I+tP)/(D+tk), rankP=k maximizingG_D(alpha),          deficitG_D.
                                                               (Z4)

At0 only the one-hole family wins. At positive-order ties both listed
unitary-orbit families occur; no nontrivial mixture is another minimizer.
This closes the fixed positive lower bound missing from the inherited
exact-eventual-bulk theorem. It is still an EVENTUAL fixedm theorem,
not an exact formula in all finite dimensions or in joint growingm.

**Theorem Z2.** At largeD there is a UNIQUE crossing tau_D>0 with
G_D(tau_D)=H_D. Below it the one-hole spectrum is the unique decreasing
minimizing spectrum; above it and throughout Z1's band only the selected
bulk spectra minimize. At the crossing Z4 gives all equality states.

    tau_D=1/(C0 D)+[1/(2C0)-C1/C0^3]/D^2+O_m(D^-3).     (Z5)

Its exact definition retains integer ranks. The first two terms are
unaffected by integer rounding; the next remainder may depend on it.

**Theorem Z3.** For every finiteB, uniformly over0<=beta<=B,

    D E_D(beta/D)=max{1,beta C0}+O_(m,B)(1/D).            (Z6)

Furthermore, for EVERY sequence epsilon_D->0,

    sup_(0<=alpha<=epsilon_D)
      |E_D(alpha)/max{1/D,alpha C0}-1| ->0.              (Z7)

In particular this covers every alpha_D->0, including exact zero orders
and arbitrary rates relative to1/D. No pointwise-limit exchange is used.

**Theorem Z4 (complete leading spectral classification).** Consider any
actualAPPT statesrho_D and ordersalpha_D>=0 withDalpha_D->beta<infinity.
Let y_i=Dlambda_i decrease, a_D=y_D, nu_D=D^-1 sum_i delta_(y_i), and

    mu0=(1-theta0)delta_l0+theta0 delta_h0,
    w_D=a_D^alpha_D ifalpha_D>0,
        1_(a_D>0) ifalpha_D=0.                          (Z8)

Let W1 be the usual one-dimensional probability distance on[0,3],
equivalently the integral of the absolute difference of cumulative
distribution functions. Scaled near-optimality means

    D[E_D(alpha_D)-e_(alpha_D)(rho_D)] ->0.              (Z9)

It holds if and only if

    w_D->0,                                  beta<beta_star;
    W1(nu_D,mu0)->0,                          beta>beta_star;
    min{w_D,W1(nu_D,mu0)}->0,                 beta=beta_star. (Z10)

On a hole branch, a_D->0 and all other y_i converge uniformly to1.
On a bulk branch, the extreme eigenvalues also obeya_D->l0,y_1->h0;
there are no fixed-height endpoint outliers. At the critical value the
two branches may alternate; no single limiting branch is required.
For beta>0 the hole condition requires alpha_D ln(1/a_D)->infinity
for positivea_D, or exacta_D=0. An ordinary exponential hole with
a_D=exp(-sD), fixeds>0, does not reach the hole optimum.

The credited one-hole/projection spectra and old scalar optimization
are known inputs. The new content is their full actual-set exact
low-order selection, small-order crossing, and leading classification.
No ASEP bulk attainment or new Lean coverage is asserted.

## 2. Actual ranktwo tests, singularity and a strict hole comparison

Assignlambda_1 to an antisymmetric two-Schmidt Bell vector,
lambda_(D-1) to its symmetric partner, andlambda_D,lambda_(D-2) to
the two diagonal directions. Testing a real two-Schmidt unit vector
gives the necessary positive quadratic form

    lambda_D x^2+lambda_(D-2)y^2
                 -(lambda_1-lambda_(D-1))xy>=0.         (Z11)

Consequently

    lambda_1-lambda_(D-1)<=2sqrt(lambda_(D-2)lambda_D),
    lambda_1<=lambda_(D-2)+lambda_(D-1)+lambda_D,
    lambda_1<=3/(D+2).                                 (Z12)

For the last bound putb=lambda_(D-2). The last three sum is at least
lambda_1 and at most3b, while the otherD-4 middle coordinates are
at leastb. Thus1>=2lambda_1+(D-4)b>=(D+2)lambda_1/3.
Atlambda_D=0, Z11 forceslambda_1<=lambda_(D-1): all firstD-1
eigenvalues equal1/(D-1). There is no smaller APPT rank.
Conversely(I-P)/(D-1) is actually APPT for every rankone projector:
the partial-transpose eigenvalues of a pure projector are Schmidt
squares and signed pair products, all at most1, after every unitary.
This proves the known rank endpoint and its full equality statement.

Normalizey_i=Dlambda_i anda=y_D in[0,1]. The mean of the firstD-1
coordinates ismu=(D-a)/(D-1)>=1. Z12 gives their spread at most
2sqrt(3a), hence

    max_(i<D)|y_i-mu|<=2sqrt(3a),
    max_(i<D)|y_i-1|<=2sqrt(3a)+1/(D-1).                 (Z13)

Take0<alpha<=1/2 andbeta=Dalpha. If0<a<=1/48 andD>=3, those
coordinates andmu lie in[1/2,2]. Since| (x^alpha)'' |<=4alpha there,
Taylor about the ACTUAL mean and cancellation of the linear terms give

    sum_(i<D)y_i^alpha>=(D-1)mu^alpha-24alpha(D-1)a.     (Z14)

Let M=D^-1 sum y_i^alpha andM_h=((D-1)/D)(D/(D-1))^alpha.
Because0<alpha<=1 andmu>=1, the decrease frommu0=D/(D-1) tomu
costs at mostalpha a/(D-1) per power of the mean. Retaining the final
positive power separately gives

    M-M_h>=[a^alpha-alpha a-24Dalpha a]/D
           >=[a^alpha-25beta a]/D.                     (Z15)

Choose once for fixedm

    delta_bar=min{1/48,1/[2(m+1)],1/(4q)},
    delta(beta)=min{delta_bar,(1+50beta)^(-2)}.          (Z16)

For0<a<=delta(beta), a^alpha>=sqrt(a) and25beta a<sqrt(a)/2.
ThusM>M_h: every such full-rank actual state has STRICTLY greater
entropy than the one-hole state. All trace and normalization terms
were retained in Z14-Z15. Atalpha=0 the comparison is just the strict
rank difference. At a=0 the actual singular classification already applies.
An exact minimizer at0<alpha<=1/2 is therefore either the one-hole
state or has a>delta(beta).

## 3. Complete vertices of the floor-cut outer polytope

The maximalm-Schmidt physical witness gives the necessary inequality

    h(lambda)=sum_(bottomK)lambda-sum_(topR)lambda>=0.  (Z17)

Its pure-projector partial transpose hasR negative andK positive
eigenvalues of size1/m; global-unitary freedom permits the extremal
assignment. LetOmega_delta be the ordered probability simplex with
Z17 andlambda_D>=delta/D, where0<delta<=delta_bar.
This is a necessary relaxation only. Actual regular competitors lie in it.

The ordered simplex has the unique gap representation
lambda=sum x_i u_i, x_i=i(lambda_i-lambda_(i+1)), sum x_i=1.
Imposinglambda_D>=delta/D is exactlyx_D>=delta. Its new simplex
vertices arev_i=delta u_D+(1-delta)u_i,1<=i<=D, withv_D=u_D.
For D>=2m^2, the unshifted halfspace values are

    h(u_i)=-1, i<R;
           -R/i, R<=i<=D-K;
           (i-D+m)/i, D-K<i<=D.                        (Z18)

Nowh(v_i)=delta m/D+(1-delta)h(u_i). They are strictly negative
fori<D-m: h(u_i)<=-1/D and(m+1)delta<1. They are strictly positive
fori>=D-m, including the old zero-sign vertex. ThusOmega_delta has
exactly the survivingv_j,j=D-s,0<=s<=m, and every opposite-sign edge
cut[v_i,v_j],i<D-m<=j. A support perturbation preserving trace and
h eliminates every other candidate: off the cutting plane two positive
gap coordinates suffice; on it three suffice. Size-two boundary supports
must have opposite signs and give the unique extreme cut. This also
proves completeness at the coordinate floor, with no missing zero-sign case.

An edge-cut spectrum has normalized levels

    a on its firsti coordinates,
    b on its nextj-i coordinates,
    delta on its lasts=D-j coordinates,                 (Z19)

wherea>b>=delta, trace one andh=0 determine them. The supportwise mean is
mu=(D-sdelta)/(D-s)=1+O_m(1/D), uniformly even when delta varies.
Setr=a/b andtheta=i/j. The three negative-index regimes give

    i<R:       i(a-b)=(m-s)b+sdelta,              r<=m+1;
    R<=i<=D-K: R a=(K-s)b+sdelta,                r<=q;
    i>D-K:     (ell-m)a=(ell-s)b+sdelta,
               ell=D-i in[m+1,K-1],              r<=m+1. (Z20)

For a middle cut withs>=1, the maximuma is at least1, so b>=1/q.
Hence

    r=q-(s/R)(1-delta/b)<=q-1/(2R)=:r_star<q.          (Z21)

For a middle cut withs=0, the cutting point is precisely the old full
q-bulk spectrum, independent ofdelta. Its smallest normalized value is
at least1/q>delta, so all these original vertices survive the floor.
Early and late cuts have respectivelytheta=O_m(1/D) and1-theta=O_m(1/D).
The survivingv_j have onlys<=m floor coordinates and otherwise a
value1+O_m(1/D). These exhaust all vertices.

Every point ofOmega_delta also has a uniform normalized upper bound:
withb'=lambda_(D-K+1), Z17 implieslambda_1<=(m+1)b', while
b'<=1/(D-K+1). ThusDlambda_1<=2(m+1) forD>=2K.

## 4. Uniform rescaled scalar gaps, with two distinct floor regimes

Define

    C_r(theta)=ln(1+(r-1)theta)-theta lnr,
    C(r)=max_theta C_r(theta),
    B_r(alpha)=max_theta g_r(alpha,theta).               (Z22)

The functiong_r/alpha extends smoothly toalpha=0 with valueC_r,
uniformly onr in[1,m+1],theta in[0,1],alpha in[0,1/2]. Its endpoints
intheta are0 and its theta derivative is uniformly bounded. Consequently
early and late cuts satisfyg_r<=C_m alpha/D. Forr>1, C_r strictly
increases withr at each interior theta; explicitly

    partial_r C_r=theta(1-theta)(r-1)/
                         [r(1+(r-1)theta)]>0.          (Z23)

The analogous strict derivative ofg_r holds foralpha>0. Therefore
the positive constants

    b0=min_(0<=alpha<=1/2) B_q(alpha)/alpha>0,
    gamma0=min_(0<=alpha<=1/2)
                  [B_q(alpha)-B_(r_star)(alpha)]/alpha>0 (Z24)

use the removablealpha0 values. The maximizing bulk fraction stays
in a fixed interior interval here. Neighboring integer ranks lie in
[R,D-K] for largeD and their deficit is at leastB_q(alpha)-C_m alpha/D^2.
The alpha factor is retained: this comparison works for arbitrarily tiny
positive orders, not just orders bounded away from zero.

First take a FIXED positive floor delta and a fixed finiteB. All normalized
eigenvalues inOmega_delta lie in[delta,2(m+1)], so uniformly there

    e_alpha/alpha=-D^-1 sum ln y_i+O_(m,delta)(alpha),
                                                  0<alpha<=B/D. (Z25)

For the edge cut Z19 its logarithmic objective is

    -D^-1 sum ln y_i
      =(j/D)[C_r(theta)-lnmu]-(s/D)lndelta.             (Z26)

Thus every nonbulk middle vertex has value at mostC(r_star)+O(1/D),
and early, late and surviving vertices have valueO(1/D). The uniform
gapC(q)-C(r_star)>0 and the positiveC(q) exclude all of them compared
to a rounded bulk vertex, simultaneously for all0<alpha<=B/D.

Second allow delta to vary arbitrarily in(0,delta_bar] and takebeta=Dalpha
large, still0<alpha<=1/2. Do not use logarithms of a vanishing floor.
The normalized power moment of Z19 satisfies the direct bound

    M=(j/D)mu^alpha
        [1+theta(r^alpha-1)]/[1+(r-1)theta]^alpha
                          +(s/D)delta^alpha
      >=(j/D)[1+theta(r^alpha-1)]/[1+(r-1)theta]^alpha. (Z27)

Since1-alpha>=1/2, its deficit is at mostg_r(alpha,theta)+C_m/D.
Survivingv_j satisfy the sameC_m/D bound. Therefore every nonbulk
middle vertex has deficit at mostB_(r_star)(alpha)+C_m/D, and every
other nonbulk vertex at mostC_m alpha/D+C_m/D. Divide byalpha:
the additional term is at mostC_m/beta. Choose a finiteB0(m) large
enough that this is smaller than a fixed fraction of both constants
in Z24, and also B0 b0/2>2. For all largeD, everybeta>=B0 and
0<alpha<=1/2, every nonbulk vertex is STRICTLY worse than a rounded
q-bulk vertex, uniformly over ALL allowed floors. The rounded bulk
deficit is greater thanH_D<=2/D as well.

## 5. Exact full-physical selection and all equality states

Forbeta<=B0, use the constant floor delta=delta(B0). Z15 excludes
every full-rank actual state witha<=delta. For the others, Section4's
fixed-floor argument applies withB=B0 and selects only bulk vertices.
Forbeta>=B0 andalpha<=1/2, use the varying floor delta(beta). Z15
again excludes all small-minimum competitors, while the direct-moment
argument selects the bulk and proves it better than the one-hole state.

On each floor-cut polytope, for0<alpha<1 minimizing entropy is minimizing
the strictly concave power sum. A nontrivial convex combination of distinct
vertices has strictly greater power sum than the minimum. Thus no nonvertex
can be another minimizer. For completeness, all bulk spectra are actually
APPT: the total absolute negative eigenvalue sum of a unit-Schmidt
pure-projector partial transpose is at most(m-1)/2. A conjugated
projection has diagonal weights in[0,1], so every unitary conjugate of
I+tP has nonnegative partial-transpose quadratic forms. Normalize its
trace. This holds for every integer projection rank.

We have proved Z3-Z4 for ALL0<=alpha<=1/2 at sufficiently largeD.
For1/2<=alpha<=c lnD, apply the inherited ordinary F2 of
../appt-eventual-bulk-20261014/PAPER.md with fixed lower order1/2.
It supplies the full actual-set bulk optimum and all equality states on
that entire positive-order band. The known one-hole deficit cannot win
there. This proves Z1, including orders approaching or equal to0.
The inherited source is frozen and independently completely read; this
ordinary use does not extend any Lean audit or claim its theorem as new.

## 6. Unique crossing and the exact small-order expansion

For each nonuniform positive bulk spectrum, ln(D^-1 sum y_i^alpha)
is strictly convex inalpha: its second derivative is the positive
variance oflny under the tilted positive weights. Its value at1 is0.
The secant slope through1, namelyg_q(alpha,k/D), is therefore strictly
increasing inalpha, including its continuous values at0 and1. A finite
maximum of these strictly increasing functions is strictly increasing
and continuous. G_D(0)=0; at fixed positive order its limit is positive,
whereasH_D->0. This proves existence and uniqueness of tau_D.

The removable expansion at0 is

    g_q(alpha,theta)
      =alpha C_q(theta)
       +alpha^2[C_q(theta)-theta(1-theta)L^2/2]+O_m(alpha^3),
                                                               (Z28)

uniformly intheta. C_q has the unique maximizer theta0 in(0,1),
withC_q''(theta0)=-L^2. The explicit Z2 fraction is smooth at0.
At its maximum

    B_q(alpha)=alpha C0+alpha^2 C1+O_m(alpha^3),
    0<=B_q(alpha)-G_D(alpha)<=C_m alpha/D^2.             (Z29)

The last bound follows from a theta-second-derivative bound on g_q/alpha
and its stationary first derivative, not an unscaled O(1/D) rounding error.
Comparing orders1/(2C0D) and2/(C0D) shows tau_D lies between them at
largeD. Substitution ofH_D=1/D+1/(2D^2)+O(D^-3) in Z29 gives
C0 tau_D+C1 tau_D^2=1/D+1/(2D^2)+O(D^-3). Solving successively proves Z5.

Forbeta in[0,B], Z29 and Z3 give the uniform Z6, includingbeta0 by
the rank endpoint. More generally, for0<=alpha<=1/2,

    |E_D(alpha)-max(1/D,alpha C0)|
             <=C_m[D^-2+alpha^2+alpha D^-2].            (Z30)

Dividing bymax(1/D,alpha C0) bounds the relative error by
C'_m(D^-1+alpha+D^-2). This proves Z7 with its actual uniform quantifier.

## 7. Near-optimal hole depth and the full bulk law

For boundedbeta=Dalpha and a_D->0, Z13 makes all other normalized
coordinates uniformly flat. Taylor about1, retaining their total
deviation1-a_D, gives

    M=1-(1-a_D^alpha)/D+O_B(a_D/D+D^-2),
    D e_alpha(rho)=1-w_D+O_B(a_D+D^-1).                 (Z31)

The statement includesalpha=0 with the rank-indicator convention in Z8:
a positive minimum gives rankD and deficit0; a zero minimum gives the
one-hole spectrum andD H_D=1+O(1/D). For positive orders, the moment
remainder follows fromsum_(i<D)(y_i-1)^2<=C D a_D+C/D andalpha<=B/D.
Ifw_D->0 thena_D->0, sincea_D^alpha>=a_D at eventualalpha<=1.

If instead a_D>=delta>0, all normalized eigenvalues are in[delta,3],
and uniformly for boundedbeta

    D e_alpha(rho)=beta G(rho)+o(1),
    G(rho)=-D^-1 sum ln y_i.                            (Z32)

To classify G->C0, use the actual common pivotb=lambda_(D-K+1),
z_i=lambda_i/b ands=D^-1 sum z_i. The maximal-Schmidt inequality implies
z_R<=q; the ranktwo test impliesz_1<=3. Thus except the fixedR-1 heads
andK bottom slots, all z_i lie in[1,q]. Their means0=1+t theta obeys
s=s0+O_m(1/D). With the positive minimum, exceptional logarithms are
uniformly bounded. Define the nonnegative strict chord gap

    d_q(z)=lnz-[(z-1)/t]L, z in[1,q],
    G=C_q(theta)-mean_middle d_q(z)+O_(m,delta)(1/D).   (Z33)

The gap vanishes exactly at1 andq. Therefore G->C0 if and only if
theta->theta0 and the mean gap tends to0. Compactness then forces the
middle empirical measure onto those endpoints, with the unique weights
fixed by its mean. Rescaling bys->t/L yieldsnu_D->mu0 inW1.

Conversely, empirical convergence to mu0 forces endpoint rigidity using
the actual Z17, without assuming it. Positive proportions nearh0 andl0
give y_R>=h0-o(1) andp=y_(D-K+1)<=l0+o(1). Then

    y_1<=Kp-(R-1)y_R<=h0+o(1),
    y_D>=R y_R-(K-1)p>=l0-o(1),                        (Z34)

becauseK l0=R h0. Sorting supplies the opposite bounds. Hence all y
eventually lie in a compact positive interval and logs are continuous
there, provingG->C0 fromnu_D->mu0. This proves both the necessity and
sufficiency of the bulk law, and the stated extreme-eigenvalue limits.

## 8. The three leading branches, including alternating critical sequences

Ifbeta<beta_star, a subsequence with the minimum bounded below has
limsupD e<=beta C0<1 by Z32-Z33. Near-optimal states must therefore have
a_D->0, and Z31 makes Z9 equivalent tow_D->0. This also coversbeta0
and exact zero orders.

Ifbeta>beta_star, any subsequence witha_D->0 has limsupD e<=1<beta C0.
Thus the minimum is bounded below. Z32-Z34 make Z9 equivalent to
the bulk empirical law, with all endpoint consequences in Z10.

Atbeta=beta_star, take any subsequence on which
min(w_D,W1(nu_D,mu0)) stays positive. A further subsequence either has
a_D->0, when Z31 and near-optimality forcew_D->0, or has a positive
minimum lower bound, when Z32-Z34 forceW1->0. Both are contradictions.
Conversely, if the displayed minimum tends to0, any subsequence can
be split into the hole option or the bulk option, and the corresponding
Z31 or Z32-Z34 givesD e->1. This proves the critical equivalence and
does not demand eventual residence in one branch.

Both branches are physically attained: the one-hole state and actual
integer bulk ranks nearDtheta0 suffice, including their arbitrary
alternation atbeta_star. Full-rank hole approximants are also actual:
(I-(1-epsilon)P)/(D-1+epsilon),rankP1,0<epsilon<=1. Their partial
transposes are positive under every global unitary becauseP^Gamma<=I.
Foralpha=beta/D, beta>0, epsilon=exp(-sD) givesw_D->exp(-s beta),
soD e->1-exp(-s beta)<1. Choosing epsilon=exp(-D^2) instead gives
w_D->0. These distinguish physical near-attainment from exact equality.

## 9. Attribution, evidence and unfinished domains

The known singular/pole/projection spectra, ranktwo criteria and earlier
positive-order scalar formulas retain their attribution. The previous
full-axis O(1/D) theorem did not resolve this1/D window or exact low-order
optimization; the exact-eventual-bulk theorem excluded orders tending to0.
The new floor-cut/physical-hole argument closes those particular gaps.
Finite diagnostics are supporting identities and deliberate wrong-extension
controls, not a proof of the quantified optimization or infinite limits.
Internal independent AI review is not external human peer review.
No Lean, audit-root expansion, submission, Release or DOI is implied.
Every statement keepsm fixed. Arbitrary finite dimensions, smallest onset,
ASEP bulk, joint growingm and the actual high-order critical optimizer
transition remain separate. This is not a new independent major conjecture.
