# Exact eventual bulk entropy and all minimizing spectra for actual APPT states

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID0009-0000-3864-3536.14 October2026. No external funding.
OpenAI AI assistants assisted. All rights reserved for original material.
Natural logarithms. Ordinary mathematics; same APPT programme.

## 1. Actual objects and complete conclusions

Fix an integer m>=3. For each integer n>=m write D=mn and

    R=m(m-1)/2, K=m(m+1)/2, q=(m+1)/(m-1), t=q-1,
    sigma_m=1/ln(m-1).                                      (F0)

APPT means an actual positive semidefinite trace-one complex matrix on
C^m tensor C^n whose partial transpose remains positive under EVERY global
unitary conjugation. For alpha>0 use the usual spectral Renyi entropy
S_alpha=ln(Tr rho^alpha)/(1-alpha), with S_1=-Tr rho lnrho.
No sampled orbit or caller-supplied Schmidt interface replaces this condition.

For r>=1 and0<=theta<=1 put

    g_r(alpha,theta)=
      [ln(1+theta(r^alpha-1))-alpha ln(1+(r-1)theta)]/(alpha-1),
    g_r(1,theta)=theta r lnr/[1+(r-1)theta]-ln[1+(r-1)theta],
    B_r(alpha)=max_(0<=theta<=1)g_r(alpha,theta).              (F1)

These are smooth through alpha=1 on every compact positive order interval.
For r=q>1 the unique maximizing theta is

    theta_alpha=(q^alpha-1-alpha t)/[t(alpha-1)(q^alpha-1)],
                                                alpha!=1,
    theta_1=(q lnq-t)/t^2.                                  (F2)

Let C_D(alpha) be the set consisting of floor(D theta_alpha) and
ceil(D theta_alpha), with duplicates removed. Let T_D(alpha) be those k
in C_D(alpha) that maximize the EXACT value g_q(alpha,k/D).

**Theorem F1 (compact orders).** For every0<a<=A<infinity there is
D0(m,a,A) such that all actual n>=m with D>=D0, and every real
alpha in[a,A], satisfy

    min_(actual APPT_(m,n))S_alpha
      =lnD-max_(k in C_D(alpha))g_q(alpha,k/D).              (F3)

All equality states, and only those states, have the form

    rho=(I+tP)/(D+tk), P an orthogonal projection,
                              rankP=k in T_D(alpha).       (F4)

In particular the equality classification is at the matrix level, allowing
every global unitary orbit, and every minimizer is full rank. Both adjacent
integer ranks are compared; possible ties are retained. No fixed rounding
rule such as choosing the nearest integer or always choosing the ceiling
is asserted at an arbitrary real order.

**Theorem F2 (logarithmically growing orders).** For every a>0 and
0<c<sigma_m there is D0(m,a,c) such that F3-F4 hold simultaneously for
ALL real a<=alpha<=c lnD and all actual n with D>=D0.

**Theorem F3 (a sharp limit of this relaxation).** If c>sigma_m and
alpha=c lnD, the one-Schmidt-halfspace relaxation used below has a
nonAPPT single-spike spectrum with a strictly smaller entropy than every
q-bulk projection state at all sufficiently large D. Thus sigma_m is the
sharp leading logarithmic coefficient for eventual bulk optimality of
THIS relaxation. It is not the actual APPT pole transition.

**Corollary F4 (rounding error).** On each interval[a,A] as in F1, let
d_D(alpha)=dist(D theta_alpha,Z) and put

    J_alpha=t(q^alpha-1)/
       [(1+theta_alpha(q^alpha-1))(1+t theta_alpha)]>0.       (F5)

The formula includes alpha=1, where J_1=t^2/(1+t theta_1)^2.
Uniformly on the interval,

    lnD-min S_alpha
       =B_q(alpha)-J_alpha d_D(alpha)^2/(2D^2)+O_(m,a,A)(D^-3).
                                                                  (F6)

The exact integer selection remains F3, including near a half-integer.
The scalar constant and alpha1 stationary rank are credited to
Ahiable--Kothakonda--Winter2608.03390v2, Theorem6.10, which optimizes
their inscribed polytope. Theorems F1-F2 instead establish eventual EXACT
optimization over the full actual APPT set. They do not assert every
finite dimension, joint growingm, orders tending to0 without a fixed
positive lower bound, an ASEP bulk result, or the smallest possible D0.

## 2. A necessary physical halfspace and every one of its vertices

An m-Schmidt maximally entangled unit vector has a partially transposed
projector with R eigenvalues-1/m, K eigenvalues+1/m, and D-m^2 zeros.
Assigning the largest R eigenvalues of an actual state to the negative
directions and the smallest K to the positive directions by a global
unitary gives the necessary APPT condition

    h(lambda):=sum_(i=D-K+1..D)lambda_i
                        -sum_(i=1..R)lambda_i>=0.          (F7)

Let Omega be the ordered probability simplex cut by F7. This is an OUTER
relaxation, not a claimed sufficient spectral test. The argument is the
same actual witness as the earlier ordinary EXACT_RECTANGULAR.md purity
proof; no part of that purity theorem is reproved as a new result here.

Set lambda_(D+1)=0 and let u_i be uniform on its first i coordinates.
The unique affine gap coordinates of the ordered simplex are

    x_i=i(lambda_i-lambda_(i+1))>=0,
    sum_i x_i=1, lambda=sum_i x_i u_i.                   (F8)

For D>=2m^2 the halfspace values are

    h(u_i)=-1,                          1<=i<R,
           -R/i,                        R<=i<=D-K,
           (i-D+m)/i,                   D-K<i<=D.       (F9)

Thus all surviving old vertices are u_(D-s),0<=s<=m; u_(D-m) is exactly
on the cutting plane. Every other vertex is an edge cut between a
negative u_i,1<=i<D-m, and a positive u_j,j=D-s,0<=s<m.

For completeness, if h>0 and at least two gap coordinates are positive,
one may perturb two of them with opposite signs and sufficiently small
amplitude, retaining h>0 and trace one. If h=0 and at least three are
positive, solve the two homogeneous constraints sum dx=0 and
sum h(u_i)dx_i=0 for a nonzero supported perturbation; sufficiently small
positive and negative amplitudes remain feasible. Such points are not
vertices. A size-two support on h=0 requires opposite halfspace signs
unless both vanish; there is only one zero-sign u_i. Opposite signs
give the unique cut point. Each such point is extreme because any
feasible decomposition has the same size-two support and zero h, forcing
the same weights. Surviving size-one supports are extreme. This proves
the complete list, including boundary and zero coordinates. The elementary
finite-polytope convex-hull theorem gives a decomposition into these vertices.

Write h(u_i)=-A_i/i, h(u_j)=B_s/j, where B_s=m-s>0. The cut weight on
u_i is iB_s/(iB_s+jA_i). The resulting spectrum has

    (A_i+B_s)/(iB_s+jA_i),                i copies,
    A_i/(iB_s+jA_i),                      j-i copies,
    0,                                    s copies.         (F10)

Its exact entropy deficit is

    lnD-S_alpha=ln(D/j)+g_(1+B_s/A_i)(alpha,i/j).             (F11)

This follows by direct normalization; zero coordinates contribute0 to
each positive power and to xlnx. In particular the finite support loss
ln(D/j) is retained at every positive order, including alpha=1.

## 3. Scalar strictness, all competitor regimes, and compact uniformity

For r>1, write b=r-1 and Q=r^alpha. The unique continuous maximizing
theta is the version of F2 with q replaced by r. Indeed

    partial_theta g_r
      =b(Q-1)(theta_alpha(r)-theta)/
                     [(1+theta(Q-1))(1+b theta)],          (F12)

also at alpha=1 by its removable limit. The endpoints of g_r are0 and
strict Jensen gives g_r>0 in the interior, so this unique theta lies
strictly in(0,1). F12 proves strict increase before theta and strict
decrease afterwards. The formulas are continuous through alpha=1.

For alpha!=1, direct differentiation in the ratio gives

    partial_r g_r=
      alpha theta(1-theta)(r^(alpha-1)-1)/
      [(alpha-1)(1-theta+theta r^alpha)(1-theta+theta r)]>0,
                                         0<theta<1.       (F13)

At alpha=1 the derivative is theta(1-theta)lnr/(1-theta+theta r)^2>0.
Thus B_r(alpha) strictly increases with r>1 at every alpha>0: evaluate
the larger ratio at the smaller ratio's interior maximizer. These maxima
are continuous in alpha by compactness and the smooth formulas.

Fix I=[a,A] with a>0. On the compact set
I times[1,m+1] times[0,1], the theta derivative of g_r is bounded,
including alpha=1 and r=1. Denote a bound by M. Consequently

    |g_r(alpha,theta)|<=M min(theta,1-theta)               (F14)

uniformly there, since both endpoints are0. Negative indices have three
exhaustive regimes:

* If i<R, then A_i=i and 1+B_s/A_i<=m+1. Here i/j=O_m(1/D).
  F11-F14 make every such deficit O_(m,a,A)(1/D).
* If R<=i<=D-K, then A_i=R. With s=0 the ratio is exactly q and j=D:
  these are the full-support q-bulk vertices. With1<=s<m the ratio is
  q_s=1+(m-s)/R<q, and the deficit is at most B_(q_s)(alpha)+O_m(1/D).
* If D-K<i<D-m, put ell=D-i, so m+1<=ell<=K-1 and A_i=ell-m>=1.
  Again the ratio is at most m+1. Now1-i/j=(ell-s)/(D-s)=O_m(1/D),
  and the deficit is O_(m,a,A)(1/D).

The surviving u_(D-s) have deficit ln[D/(D-s)]=O_m(1/D), too.
All these bounds hold for the entire fixed interval, not pointwise in alpha.

Continuity and strictness give the strictly positive constants

    b0=min_(alpha in I)B_q(alpha)>0,
    Delta=min_(alpha in I,1<=s<m)[B_q(alpha)-B_(q_s)(alpha)]>0,
    zeta=min_(alpha in I)min(theta_alpha,1-theta_alpha)>0.  (F15)

The neighboring integer ranks of D theta_alpha belong to[R,D-K] for all
large D, uniformly on I. Evaluating at one of them and using F14 gives
a q-bulk vertex with deficit at least B_q(alpha)-M/D. Choose one D0
large enough that this loss and every O(1/D) above are smaller than
min(b0,Delta)/4. Then every nonbulk Omega vertex has STRICTLY smaller
deficit than a bulk vertex, at every alpha in I. Among the bulk vertices,
F12 restricts every maximizing integer rank to C_D(alpha). This proves
the exact vertex optimization, with uniform quantifiers.

## 4. Physical attainment and the full equality classification

For any unit vector with Schmidt coefficients s_l, the negative eigenvalues
of the partial transpose of its projector are-s_l s_v,l<v. Their total
absolute sum is

    sum_(l<v)s_l s_v=[(sum_l s_l)^2-1]/2<=(m-1)/2.         (F16)

For every projection P' the diagonal weights in this eigenbasis lie in[0,1],
so Tr(P' (|psi><psi|)^Gamma)>=-(m-1)/2. Therefore

    <psi,(I+tP')^Gamma psi>>=1-t(m-1)/2=0.                (F17)

This holds for every unit psi and every unitary conjugate P' of any given
projection P. Positivity and trace normalization of I+tP are immediate.
Hence every rank-k bulk spectrum is an actual all-unitary APPT spectrum.
This repeats the disclosed elementary projection construction, not a
claim of a newly discovered physical family.

At alpha>1, minimizing S_alpha is maximizing the strictly convex function
sum lambda_i^alpha. At0<alpha<1 it is minimizing the strictly concave
sum lambda_i^alpha. At1 the entropy itself is strictly concave. All three
strictness statements hold on the full nonnegative simplex, including zeros.
If a point of Omega is not a vertex, a nontrivial convex combination of
distinct vertices has strictly inferior objective to the optimum. It cannot
be an entropy minimizer. Sections2-3 therefore classify ALL optimizing
decreasing spectra of Omega as exactly the selected bulk vertices.
Every actual APPT spectrum lies in Omega, and F16-F17 show that every
selected vertex belongs to the actual APPT set. Thus the outer optimum
equals the actual optimum, and the same equality classification applies.
The spectral theorem gives exactly F4. This completes F1 without assuming
that all other vertices of the relaxation are actual APPT.

## 5. Exact bulk optimality up to a logarithmic order band

Only alpha above a fixed A0>=2 needs an additional argument; Section3
already treats[a,A0]. For r>1 define the continuous maximum power moment

    F_r(alpha)=max_theta [1+theta(r^alpha-1)]/[1+(r-1)theta]^alpha.

From F2 and alpha theta_alpha(r)->1/(r-1), its exact asymptotic is

    F_r(alpha)~r^alpha/[e(r-1)alpha], alpha->infinity.     (F18)

Indeed the maximizing numerator is asymptotic to r^alpha/[(r-1)alpha],
and its denominator tends to e. Since only q and the finitely many q_s
are needed, constants can be chosen so for every alpha>=A0

    F_q(alpha)>=C1 q^alpha/alpha,
    F_(q_s)(alpha)/F_q(alpha)<=C2(q_s/q)^alpha.            (F19)

Here and below C1>0 and every upper constant depend only on fixedm.
These are eventual scalar bounds, not an assumption on the actual optimum.

For the cut F10 the power moment normalized to dimension D is exactly

    M_D=(D/j)^(alpha-1)
            [1+(i/j)(r^alpha-1)]/[1+(r-1)i/j]^alpha.     (F20)

For a surviving uniform vertex it is(D/(D-s))^(alpha-1).
For a fixed band alpha<=c lnD, the factor(D/j)^(alpha-1) is at most
exp(C_m alpha/D). The three negative-index regimes yield:

* Early i<R: M_D<=exp(C_m alpha/D)[1+C_m(m+1)^alpha/D].
* Middle with s>=1: M_D<=exp(C_m alpha/D)F_(q_s)(alpha).
* Late i>D-K: set u=(j-i)/j=O_m(1/D). The numerator is at most r^alpha
  and the denominator at least r^alpha(1-u)^alpha, giving
  M_D<=exp(C'_m alpha/D).

The surviving uniform vertices satisfy the last bound as well. F19 then
bounds the ratio of ANY nonbulk vertex moment to F_q by

    C_m alpha/q^alpha
      +C_m max_(1<=s<m)(q_s/q)^alpha
      +C_m alpha(m-1)^alpha/D,                           (F21)

for all large D, uniformly on[A0,c lnD]. The last term uses
(m+1)/q=m-1. Increase A0 so the first two terms sum to at most1/4
for every alpha>=A0. If c<1/ln(m-1), the last term is at most
C_m c lnD D^(c ln(m-1)-1)->0. It is eventually at most1/4.
Thus every nonbulk vertex moment is at most F_q/2 throughout this band.

The continuous optimum can still be rounded to an actual bulk rank:
theta_alpha is comparable to1/alpha, uniformly for alpha>=A0, so the
two neighboring ranks lie in[R,D-K] for alpha<=c lnD at large D.
If f(theta) denotes the moment in F18 before maximization, then

    (lnf)''=-(q^alpha-1)^2/[1+theta(q^alpha-1)]^2
                         +alpha t^2/(1+t theta)^2.       (F22)

On the1/D neighborhood of theta_alpha its absolute value is bounded by
C_m alpha^2, since theta>=theta_alpha/2>=C'_m/alpha.
The first derivative at theta_alpha is0. Taylor gives

    max_(k in C_D(alpha)) f(k/D)
            >=F_q(alpha)exp[-C_m alpha^2/D^2]>=3F_q/4    (F23)

uniformly in the logarithmic band at large D. This strictly dominates
F21. Combining the fixed initial interval and this band proves the same
vertex selection and hence, by Section4, the entire F2 equality theorem.
No critical-order assumption is used at the upper endpoint c lnD.

## 6. Sharpness for the relaxation and the rounding expansion

The early cut i=1,s=0 is the relaxation vertex

    lambda_sp=(m+1,1,...,1)/(D+m),
    M_sp=(D/(D+m))^alpha[(m+1)^alpha+D-1]/D.              (F24)

At alpha=c lnD with c>sigma_m, F18 gives

    M_sp/F_q(alpha)~e t alpha (m-1)^alpha/D->infinity.    (F25)

It beats every bulk rank. It is nevertheless NOT APPT: conjugate its
distinguished projector to a two-Schmidt antisymmetric Bell vector and
test the symmetric maximally entangled Bell vector. The unnormalized
partial-transpose expectation for I+mP is1-m/2<0. Thus F25 concerns
only the single-halfspace method and proves F3, not an APPT counterexample
or the physical transition coefficient obtained in the earlier cutoff papers.

Finally F12 gives g_q''(alpha,theta_alpha)=-J_alpha. On a compact
positive order interval, theta_alpha stays away from0 and1 and all third
theta derivatives are uniformly bounded, also through alpha=1. For either
neighboring integer k, Taylor yields

    B_q(alpha)-g_q(alpha,k/D)
       =J_alpha(k-D theta_alpha)^2/(2D^2)+O_(m,a,A)(D^-3). (F26)

Taking the smaller loss proves F6 with distance to the nearest integer;
this is an asymptotic value statement and does not replace the exact
comparison of the two ranks in F3. At alpha=1, D theta_1 is precisely the
stationary rank in the credited Ahiable--Kothakonda--Winter formula.
At alpha=2, theta_2=(m-1)/(2m), consistent with the previously proved
exact rectangular purity theorem; it is not a new independent purity claim.

## 7. Evidence and remaining scope

The mathematical argument above proves the quantified statements; finite
diagnostics only check vertex identities, exhaustive finite index bookkeeping,
scalar formulas and deliberately false extensions. It has no new Lean
formalization, empty-kernel replay, external human peer review or priority
certification. The fixedm threshold may depend on the positive lower order
bound and logarithmic-band margin. The proof does not cover m growing,
alpha tending to0 without that bound, the true minimal onset, arbitrary
finite-dimensional multilevel optima, the critical optimizer transition,
ASEP bulk attainment, or the existing Gaussian and finite-tree audit scopes.
