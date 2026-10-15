# One APPT entropy equivalent for every positive order and aspect ratio

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. ORCID 0009-0000-3864-3536;
mxymmxym1@gmail.com. 14 October 2026, Asia/Shanghai.
No external funding. OpenAI AI assistants assisted research and writing.
Copyright 2026 Yongxian Zhang; all rights reserved for original material.

The linear-order scalar profile has an exact finite-parameter version that
also covers arbitrarily faster order growth. This closes the unrestricted-
aspect large-order gap left in the earlier endpoint notes. The complete
all-positive-order statement is asymptotic as the smaller local dimension
grows. It is not an exact finite-dimensional entropy optimization theorem.

## 1. The calibrated finite scalar profile

Keep the actual APPT objects and notation in [PAPER.md](PAPER.md):
2<=m<=n, D=mn, u_D=3D/(D+2), M*_alpha and E_alpha=log M*_alpha/(alpha-1)
for alpha>1. All limits here have m->infinity, and m>=3 is used below.
For 0<=kappa<=2/(m-1) set

    eta_m(kappa)=2(m-2)kappa^2/[2-(m-3)kappa],
    d_m(kappa)=2-kappa-eta_m(kappa)>=0.

The denominator is positive even at the upper endpoint. The last inequality
is the exact identity L14 in [LINEAR_ORDER_VARIATIONAL.md](LINEAR_ORDER_VARIATIONAL.md).
For every alpha>1 define

    R=u_D^alpha/D,

    V_(m,alpha,D)(kappa,theta)
      =[1+theta((1+kappa)^alpha-1)
          +R((3-eta_m(kappa))/3)^alpha]/(1+kappa theta)^alpha,

    V_*(m,alpha,D)=max_(0<=kappa<=2/(m-1), 0<=theta<=1)
                                      V_(m,alpha,D)(kappa,theta).          (V1)

This is an explicit maximization of a continuous two-variable scalar
function on a compact rectangle. In particular V_*>=1+R and V_*>1.
It is a finite scalar approximant, not a premise restricting actual APPT
spectra to three levels. The peak uses the exact u_D; replacing it by 3
would fail for alpha much larger than D.

**Theorem V1 (all large orders).** For every fixed epsilon>0,

    sup_(n>=m, alpha>=epsilon*m)
           |M*_alpha/V_*(m,alpha,D)-1| ->0,                            (V2)

and uniformly on the same set,

    E_alpha ~ log V_*(m,alpha,D)/(alpha-1),
    (alpha-1)E_alpha-log V_*(m,alpha,D) ->0.                            (V3)

There is no upper bound on alpha or n and no assumed relation between them.

**Theorem V2 (all positive orders, all aspects).** Let P_alpha be U0 in
[UNIFORM_PROFILE.md](UNIFORM_PROFILE.md). Put, for sufficiently large m,

    P^all_alpha(m,n)=P_alpha(m,n)                      if 0<alpha<=sqrt(m),
    P^all_alpha(m,n)=log V_*(m,alpha,mn)/(alpha-1)       if alpha>sqrt(m).

Then

    sup_(n>=m, alpha>0) |E_alpha/P^all_alpha-1| ->0.                    (V4)

Thus both endpoints, finite critical orders, logarithmic and linear windows,
and orders growing arbitrarily faster than m or D belong to one equivalent.
The arbitrary split at sqrt(m) merely keeps the elementary finite-order
formula below and the finite variational formula above; it is not a phase
boundary. This is one completed APPT asymptotic direction, not several
independent counted solutions of major conjectures.

## 2. Actual physical inputs and the crucial dimension dichotomy

Use the actual middle set Bset, endpoints A=D lambda_j and B=D lambda_R,
and kappa=B/A-1 from the linear note. The necessary physical clique coupling
L7 gives

    y_1<=A[3-eta_m(kappa)], 0<=kappa<=2/(m-1).                         (V5)

The other actual bounds, from PAPER.md, are

    y_1<=u_D, y_2<=v_m->1+sqrt(2)<3,
    |y_i-1|<=delta_m=O(1/m) on Bset,
    |Bset|=D-m^2+2.                                                  (V6)

All these estimates are uniform over n>=m. They came from actual
all-global-unitary Schmidt witnesses, with full derivations and definitions
in the cited notes; no graph condition is used as a replacement definition
of APPT.

Set b_m=1+delta_m and T=b_m^alpha. Fix an arbitrary constant K>1. First
consider the comparable-or-smaller-peak range R<=K T. Then

    D>=K^(-1)(u_D/b_m)^alpha>=K^(-1)2^alpha                           (V7)

for all sufficiently large m, independently of n and alpha. Since
alpha>=epsilon*m, this gives uniformly

    m^2/D->0, alpha*m^2/D->0, alpha/D->0,
    (1+2/(m-1))^alpha/D->0.                                         (V8)

For the last bound specifically,

    (1+2/(m-1))^alpha/D
      <=K[(1+2/(m-1))b_m/u_D]^alpha<=K 2^(-alpha),

after a further common threshold. The other bounds follow from
alpha*m^2/D<=K alpha*m^2 2^(-alpha), whose supremum over alpha>=epsilon*m
tends to zero. These thresholds depend only on epsilon and K, not n or
alpha. This resolves the apparent difficulty of arbitrarily large alpha:
whenever bulk competition matters, its dimension is exponentially large
in that order. The remaining range will use the exact peak instead.

## 3. Uniform upper comparison in the comparable range

The actual middle mean mu satisfies |mu-1|=O(m^2/D), exactly as in L8.
For kappa>0 set theta=(mu-A)/(B-A); for kappa=0 set theta=0. Thus
A=mu/(1+kappa theta) in both cases. The actual convex secant and V5 give

    M_alpha(rho)
      <=mu^alpha/(1+kappa theta)^alpha
          [1+theta((1+kappa)^alpha-1)+(3-eta_m(kappa))^alpha/D]
          +m^2 v_m^alpha/D.                                        (V9)

Dropping the middle fraction |Bset|/D only increases the upper bound.
The exceptional remainder excludes the largest eigenvalue. By V8,

    mu^alpha=1+o(1),
    (3/u_D)^alpha=(1+2/D)^alpha=1+o(1),                              (V10)

uniformly in this range. Replacing the head coefficient by R therefore
costs only a uniform relative o(1). The exceptional remainder, divided by
V_*>=R, is at most m^2(v_m/u_D)^alpha->0 uniformly, since eventually
v_m/u_D<=15/16 and alpha>=epsilon*m. It follows that

    M*_alpha<=V_*[1+o(1)]                                           (V11)

in the comparable range. This estimates every actual state before taking
its maximum.

## 4. Uniform actual lower comparison for every scalar parameter

For any point (kappa,theta) in the finite rectangle V1 let

    k=max(1,min(D-1,floor(theta D))), theta_D=k/D,
    d=d_m(kappa), z=1+kappa theta_D+d/D.

Choose an actual rank-k orthogonal projection P and a unit v in its range.
Then rho=(I+kappa P+d vv*)/(D z) is an actual positive definite APPT
density. The exact Schmidt SOS G26 applies throughout the closed width
interval, including kappa=0 and d=0. This proves all-unitary positivity
for every finite rank; no existence or rank assumption is left to an ansatz.

Its exact moment, from the three actual eigenvalue multiplicities, is

    M_alpha(rho)=z^(-alpha)
      [1+theta_D((1+kappa)^alpha-1)
         -(1+kappa)^alpha/D+(3-eta_m(kappa))^alpha/D].                (V12)

The negative term removes the baseline slot replaced by the spike and
must be retained before estimating. Since |theta_D-theta|<=1/D and
0<=d<=2,

    z/(1+kappa theta)=1+O(1/D),
    [z/(1+kappa theta)]^alpha=1+o(1)                                (V13)

uniformly in both scalar parameters by V8. Moreover the head numerator
in V12 is at least the calibrated head numerator in V1, because 3>=u_D.
The rank-rounding error and removed slot together have absolute value at
most 2(1+kappa)^alpha/D, which tends uniformly to zero by V8. The scalar
numerator in V1 is at least one. Thus V12-V13 imply

    M_alpha(rho)>=V_(m,alpha,D)(kappa,theta)[1-o(1)]                  (V14)

uniformly over the whole rectangle. Choosing its attained maximizer gives
M*_alpha>=V_*[1-o(1)]. This proves both sides of V2 for R<=K T without
fixing limiting width or mixing parameters.

## 5. Exact peak comparison in the other range

When R>=K T, there is no need to assume alpha/D small. The exact pure-spike
state gives M*_alpha>=R for every alpha>1, including alpha much larger
than D. On every actual state, V6 bounds the middle moment by T and the
non-largest exceptional moment by R m^2(v_m/u_D)^alpha. Consequently

    R<=M*_alpha<=R[1+o(1)]+T.                                       (V15)

Independently, the scalar bulk term is at most (1+2/(m-1))^alpha<=T and
its calibrated head term is at most R. Hence

    R<=1+R<=V_*<=R+T.                                               (V16)

For R>=K T, these estimates give |M*/V_*-1|<=o(1)+O(1/K), uniformly
with no upper order restriction. Combine them with V11-V14, first let m
grow for fixed K, then let K grow. This proves the whole supremum V2.

The scalar choice kappa=2/(m-1),theta=1/2 has bulk moment

    [(1+1/m)^alpha+(1-1/m)^alpha]/2.                                (V17)

It is nondecreasing in alpha>=1: its logarithm is convex, vanishes at
alpha=1, and its derivative there is nonnegative by Jensen for x log x.
At alpha=epsilon*m it tends to cosh(epsilon)>1. Therefore log V_* is
uniformly bounded below by a positive constant on alpha>=epsilon*m.
V2 makes log M*-log V_* tend uniformly to zero, which proves the relative
entropy equivalent and the additive logarithmic statement V3.

## 6. Vanishing moment excess and the complete uniform assembly

For alpha->infinity with alpha=o(m), the same finite scalar profile has

    V_*-1 ~ R+alpha(alpha-1)/(2m^2),                                  (V18)

uniformly in n>=m. Here multiplicative moment accuracy alone would be
insufficient; we prove the excess estimate separately.

The scalar bulk is the alpha moment of a two-point mean-one variable,
whose squared deviation is

    kappa^2 theta(1-theta)/(1+kappa theta)^2<=1/(m-1)^2.

Both deviations have absolute value at most 2/(m-1). Since alpha/m->0,
Taylor's integral bounds uniformly give its moment excess as
alpha(alpha-1)/2 times this variance, with relative error o(1).
The calibrated head is at most R. This bounds V_*-1 above by the
right side of V18 times 1+o(1).

For the lower bound choose H=ceil(sqrt(alpha*m)),
kappa=2/(m+H),theta=1/2. Its variance times m^2 tends to one, because
H/m->0. Its head multiplier tends to one, since

    eta_m(kappa)=4(m-2)/[(m+H)(H+3)],
    alpha eta_m(kappa)=O(alpha/H)->0,
    alpha log(1+kappa/2)=O(alpha/m)->0.

This gives the matching lower excess bound, with error relative to the
sum of its two positive contributions. All estimates are uniform over
any L_m<=alpha<=U_m with L_m->infinity and U_m=o(m), and over every n>=m.

PAPER.md G1 proves exactly the same excess equivalent for M*_alpha-1.
Thus their positive logarithms agree relatively on this sublinear range,
even when the excess vanishes. If a uniform V4 counterexample above
sqrt(m) existed, a subsequence of alpha/m either tends to zero or is
bounded below by a positive epsilon. The first case is covered by V18
and G1; the second by V3. Both contradict it. Below sqrt(m), the old U2
already supplies uniformity. This proves V4 for every positive order,
without an aspect-ratio or order-growth restriction.

## 7. Relation to the earlier profiles and remaining questions

On alpha/m->c>0 with bounded 3^alpha/D, the rescaled width L=m kappa
turns V1 into F_*(c,r) of the linear note, including its width-two boundary.
V18 recovers the two-term sublinear law. For bounded n/m, the peak term
recovers the unlimited-order elementary formula. The zero-order two-window
law and its finite-window spectral criteria retain their existing scope.
The all-positive-order near-minimizer classification for bounded aspect
also retains its existing complete statement; no all-aspect spectral
classification is newly claimed by this entropy-value theorem.

This closes the all-aspect order-growth gap in the growing-m first nonzero
entropy value. Fixed-m moving-order optimization, exact finite minima
outside the explicit small positive-order band, every-aspect rigidity,
absolute separability and complete Lean formalization remain outside the
result. The finite projection/spike construction is credited as an input.
No external human peer review or historical-priority certification, new
Release, DOI or aiXiv submission is asserted.
