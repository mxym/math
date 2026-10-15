# Unrestricted positive-order optimization of the final APPT bulk onset

Yongxian Zhang (张永贤), South China University of Technology.
15 October 2026, Asia/Shanghai. Complete ordinary proof M0-M2, separately
covered by a source-bound independent AI-agent read. M_REVIEW.md/json and
FINAL_STATUS_BINDING.json bind that read and the final status-only edits.
The L0-L2 read did not automatically cover this global extension.

## 1. Complete global statement

Use exactly PAPER.md's original all-global-unitary APPT density matrices,
integer bulk G_alpha, and extended integer FINAL onset N_alpha(m), with
+infinity allowed if bulk equality never holds at all later dimensions.
All orders in this manuscript are positive and finite, with no common
upper bound or lower bound away from zero. Put

    M(m)=min_(alpha>0) N_alpha(m).

For sufficiently large m this minimum is finite and attained, its global
minimizing set is closed and nonempty in (0,infinity), and

    M(m)=d_0*m^2+a_c*m+O(1).                               (M1)

Every order attaining it satisfies

    alpha=alpha_0+u_c/m+O(m^-2).                           (M2)

For every fixed H>=0, EVERY alpha>0 with N_alpha(m)<=M(m)+H has the
same conclusion with O_H(m^-2). All integer ties remain; uniqueness of
a finite minimizing order is not claimed. Constants alpha_0,d_0,u_c,a_c
are the exact analytic J/K/L definitions, not their illustrative decimals.

It suffices to prevent optimizing orders escaping the fixed interval
I=[1/2,2]. Let B=abs(a_c)+2 and n_m=floor(d_0*m^2+B*m). L gives
M_I(m)<=d_0*m^2+a_c*m+O(1)<n_m for large m. We will prove

    E_alpha(m,n_m)>G_alpha(m,m*n_m)
                        if 0<alpha<=1/2 or alpha>=2.       (M3)

Then such orders have N_alpha(m)>n_m, retaining the ALL larger n
definition; they cannot be global minimizers or fixed-gap near-minimizers.

## 2. Small orders, uniformly down to zero

Choose z=z_-(1/2), whose limiting negative head is strictly above zero.
The normalized gain kernel has the exact integral representation

    psi_alpha(1+h)/alpha
       =h^2*integral_0^1 (1-v)(1+v*h)^(alpha-2) dv.        (M4)

For this fixed negative h in (-1,0), its critical ratio
R_-(alpha,z)=psi_alpha(1+h)/(alpha*z) is strictly decreasing in alpha,
and extends analytically to alpha=0. Therefore, on [0,1/2],

    R_-(alpha,z)>=D_-(1/2)>d_0.                           (M5)

The last strict inequality follows from J's unique global minimum at
alpha_0>1/2, not from numerical values.

Here is the needed uniform finite-parameter justification. In L's (5a)
write w=alpha*w_0, where w_0=psi_alpha(1+kappa)/(alpha*kappa) is jointly
analytic at alpha=0 and kappa=0 by (M4). Then
v=(alpha-1)w_0 remains small with kappa, and

    B_alpha(kappa)/alpha
       =w_0*ell(v)-log(1+alpha*w_0)/alpha,
    g_s/alpha=(DeltaPsi/alpha-h*w_0)/(1+alpha*w_0).         (M6)

The apparent log quotient at zero has its analytic continuation.
All retained bases stay uniformly positive; so both functions are
jointly analytic near alpha in [0,1/2] and small kappa. The body difference
(B_alpha(kappa)-B_alpha(t))/alpha has its nonzero leading contrast factor
of order m^-3, while g_s/alpha tends to z*R_-(alpha,z)>0. Canceling those
factors in the exact crossing identity yields uniformly

    nu_-,m(alpha,z)=R_-(alpha,z)*m^2+O(m).                 (M7)

The exact derivative in n divided by alpha lies between positive
constants times m^-5 in absolute value for n comparable to m^2.
By (M5), the crossing is at least a fixed positive multiple of m^2
above n_m. The exact real-rank score minus B_alpha(t), divided by alpha,
is therefore >=c*m^-3. Real optimal rank fractions are 1/2+O(1/m)
uniformly, using the analytic maximization of score/alpha even at zero.
The two adjacent integer ranks are physical and their score loss divided
by alpha is O(m^-8), from the uniform second derivative in the rank
fraction. Hence a true negative-family APPT state strictly beats actual
integer bulk for EVERY 0<alpha<=1/2. Every error was divided by alpha
before taking a uniform bound; no absolute remainder is used against
arbitrarily tiny positive alpha. This proves M0.

## 3. Large orders through a logarithmically growing window

Now D=m*n_m=(d_0+O(1/m))*m^3. Set

    t=2/(m-1), kappa=2/(m+1), z=2, p=1+kappa/2,
    alpha_star=(5/(2*log 2))*log m.                        (M8)

For EVERY 2<=alpha<=alpha_star choose any exact integer bulk winning
rank k at contrast t. Its fraction theta=k/D is 1/2+O(alpha/m+1/D),
uniformly: this follows by expanding the exact bulk rank formula in
alpha*t, which tends to zero throughout (M8). Thus the same k is in the
physical interval [m(m-1)/2,D-m(m+1)/2]. The positive boundary state

    rho=(I+kappa*P+p*vv*)/(D+kappa*k+p), v in ran P,       (M9)

is actual all-global-unitary APPT, since (M8) is exactly the z=2 boundary
family. Compare with the winning bulk state of raw contrast t and rank k.

We record common estimates rather than applying a fixed-alpha theorem.
Put Q=(1+kappa)^alpha-1 and
H=(1+kappa+p)^alpha-(1+kappa)^alpha. For alpha in this range,

    alpha*kappa=O(log m/m),
    Q=alpha*kappa*[1+O(alpha/m)],
    H=(2^alpha-1)+O(alpha*2^alpha/m),
    0<H/D<=C*m^-1/2.                                     (M10)

The constants are absolute (with d_0 fixed). These bounds follow from
|exp x-1-x|<=C*x^2 for the uniformly small x=alpha*log(1+kappa),
and from (1+kappa+p)=2+3*kappa/2 with the same small exponent.
Since alpha>=2, alpha-1 is bounded away from zero. Subtracting the
power/trace logarithms EXACTLY before expansion gives the head increment

    D(e_head-e_body)
      ={D*log(1+H/[D+k*Q])-alpha*D*log(1+p/[D+k*kappa])}
                                                        /(alpha-1).

Expanding these logarithms with their relative errors from (M10), and
using 2^alpha-1-alpha>=2^(alpha-2) for alpha>=2, yields uniformly

    D(e_head-e_body)
      >=psi_alpha(2)*[1-C*(alpha/m+m^-1/2)].               (M11)

Indeed the denominator corrections have size O(alpha/m), the first
logarithm error is O(H/D) relative to the leading power term, and the
trace/head correction is O(alpha/m); the displayed lower bound for
2^alpha-1-alpha absorbs all these into the same relative kernel error.

For completeness, fixed-rank body loss also has a uniform estimate.
For r between kappa and t, the exact binary-body derivative is

    partial_r e_alpha(theta,r)
     =alpha*theta*(1-theta)*r*[1+O(alpha*r)],              (M12)

uniformly for theta near 1/2. This follows directly by differentiating
[log(1+theta*((1+r)^alpha-1))-alpha*log(1+theta*r)]/(alpha-1)
and expanding its analytic quotient in alpha*r; cancellation of the
first-order numerator leaves the displayed leading term. Both denominator
factors stay bounded away from zero. Since theta*(1-theta)<=1/4,
integration and t^2-kappa^2=16*m/(m^2-1)^2 give

    D(e_bulk-e_body)<=alpha*D*(t^2-kappa^2)/8
                           *[1+O(alpha/m)]
                     <=2*alpha*(d_0+o(1)),               (M13)

where the o(1) is uniform throughout (M8), including the O(m) displacement
in n_m. Finally (M4) at h=1 shows psi_alpha(2)/alpha is strictly increasing,
so for alpha>=2 it is >=psi_2(2)/2=1/2. As d_0<1/4 (J gives its minimum
strictly below D_+(2)=1/4), the fixed gap 1/2-2*d_0 is positive.
Combining (M11)-(M13) proves e_head>e_bulk=G_alpha for every
2<=alpha<=alpha_star. No continuous-rank replacement of the winning
integer bulk was made in this comparison.

## 4. Arbitrarily large orders

At alpha=alpha_star, (M10)-(M11) and the nonnegative body deficit give

    e_alpha_star(rho)>=c*m^-1/2/log m.                    (M14)

Here psi_alpha_star(2) is comparable to m^(5/2)/log m and D to m^3.
Fix this one actual state, chosen at alpha_star. Its entropy deficit
e_alpha(rho)=log D-S_alpha(rho) is nondecreasing in alpha>0. One direct
proof is convexity of log(sum_i lambda_i^alpha): slopes of its secants
from alpha=1 are nondecreasing, with the continuous derivative at one.
This is exactly the order monotonicity of finite-dimensional Renyi entropy.

For every positive order, all projection-bulk states have
max_i D*lambda_i<=1+t, and therefore

    G_alpha<=G_infinity<=log(1+t)=O(1/m).                 (M15)

This follows from S_alpha>=S_infinity, or the same secant argument.
Because m^-1/2/log m is larger than 1/m eventually, (M14)-(M15)
imply strict actual improvement for EVERY alpha>=alpha_star, with no
upper bound or relation to m. Together with Section 3 this proves M1
and completes (M3).

## 5. Global attainment, every minimizing order and every fixed-gap order

An outside-I order fails bulk equality at n_m, hence N_alpha(m)>n_m.
The inside-I candidate from L has N<n_m. Thus

    M(m)=M_[1/2,2](m)

for all large m, and EVERY global minimizing order belongs to the
interior of this interval. L proves this common minimum is attained,
has the value (M1), and localizes every minimizer as in (M2). Its closed
minimizing set in [1/2,2] lies away from both endpoints by (M3), so is
also closed (indeed compact) in the full positive half-axis.

For a fixed H, n_m-M_[1/2,2](m) grows at least linearly because
B>a_c. Eventually no outside-I order has N<=M+H. Apply L's bounded-gap
theorem inside I. This proves the stated conclusion for EVERY positive
bounded-gap order, even if it was initially allowed to depend on m
arbitrarily. Infinite N are automatically excluded by that inequality.

## 6. Exact scope

This removes the compact-order restriction ONLY for optimization of the
minimal FINAL onset and its fixed-additive-gap orders. It does not prove
the entire entropy extremum, exact optimizer classification or an exact
critical-window formula uniformly for arbitrary moving alpha. The lower
witnesses suffice to exclude escape; no such stronger theorem is used.
No exact finite threshold, effective cutoff, unique finite minimizing
order, external human peer review, new Lean, old audit expansion or
additional major-conjecture solution is claimed. All finite controls are
diagnostics; the preceding estimates carry the unbounded quantifiers.

Inputs are the separately reviewed I/J/K/L actual boundary constructions,
critical kernel identity and FINAL-onset theorem. This manuscript passed its own separate source-bound independent
ordinary mathematical read of the complete M0-M2 target. The existing bounded primary
literature screens are credited context, not an exhaustive priority claim.
Yongxian Zhang, SCUT; no external funding; OpenAI AI assistants assisted.
Original material all rights reserved; third-party notices retained.
