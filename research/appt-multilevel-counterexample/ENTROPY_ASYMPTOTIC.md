# The sharp APPT minimum-entropy law and entropy-extremizer rigidity

Analytic research working proof, 10 October 2026. No preprint or Release is prepared. All logarithms are natural. This argument uses the physical paired-gap/triangular bounds already proved in SHARP_ASYMPTOTIC.md, and the newly proved flat lower constructions in FLAT_EXTREMIZERS.md. The stronger physical star test and the nonlinear entropy estimate are derived here. No finite verification, Lean certificate, or external peer review is asserted.


> The final result in Section 12 covers every fixed finite Renyi order alpha>=1, not only the initial interval [1,2]. It proves a sharp spectral transition at alpha=2: all eigenvalues of low-order entropy near-minimizers are relatively flat, whereas high-order near-minimizers have exactly one fixed-height normalized outlier at three. Sections 1-9 establish the von Neumann theorem, which supplies the essential nonlinear upper bound.

## 1. Main results

Let Hmin(m,n) be the minimum von Neumann entropy of an APPT density matrix on C^m tensor C^n, 2<=m<=n. Let

    D=mn,  Emax(m,n)=log D-Hmin(m,n),
    K(m,n)=max{8,4+n/m}.

**Theorem E1 (sharp entropy deficit in all joint-growth regimes).**

    sup_{n>=m} | 2D Emax(m,n)/K(m,n)-1 | ->0 as m->infinity.   (E1)

In particular, if n/m->gamma in [1,infinity),

    D[log D-Hmin(m,n)] -> max{4,2+gamma/2}.                   (E2)

The conclusion is an UNRESTRICTED entropy optimization. Spectral flatness is not assumed in the upper bound; the main difficulty is controlling potential negative spectral outliers for which a naive quadratic Taylor bound fails.

For all dimension pairs, define

    r_m=(m+1)/(m-1),
    tau_m=r_m log(r_m)/(r_m-1),
    h_m=tau_m-1-log(tau_m)>0,
    B(m,n)=max{4/D,2/D+h_m}.

**Theorem E2 (fixed local dimension and uniform total-dimension equivalent).** For every fixed m>=2,

    Emax(m,n) -> h_m as n->infinity.                          (E3)

Combining this with (E1),

    lim_{N->infinity} sup_{2<=m<=n, mn>=N}
       | Emax(m,n)/B(m,n)-1 | =0.                            (E4)

This is a sharp first nonzero entropy-deficit equivalent, not an exact finite-dimensional interpolation formula. The fixed-m extremal interval calculation is elementary and is not claimed as a historically new principle.

**Theorem E3 (rigidity of entropy near-minimizers).** Fix n/m->gamma<infinity with m->infinity and K_gamma=max(8,4+gamma). For any APPT sequence rho_m, the following are equivalent:

    D[log D-S(rho_m)] -> K_gamma/2;                           (E5)

    D^2[Tr(rho_m^2)-1/D] -> K_gamma
    AND ||D rho_m-I||_op ->0.                                (E6)

Thus entropy near-minimizers must be uniformly flat in their normalized eigenvalues, not merely in an empirical bulk distribution. The converse also holds. Purity near-maximizers with a fixed-height spike are excluded from entropy near-minimality. No such necessity is asserted when gamma diverges, since a bounded head-energy loss is then negligible at the leading scale.

## 2. The new physical star with its center at the least eigenvalue

For m>=3 let lambda_1>=...>=lambda_D be an APPT spectrum. Define

    R=m(m-1)/2, S=m(m+1)/2, j=D-S+1,
    b=lambda_j, h=m-1,
    a_i=lambda_i/b-1, beta_i=1-lambda_(D+1-i)/b.

The b is positive: the earlier single-edge test gives lambda_1-lambda_D<=2b, and lambda_D<=b, so b=0 would force trace zero. The a_i are nonnegative and decreasing for i<=R, and beta_i are nonnegative and decreasing for i<=S. Put y=beta_1 in [0,1].

The usual paired-gap test places all diagonal witness values below b and gives

    g_i=a_i+beta_i,  sum_{i=1}^h g_i^2<=4,
    sum_{i=1}^R g_i<=m,  g_R<=2/h.                           (E7)

There is a stronger star inequality with a DIFFERENT actual assignment:

    sum_{i=1}^h (a_i+beta_(i+1))^2 <=4(1-y).                 (E8)

Proof. For a general rank-m Schmidt vector, assign lambda_D to the central diagonal |11> of its partial-transpose witness. Assign lambda_i to the negative star edge (1,i+1), and lambda_(D-i) to that edge's positive vector, for i=1,...,h. Assign the other h diagonal vectors the next h smallest eigenvalues, whose bottom ranks are h+2,...,2h+1. They are at most b because 2h+1<=S. Fill every remaining edge pair with an unused top-R and bottom-S eigenvalue, respectively. There are exactly R-h pairs left, and their differences are nonnegative. All slots are distinct because m^2<=D.

Every assignment is realized by a global unitary. The all-unitary APPT inequality for nonnegative Schmidt coordinates x_0,x_1,...,x_h is bounded above, after division by b, by

    (1-y)x_0^2+sum_i x_i^2-sum_i(a_i+beta_(i+1))x_0x_i.

The other edge terms that were dropped were nonpositive, and the leaf diagonal coefficients were enlarged to one. Thus this expression is nonnegative. Take x_0=1 and x_i=(a_i+beta_(i+1))/2, normalizing afterward if desired. This proves (E8). It is not a property inferred from a scalar necessary-only relaxation.

## 3. A nonlinear entropy bound for the entire exceptional head

Set

    f(x)=(1+x)log(1+x)-x for x>=-1,
    f(-1)=1,  hplus(a)=a^2/2-f(a) for a>=0.

**Lemma H.** Suppose a_1>=...>=a_h>=0 and y=beta_1>=...>=beta_(h+1)>=0 satisfy (E8). Then

    Hhead := sum_{i=1}^h [f(a_i)+a_i beta_i]
                    +sum_{i=1}^{h+1} f(-beta_i) <=2.          (E9)

This controls the entropy AND the cross terms created when pair gaps, rather than individual deviations, are used in the variance proof.

For 0<y<=1 put c_y=f(-y)/y^2, using the continuous value at y=1. Taylor's integral formula implies

    c_y>=1/2,  f(-beta)<=c_y beta^2 for 0<=beta<=y,
    f(a)=a^2/2-hplus(a).

Indeed f(-beta)/beta^2=integral_0^1 (1-t)/(1-beta*t) dt is increasing. Also

    c_y<=1/(2-y).                                           (E10)

For the latter, the derivative of log r-2(r-1)/(r+1) is (r-1)^2/[r(r+1)^2]>=0. It is zero at r=1, hence log r<=2(r-1)/(r+1) for 0<r<=1. Multiply by r and set r=1-y to get f(-y)<=y^2/(2-y); include y=1 by continuity.

Let u_i=a_i+beta_(i+1). Since beta is decreasing and a_i<=a_1,

    sum_i a_i(beta_i-beta_(i+1))<=a_1 y.

Expanding squares, using u_i^2>=beta_(i+1)^2, and retaining hplus(a_1), gives

    Hhead <= c_y[sum_i u_i^2+y^2]+a_1 y-hplus(a_1)
          <= c_y(2-y)^2+a_1 y-hplus(a_1)
          <=2+y(a_1-1)-hplus(a_1).                          (E11)

For a_1<=1 this proves (E9) immediately. For a_1>=1, (E8) implies a_1<=2sqrt(1-y), so y<=1-a_1^2/4 and a_1<=2. We need

    hplus(a)>=(1-a^2/4)(a-1) for 1<=a<=2.                   (E12)

A self-contained bound is

    hplus(a)=a^3 integral_0^1 t(1-t)/(1+a*t) dt
             >=a^3/[3(a+2)].                                (E13)

Cauchy--Schwarz in the weight t(1-t) proves the last step, because its mass is 1/6 and its first moment is 1/12. After multiplying the difference between the last expression and the right side of (E12) by 12(a+2), its numerator is

    3a^4+7a^3-18a^2-12a+24.

With z=a-1>=0 this becomes the manifestly positive expression

    3z^4+19z^3+21(z-5/14)^2+37/28.                           (E14)

Thus (E12) and (E11) prove (E9). If y=0, all beta_i vanish and (E8) gives sum a_i^2<=4, so the same conclusion follows. If y=1, (E8) makes every a_i and beta_(i+1) zero, and Hhead=f(-1)=1.

There is useful strictness. If a_1>=1 then (E13)-(E14) give Hhead<=2-37/1344. If 0<=a_1<=1, then

    2-Hhead>=hplus(a_1)+y(1-a_1).                            (E15)

Since hplus(a)>0 for a>0, any sequence with Hhead->2 necessarily has a_1->0 and y->0.

## 4. Uniform normalization and a tail-only variance budget

The earlier triangular argument, before inserting the star's four-unit budget, gives the stronger intermediate inequality

    V/b^2 <= sum_{i=1}^h(g_i-g_R)^2+Btail,
    V=sum_i lambda_i^2-1/D,
    Btail=max{4,D/h^2}.                                      (E16)

For reference, let w=g_R, eta_i=g_i-w, A=sum_i eta_i, and G be the decreasing upper-triangular arrangement of the eta_i. The physical norm bound gives

    ||Ge||^2+[4h/m]wA+h^2w^2<=4, e=(1,...,1)/sqrt(m).

The row inequality bounds sum_{i>h}eta_i^2 by ||Ge||^2. Centering the eigenvalues as in SHARP_ASYMPTOTIC.md gives V/b^2<=sum_i eta_i^2+wA+D w^2/4. Drop the nonpositive coefficient of wA, use 0<=hw<=2, and retain the first h squares. This is (E16), with no shape assumption.

In particular V/b^2<=C where

    C=max{8,4+D/h^2}=4+Btail.                                (E17)

Write z_i=lambda_i/b-1 and t=1/(Db). The paired sum in (E7) also yields a uniform two-sided normalization bound:

    |t-1|<=nu:=m/D+2/h<=nu_m:=1/m+2/(m-1).                   (E18)

To prove it, the positive z_i in the first R positions sum to at most sum g_i<=m. Every remaining positive deviation is at most g_R<=2/h, so all positive deviations sum to at most m+2D/h. The negative deviations among the last R positions sum in magnitude to at most m; at most m further negative slots remain, each of magnitude at most g_R. This is no greater than the preceding bound. Divide the absolute total by D to get (E18).

Furthermore,

    sum_i z_i^2=V/b^2+D(t-1)^2<=6C.                          (E19)

Indeed D(t-1)^2<=m^2/D+4m/h+4D/h^2<=7+4D/h^2, and combine with (E17).

Take the exceptional head to consist of the first h and last h+1 eigenvalues. Every remaining |z_i| is at most

    delta_m=2/sqrt(h),                                       (E20)

by decreasing order and the star square bound in (E7). All potentially fixed-size positive or negative spectral outliers have therefore been isolated; no Taylor expansion is applied to them.

## 5. The unrestricted entropy upper bound

The exact centering identity is

    [log D-S(rho)]/b = sum_i f(z_i)-D f(t-1).                 (E21)

It follows from sum_i(1+z_i)=1/b=Dt and S(rho)=-sum lambda_i log lambda_i. In particular the change of normalization is not silently discarded.

For |x|<=epsilon<1, Taylor's integral formula gives

    x^2/[2(1+epsilon)] <=f(x)<=x^2/[2(1-epsilon)].             (E22)

For all sufficiently large m, delta_m,nu_m<1. Apply (E22) only to the nonexceptional tail and the scalar t-1. By (E19),

    [log D-S(rho)]/b
      <= (1/2)V/b^2
         +sum_head [f(z_i)-z_i^2/2]
         +C[3delta_m/(1-delta_m)+3nu_m].                     (E23)

The first two terms are controlled exactly by (E9) and (E16): replace the first h residual squares by (a_i+beta_i)^2. Their cross terms are a_i beta_i, while the additional bottom slot contributes f(-beta_(h+1))-beta_(h+1)^2/2. Dropping the last nonpositive square yields

    (1/2)V/b^2+sum_head[f(z_i)-z_i^2/2]
      <=Btail/2+Hhead<=Btail/2+2=C/2.                        (E24)

This is the key nonlinear step. Bounding all negative deviations by the same quadratic Taylor coefficient without the physical star (E8) would not justify (E24).

Since Db=1/t<=1/(1-nu_m), and C/K(m,n)<=[m/(m-1)]^2, we obtain for every APPT state the explicit upper estimate

    2D[log D-S(rho)]/K(m,n)
      <= [m/(m-1)]^2 [1+6delta_m/(1-delta_m)+6nu_m]/(1-nu_m).
                                                                    (E25)

The right side tends to one independently of n>=m. This proves the upper half of (E1) over arbitrary spectra. The spectrally flat near-maximal-purity constructions in FLAT_EXTREMIZERS.md, together with (E22) at their vanishing contrast, supply the matching uniform lower bound. This proves (E1)-(E2).

## 6. Entropy near-minimizers must be flat and purity near-maximal

Now fix n/m->gamma<infinity. For a sequence satisfying (E5), the normalization in (E18) gives Db->1. Also C->K_gamma, Btail->max(4,gamma), and the error in (E23) tends to zero. Keeping Hhead instead of replacing it by two in (E24),

    [log D-S(rho)]/b <=Btail/2+Hhead+o(1).

Its left side tends to K_gamma/2=2+max(4,gamma)/2. Since Hhead<=2, it follows that Hhead->2. The strict bounds following (E14) then force

    a_1=lambda_1/b-1 ->0,
    y=1-lambda_D/b ->0.

All eigenvalues lie between these extremes, and Db->1. Therefore ||D rho-I||_op->0. Taylor's two-sided estimate now applies to the ENTIRE spectrum and turns (E5) into D^2 V->K_gamma. This proves (E5) implies (E6). Conversely (E6) and (E22) immediately give (E5), proving Theorem E3.

Thus a fixed-height outlier is not merely unnecessary for entropy optimality; it is incompatible with it at fixed aspect ratio. By contrast, the older purity near-maximizers with a normalized eigenvalue tending to three retain an entropy-deficit loss of 4-3log3. The same bulk profiles can conceal this difference, so bulk convergence alone is not enough to optimize entropy.

## 7. Fixed m: an exact limiting entropy calculation

Fix m>=2 and let n grow. The maximally entangled Schmidt-rank-m test gives

    sum_{i=1}^R lambda_i<=sum_{i=D-S+1}^D lambda_i,
    lambda_R<=r_m b,    lambda_1<=3b,    b<=1/j.

The latter single-edge bound is also valid for m=2. The N=D-m^2+2 eigenvalues at indices R,...,j lie in [b,r_m b]. The remaining m^2-2 eigenvalues have total mass O_m(1/D). Let T be the mass of the bulk, so T->1.

For any N-point probability vector whose nonzero entries lie in [a,r a], r>1, the entropy deficit from log N is at most

    h(r)=tau-1-log tau,    tau=r log r/(r-1).                  (E26)

To prove this without an assumed two-level extremizer, put z=Na and let Y_i=Np_i in [z,rz], with average one. The secant bound for the convex function x log x gives

    (1/N)sum_i Y_i log Y_i <= log z+tau(1-z).

Here 1/r<=z<=1. The right side has its maximum at z=1/tau, since 1<tau<r, and its value is (E26).

Apply this to the normalized bulk lambda/T. The entropy decomposition between bulk and exceptional coordinates, with all additional terms nonnegative, gives

    log D-S(rho) <= log D-T(log N-h(r_m))
                  =h(r_m)+o_m(1).

The apparent term (1-T)log N is only O_m(log D/D), so it tends to zero. This proves the unrestricted fixed-m upper limit.

For attainment let r=r_m, c=r-1=2/(m-1), and take the actual APPT state proportional to I+cP, with k=rank(P) and k/D->theta*=(tau-1)/(r-1). This is valid because 1<tau<r. The Schmidt-witness bound sum_{i<j}s_i s_j<=(m-1)/2 proves APPT for every projection rank. Its entropy deficit is exactly

    [r theta/(1+c theta)]log r -log(1+c theta), theta=k/D.

At theta=theta* it equals tau-1-log tau; integer rounding does not affect the limit. This proves (E3).

## 8. Uniformity over every pair with total dimension tending to infinity

As m->infinity, r_m-1~2/m. The integral identity for f gives

    tau_m-1=f(r_m-1)/(r_m-1)~1/m,
    h_m=tau_m-1-log tau_m~1/(2m^2).                           (E27)

Thus B(m,n)=max{4/D,2/D+h_m} is uniformly equivalent, over n>=m, to K(m,n)/(2D) as m grows. Positive sums and a maximum preserve the relative comparison; the error in (E27) depends only on m.

If the uniform equivalent (E4) failed, choose dimension pairs with D->infinity and relative error bounded below by a fixed positive number. Either a subsequence has m fixed, contradicting (E3) and B->h_m, or a subsequence has m->infinity, contradicting (E1) and (E27). This proves (E4). Neither convergence threshold nor an exact finite interpolation formula is asserted.

## 9. Scope and attribution

This resolves the leading unrestricted von Neumann minimum-entropy deficit over APPT states, including the fixed-local-dimension limit and uniform total-dimension equivalent. It also characterizes entropy near-minimizers at fixed aspect ratio as exactly the spectrally flat purity near-maximizers, at the stated leading scale.

The graph lower constructions, their order of limits and all-unitary implication are in TWO_ENDED_GRAPH_LIMIT.md and FLAT_EXTREMIZERS.md. The nonlinear upper bound here is independent of a spectral-shape ansatz. The earlier upper variance inequalities are used with their actual physical hypotheses. Standard Schmidt decomposition, finite-dimensional spectral theory, convexity, and elementary one-variable calculus are the mathematical background; finite regression counts are not substituted for them.

Prior studies of APPT purity and entropy include Ahiable--Kothakonda--Winter, arXiv:2608.03390, and Tran, arXiv:2609.18568. The two-level spectral-ratio construction and the scalar interval entropy calculation are not presented as newly invented principles. The new claim is the matching unrestricted joint-growth law and its outlier rigidity using the modified physical star plus two-ended constructions. Current-literature screening is not exhaustive priority certification.

Exact finite-dimensional entropy minima, higher-order terms, an effective hierarchy dimension threshold, and absolute separability remain separate questions. Sections 10 and 12 below extend the sharp leading law to every fixed finite Renyi order alpha>=1; the interval 0<alpha<1 is not settled here. The new research notes are not included retroactively in any earlier immutable release or in the concurrently maintained preprint.


## 10. Extension to the whole Renyi interval 1<=alpha<=2

For each FIXED alpha in [1,2], let

    Emax_alpha(m,n)=log D-min_{rho APPT} S_alpha(rho),

where S_1=S and S_alpha=(1-alpha)^(-1)log Tr(rho^alpha) otherwise. Then

    sup_{n>=m}| 2D Emax_alpha(m,n)/(alpha*K(m,n))-1 | ->0.     (E28)

At every fixed finite aspect ratio gamma and every fixed 1<=alpha<2, a sequence asymptotically minimizes S_alpha at this scale if and only if it satisfies (E6): optimal purity coefficient AND vanishing relative operator contrast. At alpha=2, purity alone is the criterion and fixed-height spikes remain possible. The rigidity assertion is not uniform for alpha approaching two with m.

To prove this, for 1<alpha<2 define

    f_alpha(x)=[(1+x)^alpha-1-alpha*x]/[alpha(alpha-1)],
    p=2-alpha in (0,1).

The weighted arithmetic-geometric inequality gives, for every t>0,

    t^(-p)<=(1-p)+p/t.

This compares second derivatives. Since the functions and first derivatives vanish at zero, Taylor's integral identity, valid for x>=-1 by continuity at the endpoint, implies the pointwise bound

    f_alpha(x)<=(alpha-1)x^2/2+(2-alpha)f(x).                 (E29)

Thus for x_i=D lambda_i-1,

    sum_i f_alpha(x_i)
      <=(alpha-1)D^2 V/2+(2-alpha)D[log D-S(rho)].             (E30)

The two unrestricted upper theorems bound each normalized term by K/2 up to a uniform relative o(1). The lower flat families have sum f_alpha~K/2. Also

    D[log D-S_alpha(rho)]
      =D/(alpha-1) log[1+alpha(alpha-1)sum_i f_alpha(x_i)/D].  (E31)

Here K/D=O(m^-2) uniformly in n>=m, so the logarithm is uniformly linear at the required relative scale. This proves (E28). At fixed gamma, saturation of (E30) forces saturation of the von Neumann term, because 2-alpha>0 and both component upper bounds are sharp. Theorem E3 gives flatness and purity near-maximality. The converse is the Taylor estimate on a flat spectrum. Alpha=1 is already proved; alpha=2 is exactly the purity problem after taking a logarithm.

For completeness, fixed m has an explicit Renyi limit too. Set r=r_m, and for 1<alpha<=2 put

    c_alpha=(r^alpha-1)/(r-1),
    z_alpha=(alpha-1)c_alpha/[alpha(c_alpha-1)],
    h_(m,alpha)=log z_alpha+log(c_alpha/alpha)/(alpha-1).      (E32)

Then Emax_alpha(m,n)->h_(m,alpha) as n->infinity. Indeed the convex secant bound for x^alpha in [z,rz] gives

    average Y_i^alpha <= z^(alpha-1)[c_alpha-(c_alpha-1)z].

The right side has its unique maximum at z_alpha in (1/r,1). The endpoints both have value one and every nonconstant mean-one endpoint mixture has moment greater than one, which also verifies that the critical point is in the interval. At that point its value is (c_alpha/alpha) z_alpha^(alpha-1), proving (E32). The O_m(1) excluded spectral slots contribute o(1) to the normalized power moment because every eigenvalue is at most 3/j=O_m(1/D). The projection states with the corresponding limiting rank fraction attain the secant bound. At alpha=1 use h_(m,1)=h_m; the expression is continuous there.

The small-contrast expansion gives h_(m,alpha)~alpha/(2m^2) as m->infinity. One way to verify it is to put r=1+c. The endpoint mixture of normalized eigenvalues has variance at most c^2/4+O(c^3), attained at a rank fraction tending to one half; uniform Taylor expansion of the power moment then gives alpha*c^2/8+O_alpha(c^3), and c~2/m. Thus the same sequential argument as in Section 8 proves the uniform total-dimension equivalent

    Emax_alpha(m,n) ~ max{4alpha/D,2alpha/D+h_(m,alpha)}       (E33)

for every fixed alpha in [1,2]. At alpha=2, (E32) reduces to log[m^2/(m^2-1)], in agreement with the previously established fixed-m purity limit.

The interval restriction is real. For alpha=3 and fixed gamma, the older spike near-maximizers satisfy

    D[log D-S_3(rho_spike)] -> (3/2)K_gamma+4,

whereas flat near-maximizers give (3/2)K_gamma. Therefore (E28) cannot be extended beyond two by simply retaining the same formula. Section 12 derives the missing spike correction and closes the higher-order Renyi optimum. The full alpha<1 regime, where small eigenvalues can be more important, remains outside the result.


## 11. An explicit finite-dimensional entropy separation

There is also a finite rational APPT state whose entropy is strictly smaller than the minimum of the original inscribed polytope. This example does not depend on a non-effective hierarchy threshold.

Take m=50,n=200,D=10000 and

    rho=diag(861,330 [4899 copies],319 [5100 copies])/3244431.
                                                                    (E34)

Its numerator is B=319I+11P+531|v><v|, where rank(P)=4900 and v is a unit vector in its range. For a Schmidt vector x with T=sum_{i=3}^{50}x_i and Q=sum_{i=3}^{50}x_i^2, the physical projection/witness lower bound is certified by the EXACT identity

    319 sum_i x_i^2-11 sum_{i<j}x_i x_j-531 x_1 x_2
       =295(x_1-x_2)^2
         +(649/2)(Q-T^2/48)
         +24(x_1+x_2-11T/48)^2 >=0.                         (E35)

Cauchy--Schwarz gives Q>=T^2/48. Thus every global unitary conjugate of rho has positive partial transpose, by the same explicit trace-pairing argument as PROOF.md. The numerator trace is exactly 3244431. Neither spectral sampling nor the entropy calculation itself is used as a positivity certificate.

Ahiable--Kothakonda--Winter v2, Theorem 6.10, identifies the minimum entropy of their inscribed polytope as the minimum of the one-hole, single-spike and specified two-level spectral-ratio candidates. In natural-log deficit form, those are respectively

    log[D/(D-1)],
    3 log3/(D+2)-log[(D+2)/D],
    at most h_50,

where h_50 is the continuous interval maximum in Section 7. The last upper bound covers every allowed integer rank, so no numerical rounding choice is needed for this comparison.

Exact outward rational logarithm intervals in check_entropy.py show that the deficit of (E34) exceeds ALL THREE upper values by more than 3/(10D). For the continuous two-level benchmark the scaled difference has the enclosure

    0.372043 <= D[E(rho)-h_50] <=0.372044.                    (E36)

These decimal endpoints are exact rationals with denominator one million, not floating-point tolerances. The checker uses range reduction and the convergent artanh series with an explicit rational remainder bound.

The strictly interior mixture rho_eps=(999/1000)rho+(1/1000)I/D still exceeds all three deficit benchmarks by more than 3/(10D), and

    (U rho_eps U*)^Gamma >= I/10000000 for every U.

Its scaled gap above h_50 is enclosed between 0.367559 and 0.367560. This gives a robust finite entropy separation, not only a leading asymptotic comparison. No claim of smallest dimensions is made.

At fixed aspect ratio, Theorem 6.10 also gives the inner-polytope scaled deficit limit max{3log3-2,gamma/2}; the one-hole limit one is smaller than 3log3-2. Equation (E2) gives the strictly larger unrestricted value max{4,2+gamma/2}. This does not refute a separate eventual-coincidence assertion with m FIXED and n arbitrarily large. It shows the failure of the inscribed polytope to capture the unrestricted entropy minimum in the proportional-growth regime.


## 12. Higher Renyi orders: the sharp spike correction and an order-two transition

The order-three obstruction in Section 10 suggests the correct missing term. It can be bounded sharply for EVERY fixed finite alpha>2, using the positive head rather than the negative head.

Define, for all fixed finite alpha>=1,

    A_alpha = 2alpha,                              1<=alpha<=2,
    A_alpha = (3^alpha-1-2alpha)/(alpha-1),          alpha>=2,
    Phi_alpha(gamma)=A_alpha+(alpha/2)max{4,gamma}.

The two definitions agree at alpha=2. The full joint-growth theorem is

    sup_{n>=m}| D Emax_alpha(m,n)/Phi_alpha(n/m)-1 | ->0
    as m->infinity.                                         (E37)

Thus at fixed gamma the exact leading entropy deficit is Phi_alpha(gamma)/D. The aspect-ratio transition remains at gamma=4, but the extremal outlier structure has a separate transition at Renyi order TWO.

For fixed gamma and fixed alpha>2, a sequence attains (E37) if and only if

    D^2[Tr(rho_m^2)-1/D] ->K_gamma,
    D lambda_1 ->3,
    max_{i>=2}|D lambda_i-1| ->0.                             (E38)

For fixed 1<=alpha<2, the corresponding equivalence remains (E6), with ALL normalized eigenvalues approaching one. At alpha=2, only purity optimality is necessary; both types and other purity near-maximizers are allowed. The statements are not uniform in alpha moving with dimension. The infinite-order entropy is not obtained by exchanging these limits.

### 12.1 A sharp nonlinear positive-head bound

For alpha>2 use the same normalized kernel f_alpha as in Section 10 and put

    k_alpha(x)=f_alpha(x)-x^2/2, x>=-1.

Taylor's integral formula shows that k_alpha(x)<=0 for -1<=x<=0. For x>0,

    k_alpha(x)/x^2
      =integral_0^1 (1-s)[(1+s*x)^(alpha-2)-1] ds

is strictly increasing and tends to zero as x decreases to zero. No derivative bound near x=-1 is needed; negative deviations have the favorable sign for this upper bound.

Let x_i=D lambda_i-1 and let nu_m be as in (E18). The top h=m-1 pivot deviations a_i obey sum_i a_i^2<=4. Since x_i=(a_i-(t-1))/t on these top slots, their positive parts obey

    max_i (x_i)_+ <= c_m:=(2+nu_m)/(1-nu_m) ->2,
    sum_{i=1}^h (x_i)_+^2
      <= B_m:=(2+sqrt(h)*nu_m)^2/(1-nu_m)^2 ->4.             (E39)

For every remaining positive x_i, the star square bound and ordering give

    (x_i)_+ <=epsilon_m:=(2/sqrt(h)+nu_m)/(1-nu_m) ->0.

These estimates are uniform in n>=m. Define omega_alpha(epsilon)=sup_{0<x<=epsilon} k_alpha(x)/x^2, with value zero when epsilon=0. It tends to zero. Therefore, with Q=sum_i x_i^2=D^2 V,

    sum_i f_alpha(x_i)
      <= Q/2+B_m k_alpha(c_m)/c_m^2+omega_alpha(epsilon_m)Q.
                                                                    (E40)

The middle term tends to k_alpha(2). The earlier unrestricted purity bound gives Q<=K(m,n)(1+o(1)) uniformly. Hence (E40) bounds the normalized kernel sum by

    K(m,n)/2+k_alpha(2)+o(K(m,n)).                            (E41)

Since K/D=O(m^-2), the exact logarithm in (E31) is uniformly linear at this scale. Multiplying (E41) by alpha yields the upper value

    alpha*K/2+alpha*k_alpha(2)
      =A_alpha+(alpha/2)max{4,n/m}=Phi_alpha(n/m).

For the matching lower bound use the earlier positive-spike constructions: the spike plus high hierarchy when n/m<=4, and spike plus broad plateau when n/m>4. Their parameters can be selected with a fixed positive APPT margin and then by the justified diagonal choice, uniformly in n>=m. The first normalized deviation tends to two, all the others tend uniformly to zero, and their squared sum has the previously proved optimal excess-purity coefficient. Thus their kernel sum is

    f_alpha(2)+(1/2)(K-4)+o(K),

which matches (E41). This proves (E37) for alpha>2. The earlier sections cover [1,2]. The flat construction was needed for the low orders; the old isolated-spike construction is optimal for the high orders.

### 12.2 Rigidity and uniqueness of the fixed-height outlier

Fix gamma<infinity and suppose the high-order entropy bound is attained. Equation (E31), (E40), and the sharp purity bound force BOTH Q->K_gamma and sum k_alpha(x_i)->k_alpha(2). If max_i x_i were bounded by 2-epsilon along a subsequence, strict increase of k_alpha(x)/x^2 would give

    limsup sum_i k_alpha(x_i)
      <=4 k_alpha(2-epsilon)/(2-epsilon)^2 <k_alpha(2),

a contradiction. Therefore x_1->2, so a_1->2 by the pivot normalization. The star sum sum_i a_i^2<=4 makes every other positive head deviation tend to zero. The shifted star (E8) gives a_1^2<=4(1-y), hence y->0. Ordering and the small-tail bound then show max_{i>=2}|x_i|->0. This proves (E38) necessarily. Conversely (E38) and uniform Taylor expansion on the remaining eigenvalues give the exact kernel sum above, so they suffice.

The conclusion specifies an actual distinguished eigenvalue, not just a budget of paired spectral differences. There cannot be two separate fixed-height positive outliers or any fixed-height negative one in a high-order entropy near-minimizer. This is a leading-scale classification and does not specify the distribution of the remaining vanishing amplitudes.

### 12.3 The all-dimension equivalent for every finite order alpha>=1

The fixed-m argument in (E32) extends without change to all fixed finite alpha>1: x^alpha is convex, the maximizing scalar secant point is the same z_alpha, the O_m(1) exceptional eigenvalues give only o(1) normalized power moment, and the actual projection states attain the bulk limit. Thus h_(m,alpha) in (E32) is the exact fixed-m limit for all finite alpha>1; at alpha=1 use h_m. It still satisfies h_(m,alpha)~alpha/(2m^2) as m->infinity for fixed alpha.

Combining fixed-m and joint-growth arguments gives, uniformly over integer pairs with D=mn tending to infinity,

    Emax_alpha(m,n)
       ~ max{(A_alpha+2alpha)/D, A_alpha/D+h_(m,alpha)}.       (E42)

This includes both entropy-order branches and all dimensional growth regimes. It is not an exact finite-dimensional maximum formula, nor a result for alpha depending on D. The sequential proof is identical to Section 8, now using the positive constant A_alpha in the two competing terms.

The remaining unrestricted Renyi interval not settled here is 0<alpha<1 (and the zero- or infinite-order limits under different orders of passage). Exact finite entropy minima and effective hierarchy thresholds also remain open in this work. No absolute-separability consequence is inferred from any of these APPT entropy results.


## 13. Endpoint checks and noncommuting entropy-order limits

For comparison, the rank and operator-norm entropy endpoints have elementary exact answers at every dimension pair. They follow from the standard rank-two physical tests, not from an exchange of limits in the preceding asymptotic theorem, and are recorded as consistency checks rather than priority claims.

Assign the least eigenvalue lambda_D and lambda_(D-2) to the two diagonal Schmidt-witness vectors, lambda_1 to the negative pair, and lambda_(D-1) to the positive pair. Nonnegativity for every two-component Schmidt vector gives

    (lambda_1-lambda_(D-1))^2<=4lambda_D lambda_(D-2).          (E43)

If lambda_D=0, this forces lambda_1=lambda_(D-1); all D-1 positive eigenvalues are therefore 1/(D-1), and a second zero is impossible. Conversely every state `(I-|v><v|)/(D-1)` is APPT: the largest eigenvalue of a partially transposed unit-vector projector is at most one, so its trace pairing against I-|v><v| is nonnegative. Hence the only singular APPT spectrum is the uniform rank-(D-1) spectrum, and

    min_APPT S_0=log(D-1).

The uniform rank-two test also gives lambda_1<=lambda_D+lambda_(D-1)+lambda_(D-2). The sum on the right is at most 3(1-lambda_1)/(D-1), so

    lambda_1<=3/(D+2),    min_APPT S_infinity=log[(D+2)/3].     (E44)

The normalized spike `(I+2|v><v|)/(D+2)` attains this and is APPT by the lower witness bound -s_1s_2>=-1/2. Equality in (E44) forces all remaining eigenvalues to be 1/(D+2): for D>4 this follows from equality of the lowest-three and full-tail averages; for D=4 use (E43) and equality in the arithmetic-geometric mean to obtain the same conclusion.

In balanced growing dimensions, the optimal infinite-order entropy deficit tends to log3, whereas the optimal deficit for each fixed finite order tends to zero at the scale proved above. Thus the limits in dimension and entropy order genuinely do not commute. The unresolved range 0<alpha<1 is not covered merely by knowing the two endpoints or by analytically continuing A_alpha.
