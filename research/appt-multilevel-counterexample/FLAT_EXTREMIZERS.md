# Asymptotically optimal APPT spectra need no fixed-height outlier

Analytic research working proof, 10 October 2026. No preprint or Release preparation. This note uses the new, proved graph limit in TWO_ENDED_GRAPH_LIMIT.md and the existing unrestricted upper bound in SHARP_ASYMPTOTIC.md. No Lean certification, external peer review, or finite verification of an asymptotic positivity condition is claimed.

## 1. Statement: the entire spectrum can approach uniformity

Let D=mn and let Pmax(m,n) be the unrestricted APPT maximal purity. The following statement is substantially stronger than weak or W1 convergence of a bulk spectrum.

**Theorem F.** There exist numbers epsilon_m>0 tending to zero and APPT states rho^+_(m,n),rho^-_(m,n), defined for all sufficiently large m and every integer n>=m, such that

    rho^+ + rho^- = 2I/D,
    ||D rho^+ - I||_op = ||D rho^- - I||_op <= epsilon_m,       (F1)
    Tr((rho^+)^2)=Tr((rho^-)^2),

and

    sup_{n>=m} | [Tr((rho^+)^2)-1/D]/[Pmax(m,n)-1/D] -1 |
      ->0 as m->infinity.                                    (F2)

In particular ALL normalized eigenvalues D lambda_i tend uniformly to one, while the first nonzero excess-purity term is asymptotically maximal. There is no order-one distinguished eigenvalue D lambda_1->3, or indeed any eigenvalue a fixed distance from one. Both ends of the symmetric line through I/D are APPT and have exactly equal purity. The state is not merely chosen close to the optimum in absolute purity, which would be trivial at scale 1/D: (F2) compares the excesses.

Equivalently, for every fixed epsilon>0, if Pflat(m,n;epsilon) denotes the maximum with the additional condition ||D rho-I||_op<=epsilon, then

    sup_{n>=m} | [Pflat(m,n;epsilon)-1/D]/[Pmax(m,n)-1/D] -1 |
      ->0.                                                   (F3)

The stronger vanishing-epsilon statement in (F1)-(F2) also holds. The construction has a justified diagonal choice of finite hierarchy lengths; it does not insert an arbitrary growing hierarchy into a fixed-depth limiting theorem.

This does not assert that EVERY near-maximizer is spectrally flat. The earlier spike constructions have D lambda_1->3 and also approach the optimal purity. Thus the conclusion identifies genuine nonuniqueness of the outlier structure left open by PHASE_RIGIDITY.md.

## 2. A finite two-sided positivity observation

Take nonnegative coefficients t_l and projections P_l, and set

    X=sum_l t_l P_l, L=sum_l t_l, xbar=Tr(X)/D,
    Y=X-xbar I, rho^+=(I+Y)/D, rho^-=(I-Y)/D.                  (F4)

For a Schmidt unit vector with coefficients z_1,...,z_m, put W=(|psi><psi|)^Gamma. Its negative eigenvalues are -z_i z_j, its positive off-diagonal eigenvalues are z_i z_j, and its remaining positive eigenvalues are z_i^2. The latter sum to one.

For a rank-r projection Q, evaluation in an eigenbasis of W gives

    -S_r(z) <= Tr(QW) <= S_r(z)+1,                            (F5)

where S_r is the sum of the largest min(r,binom(m,2)) products z_i z_j. For the lower bound sum the most negative eigenvalues, padding if necessary; for the upper bound ignore the rank restriction on the diagonal positive part and bound the off-diagonal part by its r largest terms. These inequalities hold for every conjugated projection, not only commuting ones.

Suppose that the weighted graph bound

    sum_l t_l S_rank(P_l)(z) <=1-sigma                        (F6)

holds uniformly for all Schmidt unit vectors, for some fixed sigma>0. Then for every U and every psi,

    -1+sigma <= <psi,(UXU*)^Gamma psi> <=1-sigma+L.

Since 0<=xbar<=L, the partial transposes of I+Y and I-Y are both at least (sigma-L)I. If L<sigma, both density matrices in (F4) are therefore APPT, with strict unnormalized margin sigma-L. Also 0<=X<=LI implies ||Y||_op<=L. They have trace one, are positive definite, satisfy (F1), and have exactly

    D^2[Tr((rho^+)^2)-1/D] = Tr(Y^2)=Tr(X^2)-(Tr X)^2/D.       (F7)

The same equality holds for rho^-. No normalization denominator is needed after centering. This finite lemma explains why a positive-coefficient graph construction can also produce a spectrum reflected about I/D.

## 3. The small-rank hierarchy replaces an isolated spike

The new graph theorem treats ranks m^alpha_i with 0<alpha_i<1/2 as well as the earlier ranks m^(2-delta_j) with 0<delta_j<1/2. Their witness-amplitude measures live in disjoint intervals; the low hierarchy's feasibility constraints involve SUFFIX energies, opposite to the high hierarchy's PREFIX constraints.

Let d_0=4 and d_j=d_(j-1)-d_(j-1)^2/8. For a fixed p, choose

    alpha_i=3^(i-p-1), 1<=i<=p,
    l_i=floor(m^alpha_i), f_i=d_(p-i)^2/8.

These low ranks are all o(m), but every rank tends to infinity. The coefficient at that rank may be chosen rational, for example

    a_i=(1-eta)/ceil(sqrt(l_i/f_i)),                           (F8)

where eta in (0,1) is fixed and rational. Then l_i a_i^2 ->(1-eta)^2 f_i, the sum of the coefficients tends to zero, and their graph limit is 2(1-eta). Their centered square mass tends to (1-eta)^2(4-d_p).

The integer ranks use no floating-point premise: floor(m^(1/3^s)) is the exact integer 3^s-th root. The ceiling in (F8) is also an exact rational/integer operation. Their finite APPT threshold is supplied by the uniform graph theorem and the fixed positive margin, not by the ranks' formal syntax.

Increasing p after the dimension limit makes the low-rank square mass approach four while the entire operator perturbation still tends to zero. This is the missing alternative to putting four units into one fixed-height spike.

## 4. Matching eight and the broad-plateau branch uniformly

For the first construction choose a fixed number p of low levels and q of high levels, the latter with delta_j=3^(-j), ranks floor(m^(2-delta_j)), and optimal high energies e_j=d_(j-1)^2/8. Take their rational coefficients with the same factor 1-eta as in (F8), and NO broad background. The combined graph limit is the larger of its two hierarchy limits, namely 2(1-eta), not their sum. Hence (F6) holds for all sufficiently large m with sigma=eta/2, say. Since L->0 it eventually satisfies L<sigma, giving both actual APPT states in (F4).

Nested rank ratios make all cross terms vanish. The total trace of X is o(m), its support has rank o(m^2), and its centered square mass obeys, uniformly in n>=m,

    Tr(Y^2) -> (1-eta)^2(8-d_p-d_q).                          (F9)

Thus for every tolerance, p,q and eta can be fixed first to obtain a uniform lower bound arbitrarily close to eight, with ||Y||_op->0.

For the second construction use only the low hierarchy and add the broad projection P of rank k=ceil((m-1)n/2) with coefficient d=2(1-eta)/m. The graph limit is again 2(1-eta): with no high hierarchy the broad complete graph is a separate limiting component. The same finite two-sided argument applies. Put gamma=n/m and theta=k/D; uniformly over n>=m,

    theta=1/2-1/(2m)+O(m^-2),
    Tr(Y^2)=(1-eta)^2(4-d_p)+4(1-eta)^2 gamma theta(1-theta)+o(1).
                                                                    (F10)

The o(1) is uniform in n: all low traces are o(m), so their trace correction and interaction with the broad term vanish uniformly. In particular, dividing (F10) by 4+gamma gives a uniform lower ratio approaching at least (1-eta)^2(1-d_p/4). The small change in theta is a relative O(m^-2) error even when gamma diverges.

Choose the first family when n/m<=4 and the second when n/m>4. The existing sharp unrestricted upper theorem says that D^2[Pmax-1/D]/max(8,4+n/m)->1 uniformly in n>=m. Equations (F9)-(F10) match it to any prescribed relative accuracy. All coefficient sums tend to zero independently of n.

For precision about limits, for each integer h choose fixed depths and fixed rational eta to make the coefficient error below 1/h. Then choose a dimension threshold M_h such that for EVERY m>=M_h and n>=m the graph safety margin, L<sigma, ||Y||_op<=1/h, and purity comparisons are all valid. Increase the M_h if needed. At dimensions M_h<=m<M_(h+1), use the h-th verified family. This constructs an epsilon_m tending to zero and proves (F1)-(F2). Fixing an epsilon and using the unrestricted upper bound proves (F3).

There is no effective estimate for M_h in this proof. In particular no moderate dimension is labeled APPT solely from a zero-slack limiting certificate.

## 5. Entropic consequences and a real nonuniqueness of near-maximizers

For any density matrix with x_i=D lambda_i-1 and max_i|x_i|<=epsilon<1/2, sum_i x_i=0. Taylor's theorem, using f''(x)=1/(1+x) for f(x)=(1+x)log(1+x)-x, gives

    sum_i x_i^2/[2(1+epsilon)]
      <= D[log D-S(rho)]
      <= sum_i x_i^2/[2(1-epsilon)].                          (F11)

Here S is von Neumann entropy and all logarithms are natural. Thus the flat asymptotically purity-optimal states satisfy, uniformly in n>=m,

    D[log D-S(rho^+)]/max(8,4+n/m) ->1/2.                     (F12)

The same holds for rho^-. More generally, for each fixed Renyi parameter alpha>0, alpha!=1, expansion of (1+x)^alpha and then log(1+z) gives

    D[log D-S_alpha(rho^+)]/max(8,4+n/m) ->alpha/2.             (F13)

The remainders are uniform because max|x_i|->0 and sum_i x_i^2/D<=epsilon_m^2. The alpha=1 case is (F12). These statements are exact leading laws for the constructed states, and sharp laws in the spectrally flat class if its radius is chosen as in Theorem F. They do NOT establish the unrestricted minimum of any entropy over all APPT states.

There is a concrete contrast with the previously constructed spike near-maximizers. At any fixed aspect ratio gamma>=1, let K_gamma=max(8,4+gamma). The old families can be chosen with one x_i->2, max_{i>=2}|x_i|->0, and sum_i x_i^2->K_gamma. Their entropy satisfies

    D[log D-S(rho_spike)] -> K_gamma/2+3 log(3)-4,             (F14)

because f(2)=3log(3)-2 and the other square mass is K_gamma-4. The new flat families instead give K_gamma/2. Their gap is the strictly positive constant

    4-3log(3)>0.                                             (F15)

For an elementary proof of the sign, log x < (x-1/x)/2 for x>1 follows by differentiation; at x=3 this is log3<4/3.

Both families have the SAME optimal leading purity and the SAME bulk phases from PHASE_RIGIDITY.md, yet their entropy deficits differ at their first nonzero scale. Therefore purity near-optimality and the bulk law do not determine the entropy or force a finite-height outlier. For higher Renyi parameters the corresponding difference is obtained from

    D[log D-S_alpha(rho_spike)]
      ->[3^alpha-1-2alpha]/(alpha-1)+(alpha/2)(K_gamma-4).

This is a comparison of rigorously attained families, not an asserted formula for the global entropy optimum.

## 6. Scope and remaining questions

Resolved here: existence of uniformly spectrally flat APPT near-maximizers in all regimes with m->infinity; actual reflection-symmetric pairs with exactly equal purity; a complete limiting graph/energy optimization for two-ended finite hierarchies; and different leading entropy deficits among near-maximal-purity states.

The result does not say every near-maximizer is flat, does not extend vanishing relative contrast to fixed m, and does not determine arbitrary finite-dimensional maximizers, absolute separability, global entropy minima, efficient hierarchy thresholds, or minimal numbers of levels outside the specified model. For fixed m the existing nonzero excess coefficient is incompatible with contrast tending to zero, so that exclusion is substantive.

The prior physical projection-test framework, paired-gap upper bound, and high-rank amplitude method are explicitly inherited from the research notes. The new low-rank endpoint, the background interaction, and the two-sided centering lemma are derived above rather than assumed. No previous immutable proof or manuscript is modified.
