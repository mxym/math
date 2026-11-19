# Bounded-error Hermite location and the sharp fixed-order spread constant

Fix k=2m≥4. Let h_1<⋯<h_m denote the simple real roots of the monic probabilists' Hermite polynomial He_m, orthogonal to lower powers for a standard normal variable. Uniformly in n≥k+1, 0<p<1 and each feasible paired basis of the count LP, its ordered starts satisfy
  a_j=(n−1)p+sqrt((n−1)p(1−p)) h_j+O_k(1).
In particular
  Msp(n,k)=h_m sqrt(n−1)+O_k(1).
This answers the growth-order question for every fixed even k≥6 that BEKK ask after Conjecture 5.13. The error is bounded for fixed k, not uniform in k; this does not by itself prove monotonicity in n or give a rounding formula.

Put N=n−1, t=Np, σ²=Np(1−p), D~Bin(N,p). Start with the elementary large-variance moment estimate for Z=(D−t)/σ. For any fixed j, as σ→∞,
  E Z^j=E W^j+O_j(1/σ),  W~N(0,1),                     (2)
uniformly in N,p. Indeed, centering kills singleton blocks of a product of independent centered Bernoulli variables. Equivalently, the jth cumulant of a Bernoulli variable (j≥2) is bounded by C_j p(1−p): the second is p(1−p) and each succeeding one is obtained by applying p(1−p)d/dp, by its log moment generating function. Add N cumulants and divide by σ^j. Standardized cumulants of orders 1 and 2 are 0,1, and those of each fixed order ≥3 are O_j(1/σ) for σ≥1. Expanding moments by the finite set partitions proves (2).

**First, uniform coarse localization.** At any feasible pair {a,a+1}, its G polynomial in §2 of the phase proof has fixed degree d=k−2, nonnegative at every integer, not zero at either site. Its tilted mean lies in [a,a+1]. For unbounded σ consider the polynomial B(z)=G(t+σ z), scaled by a positive constant so that its monomial coefficient vector has Euclidean norm one. All its moments in (2) are controlled by fixed-degree coefficients, in particular |E[Z B(Z)]|≤C_d. We claim E B(Z)≥c_d>0 uniformly for σ sufficiently large. Otherwise take a failing sequence σ→∞ and a coefficientwise convergent subsequence B→B_0 with norm one. The standardized binomial grid has mesh 1/σ→0 and both distances to its endpoints from zero are at least σ, because t≥σ² and N−t≥σ². Each B is nonnegative on that grid, so B_0≥0 everywhere on the real line by local uniform convergence. Its normal expectation is strictly positive; by (2) and coefficient convergence it is the limit of E B(Z), a contradiction. Thus E[D G]/E G=t+O_k(σ), giving a=t+O_k(1+σ) uniformly for large σ.

On any bounded-σ range reflect D and the roots about N/2 if necessary, so p≤1/2 and t=σ²/(1−p) is bounded. Let e be the first nonroot of G in {0,…,N}. Then e≤d as there are d distinct roots, and G(e)>0. For x=e+h within the lattice, each root r differs from e by at least one, so 0≤G(e+h)/G(e)≤(1+h)^d. The successive binomial mass ratio gives
  P(D=e+h)/P(D=e)≤(2t)^h/h!.
Ignoring the denominator of the tilted law except for its mass at e bounds its tilted mean by
  e+Σ_{h≥1} h(1+h)^d (2t)^h/h!,
uniformly finite on this bounded-σ range. After undoing any reflection this again gives |a−t|≤C_k(1+σ). The reflection sends pair starts to N−a−1, harmless for this bound.

**Then, the sharp location.** The masses v_s=(n−s)w_s/[n(1−p)]=E l_s(D) at s∈J are a positive quadrature in the sense of nonnegative weights totaling one, exactly integrating polynomials of degree ≤2m−1 under Bin(N,p). This is immediate from Hermann's formula and cardinal interpolation. For σ large let b_j=(a_j−t)/σ, and P(z)=∏_{j=1}^m(z−b_j). All b_j are bounded by the first part. On the standardized quadrature support, which consists of b_j and b_j+1/σ, one factor of P at each site is zero or 1/σ and all are bounded. Hence |P(z)|≤C_m/σ throughout it. Quadrature exactness implies |E[Z^r P(Z)]|≤C_m/σ for 0≤r<m. Since its coefficients are bounded, (2) now gives |E[W^r P(W)]|≤C_m/σ for the same r. Subtract the monic He_m. The fixed matrix (E W^{i+j})_{0≤i,j<m} is positive definite by integrating squares of nonzero polynomials, so all coefficients of P−He_m are O_m(1/σ).

Choose small pairwise disjoint closed intervals around the simple Hermite roots, with He_m of opposite nonzero sign at their ends. Coefficient closeness forces P to have a root in each interval, hence exactly its correspondingly indexed root b_j. In that interval |He_m(x)|≥c_m|x−h_j| after possibly decreasing the fixed radii. Evaluating at b_j gives |b_j−h_j|=O_m(1/σ). Unscaling gives the desired bounded error. The bounded-σ case was covered by coarse localization, as |σ h_j| there is bounded.

The spread is a_m+1−a_1=(h_m−h_1)σ+O_k(1). Hermite symmetry gives h_1=−h_m, and σ≤sqrt(N)/2. Conversely p=1/2 lies in at least one closed positive-length phase by finite coverage, even when this is a transition. Its corresponding signed weights at p=1/2 are feasible by continuity. At this p, σ=sqrt(N)/2, giving the matching lower bound for the maximum over realizable bases. No use is made of unattained isolated endpoint bases.
