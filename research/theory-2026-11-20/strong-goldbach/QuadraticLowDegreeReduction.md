# A quadratic switch: a pointwise bound and an 11%-above-reference two-weight criterion

For even N let L=log N, S=S(N) the ordinary Goldbach singular series, and R the ordered prime-pair count with both logarithmic weights. For m=N−p>1 squarefree with prime factors r_i, set x_i=(log r_i)/L, h=(Σ x_i)/2, and

    Q(x)=Σ_{I⊆[k]} (−1)^|I| (h−Σ_{i∈I} x_i)₊²,       k=ω(m).
    W_j(N)=L Σ_{p<N, μ²(m)=1, ω(m)=j} (log p) Q(x).

The weights W₂,W₃ are nonnegative. For two factors LQ=(log r₁)(log r₂)/L, **not** log P⁻(m). For three factors Q is twice the convolution of the three interval indicators at h, with lengths x₁,x₂,x₃. The results are:

    liminf_{even N→∞} [R/(4NS)+(W₂+W₃)/(NS)]  ≥ 0.86868;                (1)
    if limsup (W₂+W₃)/(NS) ≤ 1.11 [½+log2−π²/24], then liminf R/(NS)>0. (2)

The reference coefficient ½+log2−π²/24 is approximately .781914. Thus (2) asks for a *one-sided*, per-target bound on a single sum of two explicit nonnegative low-factor weights, with an allowance 11% above its simplex reference. This hypothesis is **not proved**; the 11% is not an unconditional error bound. In (1) the higher-factor control and lower bound are unconditional. These bounds are asymptotic and cannot by themselves certify all finite N. This is not a claim that the two correlations individually have known asymptotics, nor that (2) is logically weaker than every prior conditional conjecture. Weighted almost-prime sieve identities have a long history; compare e.g. [Friedlander–Iwaniec, §2](https://msp.org/ent/2022/1-1/ent-v1-n1-p02-p.pdf), and the quite different prime-or-semiprime lower bound of [Li–Liu, Theorem 1.1](https://arxiv.org/html/2606.05224v2).

## 1. Unconditional mean of the quadratic kernel

The mean over all squarefree m is

    L Σ_{p<N}(log p) μ²(m) Q(x) = (1+o(1)) NS.                           (3)

Take Q=0 at m=1. In unnormalized variables let U_A(m)=Σ_{d|m}μ(d)log₊(A/d), where log₊(y)=max(log y,0). The desired per-m weight is (1/L)Σ μ(d)log₊²(√m/d). First replace √m by A=√N/L^D with a sufficiently large fixed D. The b² expansion, treatment of nonreduced classes, BV for z=[d,b²]≤AL⁴, and O(N/L²) tail of CenteredDivisorSwitch.md §§1–2 go through unchanged: here 0≤log²(A/d)/L≤log(A/d) on d≤A. Proper prime powers are negligible by the divisor bound if using Λ-progressions. The fixed-center prediction is therefore

    N A_sf(N)/L ⋅ Σ_{d≤A} c_N(d) log²(A/d)  + O(N/L²),

with c_N(d)=μ(d)1_{(d,N)=1}g_N(d)/φ(d), A_sf(N)=∏_{r∤N}(1−1/[r(r−1)]), and g_N as in CenteredDivisorSwitch.md. Write C_N(s)=Σ c_N(d)d^{−s}=H_N(s)/ζ(1+s). Thus at r∤N the r-factor of H_N is (1−[(r−1)/(r²−r−1)] r^{−s})/(1−r^{−1−s}); at r|N it is (1−r^{−1−s})^{-1}. In particular H_N(0)=S/A_sf(N) by direct multiplication. For the coefficients h_N, Σ |h_N(v)|(1+log v)≪(log log(3N))²: for r∤N the first nonconstant coefficient is O(r^-3), with a geometric higher-power tail; for r|N use ∏(1−1/r)⁻¹≪log L and Σ_{r|N}log r/r≪1+log L. The latter bounds follow by splitting at L. The standard PNT/Mertens estimate Σ_{u≤X} μ(u)log(X/u)/u=1+O(exp(−c√log X)) for X≥2 follows by integrating the exponentially decaying sum of μ(u)/u in log X; the limiting integral is 1 by the Abel transform 1/(s ζ(1+s)). Integrating the resulting estimate once more in log X gives Σ μ(u)log²(X/u)/u=2log X+O(1), uniformly X≥1. Convolve with h_N and bound the omitted coefficient tail using Σ |h_N(v)|log v. The fixed-center sum is 2 H_N(0)log A+O((log log(3N))²). Since 2log A=L−O(log L), this gives (3) for the fixed center.

For the variable center m<A² costs o(N) even in abs values: use Σ_{m≤X}τ(m)≪Xlog(2X) and two log weights. For the rest use the exact difference, per m,

    (2/L) ∫_{log A}^{(log m)/2} U_{exp(s)}(m) ds.

For log A≤s≤L/2 write U_{exp(s)}=U_A+(s−log A)V_A+∫_{log A}^s V_{A,exp(t)}dt, where V_A is the unweighted μ-divisor prefix and V_{A,B} that on (A,B]. Upon summing, m≥exp(2s) is a prime prefix. The weighted small-side BV proof in CenteredDivisorSwitch.md uniformly on prime prefixes bounds the U_A term by O(NS); SymmetricParityReduction.md (3) bounds the V_A term on prefixes by O(N/L²), using arbitrarily large logarithmic accuracy if desired. The actual L¹ interior-divisor-primitive bound of InteriorMobiusPrimitive.md, with its complement-only mask, gives O(NL^{−κ}) for the V_{A,exp(t)} term for some κ>0 uniformly here (the endpoints are interior powers). The integration length is O(log L), divided by L, so the total difference is o(NS).

On primes m the contribution is Σ log p (log m)²/(4L)= R/4+o(NS). Indeed for m>N/L^B, (log m)/L=1+O_B((log L)/L), and R≪NS by the usual upper sieve (the two linear forms p,N−p); smaller m contribute o(NS) for fixed B sufficiently large by a trivial count. No nonsquarefree contribution was silently dropped from the mean: μ² was present throughout; repeated prime factors are excluded in the box theorem below.

## 2. Exact vanishing, favorable five-factor sign, and transfer to the simplex

For k≥3 the full quadratic polynomial has zero k-fold difference. Since x_+²+(−x)_+²=x², pairing I with its complement shows Q=0 for **all even k≥4**. For k=2 this same pairing instead gives Q=x₁x₂. For k=3 the third backward difference of u₊² is 2 times the convolution of three interval indicators, hence Q≥0. For k=5 sort a≤b≤c≤d≤f and set v=(a+b+c+d−f)/2. Let F=2·1_[0,a]*1_[0,b]*1_[0,c]. Taking the largest-factor difference and then pairing the other four divisors yields

    Q=−2[F(v)−F(v−d)]≤0.

Indeed with H(u)=F(u)−F(u−d), the fourfold zero polynomial moment gives H(a+b+c+d−v)=−H(v), and v≤(a+b+c)/2. The convolution F is symmetric and nondecreasing up to (a+b+c)/2 (convolution of symmetric unimodal interval densities; directly each centered interval convolution preserves symmetric monotonicity). This uses no sign assertion at larger odd k.

For each fixed k the box domination of [SixPrimeNegativeSector.md, §1] applies to Q₊: actual normalized contribution ≤4 I_k(Q₊), where I_k(G)=1/k! ∫_{Σt=1}G(t)∏dt_i/t_i denotes the precise simplex convention given there (eliminate the last coordinate in dσ, retain every t_i in the denominator). The comparison is only for **nonnegative** quantities. At a coordinate face, the first difference over the smallest factor gives |Q|≤C_k min_i x_i on Σx_i≤1; hence the independent two-prime face bound in the appendix of the six-factor note applies, with error O_k(δ(1+log(1/δ))^{k−2}) as δ↓0.

For the infinite tail we also need tightness **uniform in N for actual primes**; bounding fixed ranks separately is insufficient. Here the extra order of smoothness makes this especially simple. For odd k≥3 the Fourier identity for a centered quadratic difference is

    Q(x)= (−1)^{(k−3)/2} (2/π) 2^k ∫₀^∞ ∏_{j=1}^k sin(t x_j/2) dt/t³.    (4)

Indeed u_+²=(u²+u|u|)/2 and u|u|=(4/π)∫₀^∞(tu−sin(tu))dt/t³. Sum the finite differences and use ∏(e^{itx_j/2}−e^{−itx_j/2}). Let 1<V<π/2 be fixed, for instance 5/4. We claim

    limsup L/(NS) Σ_{p<N, μ²(m)=1, odd k≥3} (log p) V^k |Q(x)| < ∞.        (5)

After (4) and absolute values, use [Pollack, Theorem 1.1](https://www.pollack-math.net/brunmultiplicative4.pdf) for the multiplicative weight μ²(m)∏_{r|m}2V|sin(t log r/(2L))|. These functions uniformly belong to the theorem's growth class since f≤(2V)^ω. For each r≤N^.001 with r∤N exclude the single nonzero residue N mod r. This retains all actual primes p>N^.001; smaller p can be dropped **before** (4) at o(NS) normalized numerator cost using k≪L/log L and the divisor bound. As in ExponentialEvenTail.md, after the prefactor L log p/(NS) the remaining bound is a constant times exp(Σ_{r≤N}2V|sin(t log r/(2L))|/r). For 0<t≤1 extract t³ using k≥3 and 2|sin(tx_j/2)|≤t x_j; apply Pollack with f(r)=V log r/L instead (on r≤N), weighted Euler sum O_V(1). Thus the integral near 0 is finite.

For 1≤t≤L, PNT partial summation of the absolute sine (variation rate O(1) in log r) gives an upper bound (4V/π)log(1+t)+O_V(1) on the exponent: ∫ 2V|sin(u/2)|du/u has logarithmic coefficient 4V/π by bounded primitive of its mean-zero part. For L≤t≤L³, omit primes with log r≤(C log L)^4 at harmonic cost O_V(log log L); on the remainder the PNT error is O_V(1) after differentiation, since t/L≤L² and the usual remainder in Σ_{r≤exp(v)}1/r is O((1+v)e^{−c√v}). The integral is at most (4V/π)log L+O_V(1), with lower angular endpoint at least 1. This frequency range contributes ≪_V L^{4V/π−2}(log L)^{O_V(1)}=o(1) after integrating t^{-3}. For t≥L³, use exp(2VΣ 1/r)≪_V L^{2V}; that last integral is o(1). The part from 1 to L is bounded independently of N since 4V/π<2. This proves (5), and Markov bounds the omitted k≥M ranks by O_V(V^{−M}) after limsup. Thus the actual upper bound by 4Σ_{odd k≥7}I_k(Q₊) is justified by a finite-rank limit, not an exchange of two uncontrolled limsups.

## 3. Explicit one-dimensional envelopes for all adverse high ranks together

By homogeneity of degree two, radial integration in ∏ e^{−x_i}dx_i/x_i replaces each signed simplex integral with the whole positive orthant: the radial factor is Γ(2)=1. Put J(t)=∫₀^∞e^{−v}|sin(tv/2)|dv/v and a(t)=arctan(t/2). Applying (4), Tonelli to absolute values and the elementary Laplace sine integral to the signed expression gives

    Σ_{odd k≥7} I_k(|Q|) ≤ A = (2/π)∫₀^∞ R₇(2J(t)) dt/t³,
    Σ_{odd k≥7} I_k(Q)   ≤ B = (2/π)∫₀^∞ (2a(t))⁷/(7! t³) dt,                (6)
    R₇(z)=sinh z−z−z³/3!−z⁵/5!.

For the second bound the k=7 term is positive and the alternating series terms decrease for all k≥7 since 2a≤π. The absolute convergence needed to sum the signed quantities will follow from the A bound. These estimates concern **only the reference integrals**. Combining them, I_k(Q₊)=[I_k(|Q|)+I_k(Q)]/2. Thus the full adverse actual high-rank upper bound is 2(A+B).

Here is a reproducible proof of the numerical constants, with purely rational certificate check_quadratic.py. The positive Fourier series for |sin| and the damped cosine integral give

    J(t)=(2/π) Σ_{n≥1} log(1+n²t²)/(4n²−1)
       ≤ min(t/2, π⁻¹log(1+t²)+C),    C=(4/π)Σ_{n≥1}log(n)/(4n²−1)<.31.

For C keep ten terms and bound the rest by (log 10+1)/(10(4−1/11²)), before the 4/π factor; this follows by decreasing-function integral comparison. Take T=2¹⁸. Below t=1/2, both integrals are <10^{-5} by R₇(t)≤2t⁷/7!. Above T, use R₇≤exp(z)/2 and 2J≤(4/π)log t+2C+1/T², with exp(2C+1/T²)<2, to get <1/4096 for A (4/π<4/3). For B that tail is <8/T² since 2a<π. On [1/2,T] the certificate bounds both envelopes at the right endpoint of each cell, using the **exact** t^{-3} integral on the cell. Each dyadic interval has 64 equal cells. Logarithms, Machin π, arctangents and hyperbolic tails are bounded by rational Taylor sums with explicit remainders and outward rounding. It verifies

    A < .06148,     B < .00418,     2(A+B)<.13132.

The upper envelope min(t, 2π⁻¹log(1+t²)+2C) is increasing, as is arctan; it is not necessary for J itself to be monotone. By (3), after deleting the nonpositive five-factor term and all vanishing even k≥4 terms, the adverse high ranks consume at most .13132 NS after limsup. This is precisely (1).

Finally I₂(Q)=½ because Q(t₁,t₂)=t₁t₂. For k=3, (4) yields I₃(Q)=(8/(3π))∫₀^∞arctan(t/2)³dt/t³. Substitute v=arctan(t/2), T₀=π/2; twice integrating by parts gives the inner integral −T₀³/8+(3/4)∫₀^{T₀}v cot v dv=−T₀³/8+(3/4)T₀log2. Hence I₃(Q)=log2−π²/24<.2820. As 1.11(.5+.2820)=.86802<.86868, (2) follows. The simplex constants here normalize the proposed input; neither using them as actual asymptotics nor claiming their presently unproved 11%-upper comparison would be justified.
