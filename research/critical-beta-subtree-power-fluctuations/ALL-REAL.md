# The centered real-power phase transition for critical beta-splitting trees

Fix a real p. On a random n-leaf binary tree with the critical beta-splitting law, write S_n(p)=Σ_v |v|^p, including all internal nodes v and excluding leaves. Let L=log n, Y_n=S_n(p)−E S_n(p). On the [Aldous–Janson exchangeable homogeneous fragmentation](https://arxiv.org/abs/2412.09655) realizing all finite trees, write P_i(t) for the interval frequencies, ν(dx)=dx/[2x(1−x)], b=ζ(2). For x in (0,1) write y=1−x and
```
D_r(x)=1−x^r−y^r,   κ(r)=∫D_r dν=ψ(r)+γ   (r>0),   B_p=∫D_p² dν.
```

**Theorem.** The following claims concern the distribution over random trees; each exponent is fixed, not chosen as a function of n.

* For p<1/2, p≠0, Y_n/√n converges in law to a centered nondegenerate normal with variance σ_p² given in (3) below, and Var S_n(p)/n→σ_p². For p=0, S_n(0)=n−1 identically.
* For p=1/2, Y_n/√(nL³) converges in law to a centered normal with variance B_p/[3bκ(p)²]>0, and Var S_n(p)/(nL³) converges to the same value.
* For 1/2<p<1, put Z_p(t)=Σ_i P_i(t)^p. The square-integrable martingale
  `Q(t)=Z_p(t)−1+κ(p)∫₀ᵗ Z_p(s) ds` has a terminal value Q∞, and Y_n/(n^p L)→Q∞/κ(p) in L². The latter distribution has variance B_p/[κ(p)²κ(2p)] and strictly positive third moment, so is not normal. No convergence of discrete third moments is assumed.
* At p=1 the same n log n scale gives the entropy-martingale limit −M∞/b, in L²; it is non-Gaussian with positive third moment. The companion proof establishes this separately, using the sharp mean edge-depth expansion of Aldous–Pittel. The limiting variance was already evaluated by Svihla–Lladser (2026).
* For p>1 the same n^p log n scale gives J_p−1/κ(p) in L² by the preceding [first-order result](https://github.com/mxym/math/pull/205), with J_p=∫₀^∞ Z_p(t)dt the classical fragmentation area of Bertoin. This variable is not normal because it is nonconstant and bounded below. This last range is a direct corollary of the preceding result, not a new limit theorem here.

All integrals giving the stated variances are finite. This establishes the Gaussian versus non-Gaussian transition for this critical splitting law and these deterministic power tolls. A square-root threshold for different split laws is classical, e.g. Hwang–Neininger for the uniform Quicksort split. The [Aldous–Janson overview, Open Problem 16](https://arxiv.org/html/2303.02529v3#S6.SS2) motivates subtree-power sums, not the individual fluctuation formulas here.

### 1. Finite-tree estimates

A size-m split (i,j=m−i) has q_m(i)=m/(2ij d_m), d_m=H_{m−1}, H_k=Σ_{j=1}^k 1/j. Let N_n(m) count internal m-clades, and a(n,m) be the probability that the uniform tagged leaf's descending ancestral chain visits size m. For fixed m≥2,
```
E N_n(m)=n a(n,m)/m,   a(n,m)↓a(m)=H_{m−1}/[b(m−1)] as n≥m increases.
```
The limit is from Aldous–Janson–Li; monotonicity is [Brandenberger–Chin–Mossel (BCM), Thm 1.1(i)](https://arxiv.org/html/2505.24821v3#S1); also N_n(m)/n→a(m)/m in L² by BCM Cor 1.4. A dyadic size bin [M,2M) contains at most C log(2M) tagged visits in expectation uniformly in n: the transition from k to i<k is 1/[(k−i)d_k], so every visit has exit probability ≥(M−1)/(2M H_{2M}) and there is no return.

For any bounded signed deterministic toll r_m let R_n=Σ_v r_{|v|}, and ρ=Σ_{m≥2}a(m)r_m/m. Since the tree has n−1 internal vertices, Σ_{m≤n,m≥2}a(n,m)/m=1−1/n. Also Σ_{m≥2}a(m)/m=1 by interchanging the harmonic sum and the telescoping Σ_{m>j}1/[m(m−1)]=1/j. Thus monotonicity gives
```
Σ_{2≤m≤n}|a(n,m)−a(m)|/m=Σ_{m>n}a(m)/m−1/n=O(log(2n)/n).
```
The omitted tail itself has this same big-O bound. In particular
```
 ER_n=nρ+O(log(2n)),                 Var R_n=O(n).                 (1)
```
For the variance, reveal the n−1 internal splits in breadth-first order; conditional on an unrevealed node of known size m its ordered children have the stated law. Centered split increments r_m+ER_i+ER_j−ER_m telescope to R_n−ER_n. By the mean bound they are O(log(2m)), including the finitely many smallest sizes (ER_1=0). The expectation of their squared sum is O(n): divide by n, use tagged size-biasing and, in dyadic bins M=2,4,…, sum O(log³(2M)/M). Orthogonality proves (1).

For 0<p<1, set κ=κ(p)<0, c=γ−κ′(p)/κ, and F_m=m^p(log m+c)/κ including m=1. Introduce the discrete drift operator (AF)_m=F_m−E_q(F_i+F_j). Then
```
r_m=m^p−(AF)_m=O_p(1).                                             (2)
```
Here and below big-O subscripts denote dependence on the fixed real parameter, not order in probability. Indeed set κ_m=d_m E_q D_p(i/m), κ′_m=d_m E_q[−x^p log x−y^p log y]. These are open-endpoint mesh Riemann sums at x=i/m for D_p/(2xy) and its p derivative. We have κ_m−κ=O(m^−p), κ′_m−κ′(p)=O(m^−p log(2m)). To see this, at 0 the integrands are bounded by C x^{p−1}(1+|log x|)^j, and their derivatives in x by C x^{p−2}(1+|log x|)^j, with j=0,1 respectively; symmetric bounds hold at 1, by direct differentiation. Bound the two endpoint-cell integrals and adjacent mesh terms at these orders and the total interior error by 1/m times the integrated derivative bound. The continuum derivative under the integral is justified by the same endpoint bound locally uniformly in p (allow a slightly smaller positive exponent). Now (AF)_m=m^p[(log m+c)κ_m+κ′_m]/(κ d_m), and d_m=log m+γ+O(1/m). Cancellation of the two leading terms proves (2).

In particular μ_n=E S_n(p)=F_n+n(ρ−F_1)+O(log(2n)) for 0<p<1, by (1) and telescoping. More precisely, writing x=i/m, T=x^p log x+y^p log y and J=−D_p, we have the *centered identity*
```
Y_n = (R_n−ER_n)+(1/κ)Σ_v m^p{(log m+c)(J−E_qJ)+(T−E_qT)}.
```
Indeed the centered contributions F_i+F_j−E_q(F_i+F_j) plus the deterministic telescoped boundary F_n−nF_1 equal Σ_v(AF)_m. Both J and T are bounded, and d_m E_q(J²+T²) is uniformly bounded for fixed p>0: near zero the mesh integrands are O(x^{2p−1}(1+|log x|²)+x), integrable, using endpoint bounds or summing a power-log mesh. In particular d_m Var_q J→B_p, since d_m E_q J²→B_p and E_q J=−κ_m/d_m.

### 2. The Gaussian ranges

For p<1/2 let g_m=Var_q(μ_i+μ_j), where μ_n=E S_n(p), μ_1=0. The full breadth-first increments are m^p+μ_i+μ_j−μ_m and have variance g_m conditional on m. By (1) directly if p≤0 and by (1)–(2) if 0<p<1/2, their absolute values are ≤C m^{p_+} log(2m), p_+=max(p,0). Hence no increment divided by √n exceeds o(1). Their scaled predictable quadratic variation converges in L¹:
```
 (1/n)Σ_m N_n(m)g_m  → σ_p² = Σ_{m≥2} a(m)g_m/m .                 (3)
```
For each finite truncation use the fixed-size L² law. In the tail M≤m<2M the expected absolute contribution is at most C M^{2p_+−1}log³(2M) by the tagged bin bound. These bounds sum to a vanishing dyadic tail. The same controls the limit series by Fatou. This proves variance convergence and the normal limit by the standard martingale-array central limit theorem (conditional Lindeberg follows from the deterministic increment bound). For m=4 the splits (1,3) and (2,2) both have positive probability, with μ_3+μ_1−2μ_2=3^p−2^p≠0 unless p=0. Thus σ_p²>0 as claimed.

At p=1/2 discard R_n−ER_n using (1). After dividing by √(nL³), the terms with cJ+T in the centered identity go to zero in L² by orthogonality, boundedness, and EΣ_v m=O(nL²) (Aldous–Pittel, mean edge-depth). The leading martingale has predictable quadratic variation, before dividing by κ²,
```
 (1/(nL³))Σ_v m(log m)² Var_q J → B_p/(3b) in L¹ .
```
Indeed (log m)Var_q J→B_p. For any ε>0 truncate at fixed sizes to make the coefficient error ≤ε above the truncation; the small-size contribution is O(n)/(nL³), and Σ m log m/(nL³)→1/(3b) in L¹ by the [first-order centered-at-one power *window* result](https://github.com/mxym/math/pull/205) with test function f(u)=u. The increments themselves are bounded by C√n L/√(nL³)=O(1/√L). Apply the same martingale CLT. Convergence in mean of the bracket gives the variance limit (the discarded terms vanish in scaled L²).

### 3. A continuum limit for 1/2<p<1

In the common fragmentation coupling let m=m_I(t) count the first n iid labels in each current interval I. Conditional on its finite discrete tree, the visible internal lifetimes τ_v are independent exponentials of respective rates d_m. Denote u=m/n and set a summand with m=0 to zero. For r=2p>1, uniformly in n and t,
```
 E Σ_{m≥2} u^r ≤ 2^s exp(−s t),   s=min(1,r−1)>0.                (4)
```
Indeed size-bias by a sampled tag with clade size m and use u^{r−1}≤2^s[(m−1)/(n−1)]^s on m≥2; Jensen and the two-label exponential survival law finish the proof.

The centered identity (2) implies
```
 Y_n/(n^p L) − U_n/κ → 0 in L²,   U_n=Σ_v u^p(J−E_qJ).
```
For the bounded-toll part this is (1) and 2p>1. For the cJ+T terms orthogonality and conditional holding times bound their scaled variance by C/L² times the integral of (4), since d_m E_q[(cJ+T)²]≤C. For replacing log(m)/L by 1 in the J term the relevant bound is the time integral of EΣ_{m≥2}u^{2p}(1−log(m)/L)² d_m E_q J². For fixed time empirical interval masses converge a.s. coordinatewise and in ℓ¹ (truncate to finitely many intervals with almost full mass). On every positive mass log(m)/L→1 and the rest is bounded by a constant times its empirical mass since 2p>1. Dominated convergence using (4) now applies over the full time interval.

Let Z_{n,p}(t)=Σ_{m≥1}u^p, **including all singleton blocks**, and define κ_1=0 as discrete drift coefficient. In the finite restricted process
```
 Q_n(t)=Z_{n,p}(t)−1+∫₀ᵗ Σ_{m≥1} u^p κ_m ds
```
is the compensated martingale with visible jump u^p J. Its squared tail from t to ∞ is ≤C exp(−s t) by (4) and d_m E_q J²≤C. Its terminal value differs from U_n by Σ_v u^p κ_m(τ_v−1/d_m). Conditional on T_n the squared error in mean is consequently Σ_v u^{2p}(E_q J)². Taking expectation turns this into a time integral with coefficient d_m(E_q J)²→0 uniformly bounded in m. The same finite-interval truncation and (4) show it goes to zero (exclude m=1, as before).

For fixed time, Z_{n,p}→Z_p and Σ u^p κ_m→κ(p)Z_p in L². Here ordinary mass-tail truncation alone would not suffice since p<1. Conditional on the true interval frequencies v_I, concavity gives E[(m_I/n)^p|v]≤v_I^p. The expectation of Z_p is finite: for a uniformly tagged point in a true block of mass V, −log V is the tagged subordinator with Lévy density dz/(e^z−1), so E V^{−h}<∞ for h<1 at finite t. Truncating to finitely many intervals and using conditional tail means ≤Σ_tail v_I^p gives unconditional L¹ convergence, by coordinatewise sample convergence and boundedness of κ_m. For uniform integrability of squares choose δ>0 with h=(1−p)(2+δ)<1. By empirical size bias and Jensen,
```
 E Z_{n,p}^{2+δ} ≤ E(n/M)^h ≤ E V^{-h},
```
where M is the block size of a chosen sampled tag: conditional on V, M=1+Bin(n−1,V) and E[n/M|V]=[1−(1−V)^n]/V≤1/V; h<1 gives the second Jensen bound. The analogous bound for the weighted empirical sum holds as κ_m is bounded. These bounds are uniform on compact time intervals by tagged independent increments. Thus fixed-time convergence holds in L², also after time integration on [0,t] by Minkowski. It follows that Q_n(t)→Q(t) in L². The continuum process is a martingale: conditional on the time-t frequencies, E Z_p(t+h)=Z_p(t) exp(−κ(p)h) by branching and the tagged Mellin exponent. Integrating this conditional identity yields the martingale property. The uniform empirical tail bound passes to increments of Q, giving its L² terminal limit. First take n→∞ at fixed t and then t→∞ to obtain Q_n(∞)→Q∞ in L². This proves the distributional identification.

### 4. Continuum variance and strict nonnormality

For 1/2<p<1 put J=x^p+y^p−1≥0, B_j=∫J^j dν for j≥1 (thus B_2=B_p), z=2p. At a block of mass w the jump of Z_p is w^p J, with dislocation intensity ν(dx)dt. The sum of all these jumps equals Z_p(t)−1, with no omitted continuous part: for each tag integrate the increasing pure-jump V(t)^{p−1}, using −log V a driftless subordinator and the chain rule; integration over tags counts each binary split as w^p J, by Tonelli. Its predictable drift equals B_1 Z_p dt=−κ(p) Z_p dt. Hence Q is the compensated jump sum. Its variance at ∞ is B_2∫₀^∞ E Z_z(t)dt=B_p/κ(2p), since E Z_r(t)=exp(−κ(r)t) for r>0.

Write C=−∫J D_z dν<0 and K(t)=E[Q(t)Z_z(t)]. The compensated jump product formula yields
```
 K′=−κ(z)K+C exp(−κ(3p)t),    (E Q³)′=3B_2 K+B_3 exp(−κ(3p)t).
```
Indeed the cross jump has size −w^{3p}J D_z and the centered square-jump intensity is B_2 Z_z. One may stop Q on leaving bounded intervals to justify the product formula: the jumps are bounded, the quadratic, cubic and fourth jump rates are bounded since Z_{jp}≤1 for j≥2, and localization with the polynomial jump identities yields finite fourth moments on every compact time interval (for the stopped fourth moment use a bound C(1+E Q_stopped^4) and Grönwall). The same argument with any larger even power gives uniform integrability on compact time intervals when removing stopping. Globally
```
 (E Q⁴)′=6B_2 E[Q²Z_z]+4B_3 E[QZ_{3p}]+B_4 E Z_{4p}.
```
Use E Z_r²≤E Z_r=exp(−κ(r)t) when r>1, Cauchy–Schwarz and the bounded second moment of Q to bound the derivative above by C₀ exp(−δ₀t)(1+E Q⁴) for some δ₀>0. Thus sup_t E Q⁴<∞ and third moments converge to the terminal third moment. As K(0)=K(∞)=0,
```
 E Q∞³=[B_3+3B_2 C/κ(z)]/κ(3p).                                  (5)
```
Its sign is strictly negative. With e=−x log x−y log y, J≥(1−p)e from the exponential tangent bound. For fixed x, r↦D_r is strictly concave, with D_1=0 and D′_1=e, hence (z−1)D_2≤D_z≤(z−1)e for 1<z<2. Thus
```
 (−C)/κ(z) ≥ (1−p) ∫e D_2 dν / ∫e dν = (1−p)/(2b).
```
Here D_2=2xy, ∫₀¹ e dx=1/2, and ∫e dν=b. By concavity in x and the chord of 2^t for 0≤t=1−p≤1/2, 0≤J≤2^{1−p}−1≤2(√2−1)(1−p)<3(1−p)/(2b); the last follows e.g. from b=π²/6<5/3 and √2<17/12. Therefore B_3≤(max J)B_2<−3B_2 C/κ(z). Since κ(p)<0, dividing (5) by κ(p)³ makes the sign positive. This proves strict nonnormality for the entire intermediate range without presuming any moment convergence beyond L² for the sampled trees.

The p=1 and p>1 rows in the theorem follow as indicated in its statement. The argument does not concern complex powers, joint fluctuation fields, moving powers, rates of normal approximation or arbitrary splitting measures.
