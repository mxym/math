# A sub-main-term bound for the negative six-prime sector

Let N be even, L=log N, m=N−p, with p prime. Use the singular series
S(N)=2∏_{r>2}(1−1/(r−1)²)∏_{r|N,r>2}(r−1)/(r−2), the symmetric triangular kernel K(m) from SymmetricParityReduction.md, and x₊=max(x,0). Unconditionally,

    limsup_{N→∞, even}  (1/(NS(N))) Σ_{p<N, ω(m)=6} (log p) μ²(m) (−K(m))₊
       ≤ 4 ( 1/10 + π⁴(log 2)/120 − π² ζ(3)/8 + 15 ζ(5)/16 ) < 0.608.        (1)

The displayed constant is an upper bound, not the predicted actual mass. In particular this exact-six-prime sector alone cannot exhaust the entire main term of the signed identity R(N)/2=NS(N)+…. The exact-two-prime sector and higher sectors remain; no bound for their combined deficit or proof of Goldbach is asserted.

## 1. A one-sided comparison with the log-factor simplex

For k fixed, put Δ={t_i>0, Σ_i t_i=1}, with measure dσ=dt₁…dt_{k−1} after eliminating t_k=1−Σ_{i<k}t_i (not Euclidean surface measure). Let G≥0 be continuous, bounded, symmetric and supported away from the coordinate faces. The actual reflected-prime factor measure obeys the upper bound

    limsup (L/(NS(N))) Σ_{m=∏_{i=1}^k p_i squarefree<N, N−m prime}
        log(N−m) G(log p₁/L,...,log p_k/L)
        ≤ (4/k!) ∫_Δ G(t) dσ/∏_i t_i .                                      (2)

Each m appears once; to evaluate G just below the simplex, use any continuous extension on the positive cube. Its values at the simplex determine the limit. Fixed regions with piecewise smooth boundaries and a.e. continuous cutoffs are also allowed (provided those boundaries intersect Δ in measure zero).

**Arithmetic input.** Use [Y. Liu, P. S. Park, Z. Q. Song, *Bounded gaps between products of distinct primes*, Theorem 3.2](https://people.math.harvard.edu/~pspark/boundedgaps.pdf), with their set of primes all primes (Siegel–Walfisz, level 1/2−ε for every ε>0, no exceptional modulus), u=1, fixed k, and each prime in a fixed interval [N^{a_i},N^{b_i}] with a_i≥δ>0. Their indicator sequence for products of distinct primes in these intervals satisfies summed maximum-reduced-class discrepancies ≪_{A,ε,k,box} N/L^A for q≤N^{1/2−ε}, all A. Their comparison is to its coprime sum divided by φ(q); not to an unconditioned sum. This is a classical switching-sieve input (cf. the prime-product sequence in Chen's switching principle), not a new distribution result. It is *the product* m which has an arithmetic-progression distribution, not the individual primes N−m in those boxes.

Partition the factor-log interval [δ,1] into finitely many disjoint bins and prescribe their unordered multiset for the k factors. These boxes are disjoint as sets of squarefree products. The primary theorem directly uses a set indicator, so repeated identical bins introduce no multiplicity. Endpoints can be assigned to one bin (including a single prime at an endpoint ≤N but ≥N^δ contributes O(N^{1−δ}) to a product count). Alternatively cover boundaries by fixed boxes of shrinking width, which have vanishing simplex measure. For one such box let A denote its unconditioned number of squarefree m<N. For squarefree moduli q≤D=N^{1/2−ε} coprime to 2N,

    #{m in box: m≡N mod q}= A/φ(q)+r_q,
    Σ_{q≤D,(q,2N)=1} τ(q)^C |r_q| = O_{A₀,C,δ,ε}(N/L^{A₀})                 (3)

for any fixed A₀,C>0 (box constants allowed). Indeed apply the preceding BV theorem; for the divisor weight use Cauchy–Schwarz on the first moment, since each basic discrepancy is ≪N τ(q)/q (count integers, and φ(q)^{-1}≤τ(q)/q). The weighted second bracket is bounded using Σ_{q≤N}τ(q)^{2C+1}/q≪L^{O_C(1)}. Replacing coprime box mass by A costs, after summation, at most N^{1−δ}L^{O_C(1)}: for each m in the box and large prime r|m, sum over q≤D divisible by r with weight τ(q)^C/φ(q)≪τ(q)^{C+1}/q, obtaining ≪_C L^{O_C(1)}/r; there are k such prime factors of m. The q here never includes a possibly nonreduced N class.

**Sieve constant.** Apply the usual Selberg λ² upper-bound sieve to N−m with divisors d<R=N^{1/4−ε/2} coprime to 2N. Use local selection density g(r)=1/(r−1) for r∤2N, omitting all other sieving primes, and g(d)=∏_{r|d}g(r) on squarefree d. Its optimized quadratic main term equals A/G_N(R), where

    G_N(R)=Σ_{d<R,(d,2N)=1} μ²(d) ∏_{r|d}(r−2)^{-1}.

Precisely, the square weights have λ₁=1 and λ_d=0 outside squarefree d<R with (d,2N)=1; the minimizing coefficients have |λ_d|≤∏_{r|d}(1−g(r))^{-1}≤2^{ω(d)}, by the standard Selberg diagonalization (the complementary partial G-sum is ≤G_N(R)). Thus after expansion the l.c.m.-weight at q≤R² is ≤τ(q)^{O(1)}, covered by (3). For N−m prime >R this sieve square is 1. The discarded primes ≤R cost O(R) box counts.

For completeness, write the Dirichlet series of this G-summand as ζ(1+s)H_N(s). Its H_N coefficients h satisfy, for r∤2N, h(r)=2/[r(r−2)], h(r²)=−1/[r(r−2)], h(r^e)=0 for e≥3; for r|2N they are h(r)=−1/r and h(r^e)=0 for e≥2. These multiplicative coefficients give H_N(0)=1/S(N) exactly. Moreover Σ|h(n)|≪log log(3N), and Σ|h(n)|log n≪(log log(3N))²: the nonsingular Euler errors are absolutely summable, and Σ_{r|2N}log r/r≪1+log L by splitting at L, while ∏_{r|2N}(1+1/r)≪log L by Mertens and splitting at L. Convolving with the harmonic sum shows uniformly

    G_N(R)= (log R)/S(N) + O((log log(3N))²).

The tail n>R omitted in the leading coefficient is bounded after multiplying by log R by Σ_{n>R}|h(n)|log n. Also S(N)≪log log(3N). It follows that each fixed box count of m with N−m prime is ≤(1+o(1)) S(N) A/log R+O(N/L^{A₀}), uniformly in N. No sieve lower bound is claimed.

Finally ordinary PNT gives the unconditioned box measure: in labeled coordinates a fixed symmetric bin condition H bounded away from 0 has

    A = (N/(k!L))(∫_Δ H(t) dσ/∏t_i + o(1)).

Here H includes all label permutations for the prescribed bin multiset. One direct proof sums over the first k−1 primes with reciprocal-prime measure on their fixed log bins (PNT/Mertens gives dt_i/t_i there). The last prime count up to N/(∏_{i<k}p_i) is, when 1−Σ_{i<k}t_i is in the interior of its bin, (1+o(1)) N/[(∏_{i<k}p_i)L(1−Σ_{i<k}t_i)]. If that terminal exponent lies outside the bin the analogous normalized count vanishes away from the bin edges (an overshoot gives a power saving); a terminal band of width v has bounded integrand and measure O_δ(v), then send v↓0. Repeated prime factors contribute at most O_k(N^{1−δ}) by summing 1/r² for r>N^δ. This proves the displayed box formula and its continuous extensions. Bound log(N−m)≤L, majorize G on each box, let bin widths shrink and ε↓0. This proves the factor 4 in (2).

## 2. Exact algebra and a positive-part geometric bound

Write K(t)=Σ_{I⊂[k]} (−1)^|I| min(0,Σ_{i∈I}t_i−(Σt_i)/2). Thus K(m)=L K(log p_i/L) for squarefree m. Specialize to six sorted lengths a≤b≤c≤d≤e≤f and write u=(a+b+c+d+e−f)/2. By complementary divisors as in OneSidedLargestFactor.md, K/2 is the iterated finite difference of x₊ at x=u for the first five lengths. The difference over a,b is the nonnegative tent

    f_ab(x)=max(0,min(x,a,b,a+b−x)).

Since u≤(a+b+c+d)/2≤c+d, every double shift among c,d,e is outside the support (including equality). Consequently

    K/2=f_ab(u)−f_ab(u−c)−f_ab(u−d)−f_ab(u−e),
    K₊ ≤ 2 f_ab(u).                                                         (4)

The integral of f_ab is ab, and it is symmetric about (a+b)/2: it is the convolution of the indicators of [0,a] and [0,b].

Let I(H)=(1/6!)∫_Δ H(t)dσ/∏t_i for a symmetric homogeneous degree-one function H. To evaluate it order coordinates descending and fix the largest to 1 by ratio coordinates, then divide all by their sum. For lengths x₁=1≥x₂≥…≥x₆>0, the simplex Jacobian for the substitution t_i=x_i/(Σx_j) is (Σx_j)^−6. This cancels the product denominators except for the extra 1/(Σx_j) from the degree-one kernel. Changing variables to U_i=x_{i+1}/x_i gives ∏_{i=2}^6 dx_i/x_i=∏_{i=1}^5 dU_i/U_i and x₆=∏U_i. Therefore

    I(H) = E[H(x)/(x₆ Σx_i)]

with independent U_i uniform on [0,1]. This identity is integrable for H=|K|: taking the difference over the smallest length first bounds |K|≤2⁵ x₆.

Fix the outer ratio r=U₁ as integration variable, and put x=(1,r,rd,rc,rb,ra), with d=U₂, c=dU₃, b=cU₄, a=bU₅ and B=1+d+c+b+a. Then K(x)₊ ≤ 2r f_ab(v), v=(B−1/r)/2 by (4). Integrating in r yields

    E_r[K(x)₊/(x₆ Σx_i)]
       ≤ (2/a) ∫₀^{a+b} f_ab(v) W(v) dv,
    W(v)=1/[(B−2v)(B−v)].

Indeed dr=2 dv/(B−2v)² and Σx_i=1+r B; extending the integral to the support of the tent is harmless. Its denominators there are positive, because B−2(a+b)=1+d+c−a−b≥1. The function W is convex there (product of the positive increasing convex functions (B−2v)⁻¹, (B−v)⁻¹). Bound it by the chord of its endpoints, and use the symmetry and mass ab of the tent, to get an upper bound b[W(0)+W(a+b)] ≤ b[(1+d+c)⁻²+(1+d+c)⁻¹]. Since E[b|c,d]=c/2 and c is uniform on [0,d], concavity in c of c/(1+d+c) and c/(1+d+c)² on this interval gives, by Jensen,

    I(K₊) ≤ ∫₀¹ (d/4) [(1+3d/2)⁻²+(1+3d/2)⁻¹] dd = 1/10.                 (5)

Neither sign of K is assumed globally.

## 3. The signed reference integral and the actual negative sector

The following identity is *only an evaluation on the simplex measure*. For even k=2s≥2, Fourier inversion of |x| and the vanishing of the two affine divisor moments give, writing t for the frequency,

    K(x)=(−1)^s 2^k/π ∫₀^∞ ∏_j sin(t x_j/2) dt/t².

Radial integration with e^{−Σx_j} and homogeneity allows replacing the simplex integral by the positive-orthant integral with product measure ∏e^{−x_j}dx_j/x_j; the radial factor is ∫₀^∞ e^{−u}du=1. Since ∫e^{−v}|sin(tv/2)|dv/v is O(t) near zero and O(log(2+t)) at infinity, the subsequent Fubini step is absolutely justified. The individual sine integral without absolute values is arctan(t/2). Hence

    I(K)= (−1)^s 2^k/(π k!) ∫₀^∞ arctan(t/2)^k dt/t².

For k=6, substitution v=arctan(t/2), T=π/2, and integration by parts show −I(K)=4/(15π) ∫₀^T v⁵ cot(v)dv. This is an exact standard-constant expression. Indeed integrate by parts again to obtain −5∫v⁴log sin(v)dv; insert log sin(v)=−log2−Σ_{n≥1}cos(2nv)/n by Abel damping (or integrate its L² cosine series). Two integrations by parts give ∫₀^T v⁴cos(2nv)dv=(−1)^n [T³/n²−(3/2)T/n⁴]. Thus

    −I(K)=π⁴(log 2)/120 − π² ζ(3)/8 + 15 ζ(5)/16.                      (6)

For a reproducible rational bound, use 3.1415926<π<3.1415927 and 0.6931471<log 2<0.6931472 (from Machin's formula and the series 2 atanh(1/3)). For ζ(j), j=3,5, use Σ_{n≤1000} n^{−j} < ζ(j) < Σ_{n≤1000} n^{−j}+1000^{1−j}/(j−1); these elementary rational evaluations give .051797<−I(K)<.051800. Exact code is supplied in check_six.py. The identity I((−K)₊)=I(K₊)−I(K) together with (5) bounds the **reference** negative part.

Finally (2) applies to G=(−K)₊ with all six factors ≥N^δ cut off, and (1) of FixedPowerStoppingSieve.md bounds the omitted **actual** mass by O(δ^η) after limsup, η=3/2−√2. Let δ↓0. The reference integral is finite by the ratio-coordinate bound above. This proves (1); the sieve transfer was applied only to a nonnegative function. The value of the signed reference integral was never substituted for an actual signed prime correlation.

**Independent elementary treatment of the coordinate faces (fixed k).** In fact (1) does not require the stopping theorem for this last cutoff, since k=6 is fixed. For every fixed k≥2,
 
    Σ_{p<N, P⁻(m)≤N^δ, ω(m)=k} log p μ²(m)|K(m)|
      ≪_k NS(N) δ (1+log(1/δ))^{k−2} + o_k(NS(N)),                (7)

in limsup for fixed 0<δ<1/4. Take m>N^.99 and p>N^(.01/k), the exclusions costing o_k(NS(N)) by the trivial fixed-count divisor bound. Take the difference over the smallest prime first, obtaining |K(m)|≤2^{k−1} log P⁻(m). Write m=q r with r its largest prime, so r≥N^(.99/k) and q≤N^{1−.99/k}. Exclude the negligible p|N. For each q coprime to N, the standard upper-bound Brun sieve in the variable 1≤r≤N/q sieving r,N−qr to N^(.01/k) gives O_k(S(N)h(q)N/(qL²)) choices, as in the two-prime upper bound of OneSidedLargestFactor.md; here h(q)≤2^{k−1}. The CRT remainder O(N^{.01/k+o(1)}) per q is absorbed into its main bound since N/q≥N^(.99/k). Write s=P⁻(m), a prime dividing q. The remaining k−2 distinct primes of q are ≥s. Bounding by all ordered tuples gives the normalized upper estimate

    ≪_k Σ_{s≤N^δ prime} (log s)/(sL) [1+log(L/log s)]^{k−2}.

Indeed Mertens bounds the reciprocal prime sum between s and N by log(L/log s)+O(1), uniformly for s≥2. Split log s into the dyadic ranges (2^{−j−1}δL,2^{−j}δL]; using Σ_{s≤e^Y}(log s)/s≪Y for Y≥log2 gives ≪_k δ[1+log(1/δ)]^{k−2}. This proves (7), which may replace the appeal to FixedPowerStoppingSieve.md in this fixed-k theorem. It makes no assertion uniform for unbounded k.
