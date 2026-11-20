# An optimal-size even residue mask excluding every proper prime power up to N

For stronger local retention at the same optimal size, see the [dense block wheel](OptimalDensePrimePowerWheel.md).

**Status.** An unconditional, effective local result for the positivity-only Li–Liu projection. It gives neither the existence of a prime pair nor a pointwise spectral estimate. The ordinary method bounds or subtracts the higher-prime-power terms (for example in [Goldbach in arithmetic progressions](https://academic.oup.com/qjmath/article/73/4/1375/6576399) and [Li–Liu's November paper](https://mrc.sdu.edu.cn/english/info/1018/1514.htm)); the construction below instead retains a genuinely prime-only von Mangoldt test at a compatible wheel, with optimal order of the wheel size.

For all sufficiently large even N, write L=log N. There is a squarefree positive modulus W and a 0–1 function M modulo W with the following properties.

- `log W ≍ √L`. The mask is supported on units, is even under negation, and vanishes at all p^j≤N with p prime and j≥2.
- For every even target N the construction retains a nonempty, reflection-invariant set of residues a mod W with M(a)M(N−a)=1. Their count is at least c(loglog N)^−2 times the ordinary locally admissible count of pairs of units.
- In its multiplicative Fourier expansion M uses only even Dirichlet characters. For any prescribed ε>0 the construction can be taken with `Σ |c_ψ| ≤ exp(ε√L)` for all sufficiently large N; in that statement the constant in log W≪_ε√L may grow with ε^−1.
- Conversely any nonempty unit mask excluding all actual proper prime powers ≤N, not merely their universal residue images, must have `log W ≫ √L`. The lower bound concerns exclusion on all of [1,N], not a mask required to work only inside one fixed central window.

## 1. Deal with low exponents by nonpower classes

Fix a constant C₀≥3 (to be increased for the Fourier bound), and take K=ceil(C₀√L). Let t be a prime in [2(K+14),4(K+14)] by Bertrand. For every odd prime k≤K choose distinct integers j_k in [14,13+K], and let ℓ_k be the least prime satisfying
    ℓ_k≡1 (mod k),       ℓ_k≡j_k (mod t).
This is a reduced class, with k,t distinct primes. [Linnik's theorem](https://arxiv.org/abs/0906.2749) gives ℓ_k≪K^A for a fixed effective absolute A. The ℓ_k are distinct by their different residues mod t, and ℓ_k>13 because ℓ_k≤13 would make its residue itself, not j_k. Also ℓ_k≥k+1. The modulus is
    W=2·13·∏_{3≤k≤K, k prime} ℓ_k.
Then log W≤O(π(K)log K)=O(K) and log W≥Σ_{3≤k≤K, k prime}log k≥K/2 for large K.

At 2 retain the unique unit class. At 13 retain the quadratic nonresidues. At ℓ_k retain the nonzero classes not kth powers, and let M₀ be the product of these local masks. At 13 this removes every even power, whether or not its base is divisible by 13. For every odd j≤K, j≥3, some prime k≤K divides j; its ℓ_k test excludes every a^j. Thus all remaining integer powers with exponent at most K have already been ruled out locally. In particular no lower bound on a prime base is necessary.

The local pair comparison is as follows. At ℓ denote the ordinary number of pairs of **units** a,N−a by b_ℓ=ℓ−ν_ℓ, with ν_ℓ=1 for ℓ|N and 2 otherwise. At 2 b₂=1 and the mask does not change it. At 13 the count with both arguments nonresidues is six if 13|N since −1 is a square. Otherwise, adding the two linear character sums and the quadratic Jacobi sum gives
    a_13=[13−2+2χ_13(N)+Σ_{a mod 13}χ_13(a)χ_13(N−a)]/4
         =[10+2χ_13(N)]/4∈{2,3}.
Here the last character sum is −1 by scaling and the usual elementary identity Σ_x χ(x²−c)=−1 for each c≠0: count solutions of (x−y)(x+y)=c. Thus a_13/b_13≥2/11. At ℓ_k a union bound removes at most (ℓ_k−1)/k choices for each of the two arguments from the original admissible pairs. Therefore
    a_ℓ/b_ℓ ≥ 1−2(ℓ−1)/[k(ℓ−ν_ℓ)]
              =1−2/k−2(ν_ℓ−1)/[k(ℓ−ν_ℓ)].
If ℓ|N the final term vanishes. For k≥5 the bound is 1−2/k−O(k⁻²) since ℓ≥k+1, and for k=3 the bound is positive since ℓ≥7 (it is at least 1/5). Multiplying and using Mertens gives a lower density fraction ≫(log K)^−2, uniformly in N.

Let A₀=#{a mod W: M₀(a)M₀(N−a)=1} and B_W=∏_{ℓ|W}b_ℓ. Then A₀≳(log K)^−2 B_W. We also need an **absolute** lower bound on A₀. Since all primes of W are ≤K^O(1), the ordinary local product b_ℓ/ℓ is bounded below by the product of (1−2/p) over all odd primes p≤K^O(1), together with 1/2 at 2. This lower product is ≫(log K)^−2 by Mertens. Thus A₀≫W/(log K)^4.

## 2. Delete the short list of high-power residues

List the residue classes modulo W of all integer-base powers b^j with b≥2, j>K, b^j≤N, and also their negatives. Retain in this list only residues with M₀=1, and call the resulting set E. One can list integer powers without first knowing which bases are prime. The bound
    |E| ≤ 2 floor(log₂ N) · N^(1/(K+1))
         = exp((1/C₀+o(1))√L)
follows by counting at most N^(1/(K+1)) bases per exponent. Set M=M₀−1_E. Negation preserves E and M₀, so M is still even; its nonzero values are still 1 on units. It removes every proper prime power up to N exactly, including high exponents; even removal of integer-base powers is valid.

Let A_W(N)=#{a mod W:M(a)M(N−a)=1}. At most 2|E| pairs were lost. Since W≥exp(K/2) and A₀≫W/(log K)^4, this loss is o(A₀); in particular A_W(N)>0 for all sufficiently large even N. One can compute A_W without enumerating the W residue classes: let e_N count a∈E with M₀(N−a)=1, and d_N count a∈E with N−a∈E. Reflection gives the exact count
    A_W(N)=A₀−2 e_N+d_N.
The sets of compatible residues at primes outside W are independent of this wheel restriction by CRT. Therefore the local-density normalization is
    S_W(N)=S(N) · A_W(N)/B_W
           ≫ S(N)/(loglog N)^2.
The final high-exponent mask need not factor over primes of W; its correction is the *single group ratio* A_W/B_W rather than the product of individually modified local factors. This is a local prediction for a prime count, not an asymptotic.

For effectivity, the ℓ_k may be obtained by searching the indicated CRT progressions, with effective polynomial bounds in K by Linnik, while the high-power base and exponent pair list has exp(O(√L)) size. The local counts modulo the test primes and e_N,d_N are finite elementary operations. No black-box prime-pair existence check is needed to construct the mask or to verify these local statements.

## 3. Fourier control, exact odd projection, and scope

At 2 use the principal character, at 13 use (χ₀−χ_13)/2, and at ℓ_k the kth-power indicator among units is (1/k)Σ_{ψ^k=1}ψ. Its complement within the units has coefficient ℓ¹ norm 2(1−1/k). All these characters are even: at 13, −1 is a square; at ℓ_k, −1 is a kth power for odd k. Hence the multiplicative Fourier coefficients of M₀ have ℓ¹ sum ≤2^π(K). For the even function 1_E on the unit group, Parseval gives coefficient ℓ² squared norm |E|/φ(W), so Cauchy–Schwarz gives ℓ¹ sum at most √|E| (all odd coefficients again vanish). Thus
    Σ|c_ψ(M)| ≤ 2^π(K)+√|E|
              ≤ exp((1/(2C₀)+o(1))√L).
Taking C₀ large enough proves the claimed variant with ε. This is the **one-argument** Fourier cost; a direct expansion of a two-argument product costs at most its square.

For real smooth f,g supported on a fixed interval I=(a,1−a)⊂(0,1), define
    P_{χ,f}^M = N^(−1/2) Σ_n Λ(n) χ(n) M(n) f(n/N),
    D_M(f,g) = N^(−1) Σ_{(n,N)=1} Λ(n)^2 M(n)^2 f(n/N) g(n/N).
Odd-character orthogonality gives the exact identity
    D_M(f,g) − [2/φ(N)]Σ_{χ mod N, χ odd} P_{χ,f}^M overline(P_{χ,g}^M)
      = N^(−1)Σ_{p+q=N; p,q distinct primes}
                       (log p)(log q) M(p)M(q)f(p/N)g(q/N).
Indeed n≡m is n=m and n≡−m is n+m=N on the support; the mask removes all proper powers. The p=q case (when N=2p) already gives Goldbach without this test. Strictly positive value for f=g≥0 now certifies a real prime pair with no additive higher-power error. The masked test is sufficient but not necessary: a genuine pair can lie in excluded classes.

The identity is arithmetic and unconditional. Inserting the multiplicative Fourier expansion into the analytic probes gives
    P_{χ,f}^M = Σ_{ψ mod W, ψ even} c_ψ P_{χψ,f}
with χψ induced to modulus lcm(N,W), even if W and N have common factors. Every χψ remains odd, so no principal pole is introduced. An analytic use of Li–Liu's construction requires control of the relevant zeros for these products and mixed ψ,ψ' correlations at the **original** congruence modulus N. It is not the unmodified T_lcm operator, and neither W=N^{o(1)} nor the Fourier cost above supplies a missing spectral estimate. In particular exp(ε√L) need not be absorbed by an arbitrary fixed negative power of log N.

## 4. A matching lower bound for excluding actual powers

Let W be any positive modulus with a nonempty collection of accepted units, and assume every proper prime power p^j≤N is rejected. The collection and W may depend on N; no evenness or Goldbach local condition is needed. Fix a reduced accepted class a. Linnik gives an effective absolute bound C W^A on the least prime in any reduced class mod W (enlarge C to include small moduli). Set
    T= floor[log N / log(C W^A)].
For each prime k≤T, if k∤φ(W), exponentiation by k is a bijection of the finite group (Z/WZ)^×. There is a reduced kth root class of a, containing a prime p≤CW^A by Linnik. Then p^k≤N is a rejected power in the accepted class, a contradiction. Hence every prime k≤T divides φ(W), and
    log W ≥ log φ(W) ≥ Σ_{k≤T, k prime} log k.
For T large, the last sum is ≫T by Chebyshev or PNT, forcing (log W)^2≫log N. For bounded T, log W≫log N directly from its definition (W bounded is also impossible once N is large). This proves the matching order `W=exp(Θ(√log N))` for exact periodic exclusion of actual powers, not merely for a chosen construction using universal kth-power images.

For scale, without a mask the total von Mangoldt weight of proper prime powers is already O(√N): the squares contribute θ(√N), and higher exponents cost O(N^(1/3)log N). Charging the unique partner at most log N gives O(log N/√N) normalized contamination on bounded windows. This is small enough for an ordinary Hardy–Littlewood-scale asymptotic and for Li–Liu's stronger R error, but much larger than the weight of one pair. The wheel is relevant at that microscopic positivity scale; it does not recover the signed estimate that Goldbach needs.
