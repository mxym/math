# Exceptional regimes and sparse Type II correlations for a fixed Goldbach target

This audits two routes different from the low-degree cutoff method and proves a scoped long-shift cancellation theorem with up to three true prime slots and a remaining rough proxy. It is not an unconditional Goldbach theorem. All references below are primary manuscripts.

## 1. What the exceptional-zero pointwise theorem already settles

Let χ be a primitive quadratic character of conductor q=2^r q' with q' odd, with a real zero β=1−1/(η log q), η≥10. Here r∈{0,2,3} and q' is squarefree. For an even target N let V=log N/log q and define

    C_χ(N) = χ(−1) 1_{φ(2^r)|N} (−1)^(N/φ(2^r))
                    ∏_{p|q', p∤N} (−1/(p−2)).

If the indicator vanishes the entire term is zero. For r=0 the 2-adic factor is 1 since N is even. [Matomäki–Merikoski, Theorem 1.4, arXiv:2112.11412v2](https://arxiv.org/pdf/2112.11412) gives, for V≥10, a main term NS(N)(1+C_χ(N)), with error bounded by a constant times

    (N/φ(N)) N [exp(−C √(V log η)) + exp(−C(log N)^(3/5−ε))
                         + V(log η)^6/η].

For any fixed δ>0 this is o(NS(N)) uniformly as η→∞ in 10≤V≤η^(1−δ): indeed S(N)/(N/φ(N))=∏_{p>2,p∤N}(1−1/(p−1)^2) is bounded below by the positive full product. The error on replacing von Mangoldt by prime-only log weight is O(√N (log N)^3), by trivial counting of proper powers.

The local factor gives an exact dichotomy. If any prime p≥5 dividing q' fails to divide N, then |C_χ(N)|≤1/3. Otherwise each odd-prime factor is ±1, contributed only by the prime 3, and the 2-adic factor is 0 or ±1. Thus, unless C_χ(N)=−1, one always has 1+C_χ(N)≥2/3. **Every such even target in the stated asymptotic regime already has a Goldbach representation**, using their theorem rather than the quadratic criterion. The only possible hard stratum in this window is exactly:

- the product of all primes ≥5 dividing q divides N;
- φ(2^r)|N;
- the product of χ(−1), (−1)^(N/φ(2^r)), and −1 if 3|q,3∤N (otherwise +1) is −1.

This includes but is not limited to multiples of an odd exceptional conductor. The criterion covers no targets outside that exceptional-zero range merely by an appeal to the absence of an exceptional character. It cannot be promoted to an all-N argument; even effective constants there would not bound q or force a zero to exist.

The hard stratum excludes a pair of primes *both* in the usual χ=−1 classes, unless some prime divides q. This follows directly from their character sum (18): on the set of residues a with a,N−a both units, each product χ(a)χ(N−a) is ±1. The complete average of those products, divided by their positive number, is C_χ(N). When that average is −1 every product is −1. A representation must therefore use the minority χ=+1 prime weight or one of the primes dividing q. These are exact alternatives, not a claim that the minority weight is absent.

The approximate prime identity (9)–(12) in their paper makes a structural distinction worth retaining when seeking a second-order estimate. Put A=1*χ and B=χ*log=A*Λ with Dirichlet convolution. On χ(n)=+1 one has the exact equality B(n)=(log n)A(n)/2, by pairing d,n/d, including the square term. On squarefree units A(n) is zero as soon as a factor prime has χ=−1; otherwise it equals 2^{ω(n)}. Thus on the minority side B detects primes plus products made entirely from the minority primes. On the χ=−1 side the discrepancy B−Λ for squarefree units has a good prime times a nonempty product of minority primes. Each error in the hard-stratum correlation consequently involves at least two minority prime factors across the two sides, apart from squareful or nonunit terms. This **does not give a product bound** without additional joint distribution: the quadratic size of the two-minority-factor contribution is a heuristic, not an available consequence of one-dimensional exceptional-prime scarcity. In particular their Lemma 2.1 bounds the full absolute approximation error using one lacunary harmonic sum; their Lemma 2.4 also sums absolute errors of the approximation to the rough χ-Mellin polynomial. The resulting V(log η)^6/η estimate is larger than the putative minority-scale main term V/η. No positive pointwise lower bound in the stratum C_χ(N)=−1 follows by retaining their main term or from the smoothed conductor averages in ExceptionalZeroTwoWeightTransfer.md.

## 2. An exact obstruction to transferring the modern shifted-prime determinant

[Prime Predecessors with an Even Number of Prime Factors, §§4.1, 4.2, 6](https://github.com/openai/math/tree/main/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026) obtains a parity-sensitive Type II estimate with a **structured, marked almost-prime operand**, not a pair of primes. The Cauchy–Schwarz step fixes e,n and compares mn=2eh+1 with m'n=2eh'+1. Its eq. (6.16) gives m'−m=2ek, h'−h=kn, z=m'h, mh'=z+k. Its graph input Theorem 4.1 requires a nonzero integer shift of fixed logarithmic-power size; the determinant 1 in the original equation is essential to that application.

In the corresponding Goldbach configuration, the following is instead exact. For any positive integers satisfying

    mn+eh=N,          m'n+eh'=N,          m'≠m,

put g=(e,n), so g|N; then e=g e₀, n=g n₀ and there is a nonzero integer k with

    m'−m=e₀ k,        h'−h=−n₀ k,
    z=m'h,            mh'= z−kN/g.                                       (1)

Indeed the first two follow by subtraction and (e₀,n₀)=1; the identity of the cross-products then subtracts k(mn₀+e₀h). In particular the primitive class (e,n)=1, which includes every positive factorization of a true distinct prime pair, produces shifts −kN, not −k. Conversely, for that class and (m,k)=1, given positive cross-factorizations z=m'h, z−kN=mh', with m'≡m mod |k|, set e=(m'−m)/k and n=(N−eh)/m. The determinant identity m(h'−h)=−k(N−eh) yields integrality and both equations, with e,n>0 and (e,n)=1 to be imposed. Restricting to (eh,N)=1 ensures the required coprimality. No assumption that all almost-prime factorizations are primitive is necessary for (1). On every box with e,n≤N^{1−c} the nonzero shift (1) has magnitude at least N^c, even without primitivity.

The range obstruction survives a literal dilation-graph substitution. With primitivity and the scale allocation of their §6 (m≈U, e≈U/(log N)^K, n≈N/U and h≍N/e on central Goldbach boxes), the cross-products have size Z=N(log N)^{O(1)} and |k| is at most a fixed power of log N. A nonraw comparison pattern uses two nonempty groups of free probes with primes at least exp((log N)^a), for some a>0; see their equations (4.8), (4.11) and the shared-label removal in §4.3. Once common marks have been divided out, its displacement is the base shift times the product of the free primes. With base shift −kN the displacement has magnitude at least N exp((log N)^a), far exceeding both operand scales. Its two operands with support in the still-comparable positive dyads therefore cannot both contribute. In the original proof the base shift is k, so the displaced operands do fit. One cannot assert the published transference theorem for macroscopic shifts and then subtract its comparison terms unchanged: doing so removes precisely the comparison mechanism from the relevant dyads.

A possible geometric repair is to partition m,m' into the same narrow relative cells of length 1/H with H superlogarithmic, and put E≈U/[H(log N)^K] while doing the Type II factor allocation. Then |k| again has logarithmic-power size and Z≈NH(log N)^K, making the comparison displacement small relative to Z if H exceeds the free-label products. But the first Cauchy inequality gains a factor H, and the usual convolution endpoint L² estimate in a cell only gives a squared norm O((Z/H)(log N)^{O(1)}) (expand by divisors and apply fixed divisor moments), not the two-endpoint matching saving 1/H² required after totaling the cells. Arbitrary *logarithmic* saving in the old correlation is not enough to absorb this new H. This is an accounting obstruction to the direct proof, not an impossibility theorem for refinements with new sparse-endpoint estimates. The minority-character problem and the macroscopic determinant problem are distinct; neither is resolved by the existing central spectral average.

### A sparse joint-support estimate that does hold

The lost support factor is not absent at the level of positive counting. For example, retain M≈U≤N^{1/2−c}, restrict both m,m' to one cell of length O(U/H) with H=N^{o(1)}, restrict (mm',N)=1 and P⁻(mm')>W=exp(√log N), and fix 0<|k|≤(log N)^K in the primitive determinant case. If m|z−kN and m'|z then (m,m') divides kN. The restrictions imply (m,m')=1 for large N. Each pair m,m' therefore puts z in exactly one residue class modulo mm'. For any z interval of length O(Z),

    Σ_z Σ_{m,m' in cell} 1_{m|z−kN} 1_{m'|z}
         ≪ (U/H)^2 [Z/U² +1] ≪ Z/H²,                                  (2)

since Z≈NH(log N)^K and U²≤N. Additional group-prime, size, primitive and congruence conditions can only reduce this positive count. The same upper estimate with a fixed log-power loss holds if the h,h' and m,m' coefficients are bounded by fixed powers of log N. Thus a log-saving **signed** version of (2) is a concrete more local target than the unrestricted L² graph pairing. Neither (2) nor an absolute residual-operator estimate with the larger L² norm furnishes that saving. For the stated single-endpoint norm bound, Cauchy over the factorizations and Shiu's [short-interval divisor moment bound](https://geodesic.mathdoc.fr/item/JRAM_1980__313_152201/) on the cell give
    Σ_{z≈Z}|F_cell(z)|² ≪ (log N)^O(1) Σ_{m in cell} τ(m)^O(1) Z/m
                         ≪ (Z/H)(log N)^O(1).
The gap between the two scales is precisely the cost that the existing small-shift proof cannot pay.

## 3. Log saving at a long shift on sparse cells with rough residual weights

This is an unconditional estimate involving genuine prime slots and a centered prime coefficient if desired. Its remaining controlled residual factors are rough-integer proxies, not an arbitrary coefficient or a prime. The distinction is critical for strong Goldbach. It is a scoped signed instance of the sparse-support scale proposed in §2 above.

Let N be even, L=log N, W=exp(sqrt L), 2≤w≤W, and 1≤H≤exp(L^(1/4)). Fix exponents 0<τ<θ with θ+τ<1/2. Take U=N^θ, P=N^τ, and intervals I,I' in [U,2U] of length at most U/H. Take any integer A=kN with 0<|k|≤L^K for a fixed K, and Z≥N with Z≤N H L^K; in the intended application Z≈NH times a log power. Let ψ be a fixed smoothly supported function on (0,∞), with the sum restricted to z−A>0. It is enough as well to use any interval J ⊆ [Z,2Z] of length at most Z intersected with z>A. The estimates below are uniform in such intervals and therefore also under fixed bounded-variation weighting.

Assume complex α,β are supported in I,I' respectively, bounded by L^C, and vanish outside m satisfying P⁻(m)>W and (m,N)=1. Write

    F(z) = Σ_{m p r=z, p∈[P,2P] prime, p∤N} α(m) 1_{(r,P(w))=1},
    G(z) = Σ_{m p r=z, p∈[P,2P] prime, p∤N} β(m) 1_{(r,P(w))=1},

where P(w) denotes the primorial (not the scale P) and all factors are positive. Let J be a real interval as above, ℓ(J) its length, and set

    Σ_P=Σ_{P≤p≤2P, p prime, p∤N} 1/p,
    D_w(A)=∏_{ℓ≤w prime} (1−ν_A(ℓ)/ℓ),
    ν_A(ℓ)=1 if ℓ|A, else 2.

Then for every fixed B>0,

    Σ_{z∈J∩ℤ} F(z)G(z−A)
     = ℓ(J) D_w(A) Σ_P² [Σ_m α(m)/m][Σ_m β(m)/m]
          + O_B((Z/H²)L^{−B}).                                         (1)

Implicit constants can depend on the fixed parameters θ,τ,K,C. In particular, if the first harmonic mean is O(H^{−1}L^{−B'}) with B' sufficiently large, (1) gives arbitrary fixed logarithmic saving **relative to sparse joint support scale Z/H²**, even at the Goldbach determinant shift A=kN. One may make that mean exactly zero by centering any supported prime coefficient against the supported rough sequence. No strong quantitative prime estimate is hidden in this centering: it is one scalar, not a claim about all short orthogonality conditions from the prime-slot theorem.

### Proof

Expand the two products and put d=m p, d'=m'p'. The contribution uses z≡0 mod d and z≡A mod d'. Every prime dividing d d' exceeds W for large N (since P is a fixed power), is coprime to N, and is larger than |k|. Thus gcd(d,d')>1 makes the two conditions incompatible. Otherwise CRT yields one class modulo dd'. Because d,d' are coprime to each ℓ≤w, the roughness conditions on r=z/d and r'=(z−A)/d' are **exactly** z≠0,A modulo each such ℓ. They give local counts ν_A(ℓ) independent of the four fixed factors. Since A is even the prime 2 contributes one forbidden residue, not two.

Take J₀ even with J₀=L^{1/5}+O(1). Truncating elementary inclusion-exclusion at J₀−1 and J₀ brackets the joint rough indicator. All moduli from this expansion are ≤Y=w^{J₀}=exp(O(L^{7/10}))=N^{o(1)}. Their combined CRT counting error for one tuple of factors is bounded by O(Y²): for each squarefree modulus s≤Y, at most 2^{ω(s)}≤s residue classes can occur. The gap of the two independent-model main terms is at most
    [Σ_{ℓ≤w} 2/ℓ]^{J₀}/J₀! ≪_{A'} L^{−A'}
for arbitrary A' by Stirling and Mertens. This also bounds each independent-model main term's error from the full product. Thus on each compatible tuple, the rough count is
    [ℓ(J)/(dd')] D_w(A) + O_{A'}(Z/(dd' L^{A'})+Y²).
This holds even when J is shorter than Z; the error bound just uses the upper length Z. Negative or complex α,β cause no issue since the approximation is made before multiplying by them.

There are O(U²P²/H²) possible tuples, and dd'≈U²P². The summed errors after coefficient bounds are O((Z/H²)L^{-B}) for every fixed B, since U²P²Y²≤N^{1−c} for some fixed c>0 and Z≥N. It remains to remove gcd(d,d')=1 from this main term. The following elementary counts are at most an arbitrarily small logarithmic-power fraction of the unrestricted O(U²P²/H²):

- p=p': the fraction is O(1/P).
- p|m' or p'|m: for each fixed p there are O(U/(Hp)+1) choices, giving fraction O(1/P+H/U).
- (m,m')>1: set X₀=U/H. For a common prime W<s≤X₀, both cells have O(X₀/s+1) multiples; the total is O(X₀²/W) by the sum of s^{-2}. For s>X₀, each m has O(1) such prime divisors because X₀=U^{1-o(1)}, and the other cell contains at most two multiples of each. This adds O(X₀), for a fraction O(1/W+H/U).

These estimates compare to the upper cardinality U²P²/H² and do not need any lower count of primes in the given p interval. We can therefore decouple the four main factors. The loss from decoupling remains negligible with the coefficient log-power losses since dd'≈U²P², proving (1).

### Why this does not complete the prime-slot route

In the [shifted prime-slot correlation theorem](https://github.com/openai/math/tree/main/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026), the residue after the distinguished p carries an arbitrary bounded coefficient, further factor slots, and a separate invariant marked weight. Formula (1) applies only when the companion residue is an ordinary rough proxy and when the product of the two fixed divisor scales lies below Z. If that companion instead carries its own prime weight, the CRT step asks for a correlation of two affine prime forms in the remaining variable. Nothing here provides it. Also, a cancellation of the centered coefficient in (1) is only a sparse Type II proxy estimate; it is not positivity of the original two-prime count. The result specifies where the relative 1/H² can actually be recovered without the weighted graph and where this independent argument stops.

## 4. One long residual slot can also be prime

Narrow the fixed exponent range to θ+τ<1/3. Replace F by

    F_P(z) = Σ_{m p r=z, p∈[P,2P] prime, p∤N, r prime} α(m) log r,

and keep G unchanged. There is an unconditional expansion at the same sparse scale with a principal term and **at most one explicit exceptional-character term**. Define X=10Z/(UP), and choose a sufficiently small fixed c>0; write χ_0,β0 only if a primitive real exceptional character and zero occur in the zero-free cut at conductor ≤exp(c sqrt(log X)), as specified below. Write J=(a,b] after intersecting with positive z−A. Define

    V_w^P(A) = ∏_{ℓ≤w, ℓ∤A} (1−1/(ℓ−1)),
    B_φ = Σ_{m',p' allowed} β(m')/φ(m'p'),
    A_1 = Σ_{m,p allowed} α(m)/(mp).
   
Here and below d=mp and d'=m'p' include the given α or β support and the genuine designated prime, respectively. Then

    Σ_{z∈J∩ℤ} F_P(z) G(z−A)
      = (b−a) V_w^P(A) A_1 B_φ 
        − [(b^{β0}−a^{β0})/β0] χ_0(A) A_χ B_φ E_w(A,χ_0)
        + O_B((Z/H²)L^{−B}),                                          (2)

where the second term is omitted if the exceptional character is absent or gcd(A,cond χ_0)>1. The factors in that term are

    A_χ = Σ_{m,p allowed} α(m) χ_0(mp)/(mp)^{β0},
    E_w(A,χ_0) = Σ_{s|P(w), (s,A)=1, cond χ_0|s} μ(s)/φ(s).

In particular, if both A_1 and A_χ (when needed) vanish, the signed estimate for two-cell support is O_B((Z/H²)L^{−B}) with **three actual prime slots** (p,p',r). The companion residual of G is still only a rough integer.

### Effective small-conductor subtraction

The exact standard input used for (2) is the following fixed-power-below-square-root form. For each fixed ε>0, X≥3, Q≤X^{1/2−ε}, let χ_0 be the possible exceptional primitive real character of conductor ≤R=exp(c sqrt(log X)), its possible zero having β_0≥1−c_* /sqrt(log X) for a sufficiently small fixed c_*>0. For the prime-only weight θ(y;q,a)=Σ_{p≤y,p≡a mod q}log p, the sum over q≤Q of the maximum, over 1≤y≤X and reduced a mod q, of

    | θ(y;q,a) − y/φ(q)
             + 1_{cond χ_0|q} χ_0(a) y^{β0}/(β0 φ(q)) |

is O_ε(X exp(−c_ε sqrt(log X))). If there is no such χ_0 zero, omit its term.

Here are details to delimit this input from an assumption of exponential Siegel–Walfisz. Split the primitive conductors at R after orthogonality; inducing from a character of conductor v costs the sum over v|q≤Q of 1/φ(q), at most O(log Q)/φ(v) by φ(vu)≥φ(v)φ(u) and Σ_{u≤Q}1/φ(u)≪log(2Q). For v≤R, the classical zero-free region up to T=exp(sqrt(log X)) and the Landau–Page uniqueness statement allow a common line 1−c_*/sqrt(log X) except for at most the single real zero stated above, which is retained. The effective prime number theorem with its possible exceptional term retained gives the principal term, that exceptional term, and error O(X exp(−c' sqrt(log X))). In the truncated Perron argument, subtract the poles at 1 and the possible exceptional zero and move to a line 1−c_*/(2 sqrt(log X)) inside the common zero-free strip. The logarithmic derivative after these subtractions is bounded by a power of log X there, by the local logarithmic-derivative formula and zero count. The contour can remain near 1, so a zero close to 0 paired with the exceptional zero does not require an absolute reciprocal bound. The same formula handles y≥X exp(−c'' sqrt(log X)); below this the trivial O(y log y) plus the possible O(y^{β0}) suffices. One may use half-integer endpoints for the explicit formula, changing integer sums by no more than O(log X). The small c in R can be chosen smaller than the resulting absolute exponential error exponent, so summing this error over primitive v with weight 1/φ(v) still saves exp(−c''' sqrt(log X)). For v>R use the maximal Vaughan mean-value estimate of [Akbary–Hambrook, Theorem 1.2](https://arxiv.org/abs/1309.2730): on a dyad of conductors of size D the 1/φ(v) weighted sum is, up to fixed log powers,
    O(X/D + X^{1/2}D + X^{2/3}D^{1/2} + X^{5/6}).
Dyadic summation gives the same exponential saving for Q≤X^{1/2−ε}. For the small-conductor region and exception see also [Yamada, Lemma 1.3 and the explicit-formula argument](https://arxiv.org/pdf/1306.5322); we use the ordinary zero-free region, not his particular logarithmic choice of split. Induced characters lose at most O((log X)(log q)) per modulus after averaging, by prime powers at primes dividing q. Removing all proper prime powers costs at most O(Q sqrt X (log X)^2), also absorbed. This proves the input with the retained term, without any assumption about the actual existence of such a zero.

### Proof of (2)

For fixed d, the prime r=z/d is in J/d and in the reduced class A d^{-1} mod d' when (d,d')=1. The latter coprimality is required as in (1), and both d,d' are units modulo A. For ℓ≤w dividing A, r=(A mod ℓ)=0 would force r=ℓ, impossible since r≥Z/(4UP) and w≤W. For the remaining ℓ, excluding (r'≡0 mod ℓ) on the other side excludes exactly the reduced residue r≡A d^{-1} mod ℓ. Expand this roughness condition by the same Bonferroni orders as before, now over primes not dividing A. The modulus for each remaining term is q=d's, with d' W-rough and s w-smooth; the corresponding progression is reduced. The marked sequence d' may have several factorizations m'p', but only O_τ(1), because each possible p' is a genuine prime of order N^τ. Thus, for each **fixed d**, uniqueness of the W-rough part of q means each q occurs O_τ(1) times, and the maximum-error estimate above applies after coefficient bounds. Since θ+τ<1/3 we have q≤4UPY≤X^{1/2−ε} for a fixed ε>0 and all large N. Summing over d (at most O(UP/H) tuples) gives error
    O((Z/H) L^{O(1)} exp(−c_ε sqrt(log X))) = O_B((Z/H²)L^{−B}).

For clarity on the Bonferroni gap, its nonnegative terminal AP contributions have total main bounded by O(Z/H²) times
    [Σ_{ℓ≤w,ℓ∤A} 1/(ℓ−1)]^{J₀}/J₀!,
because 1/φ(d')≪1/d' uniformly, the exceptional term is in absolute value at most O(Z/d)·1/φ(d's) for J/d, and the sum over tuples with absolute coefficients costs only fixed log powers. The same maximum-error estimate applies to that terminal layer. Consequently upper/lower bracketing against the nonnegative prime count can be used before inserting the complex coefficients, and its summed error is arbitrarily log-small at the sparse scale. Replacing the truncated principal factor by the Euler product, and the truncated exceptional s-sum by the full finite sum stated above, has the same bound: inclusion-exclusion by itself brackets the *principal* factor, but for the restricted exceptional sum argue as follows. If the conductor q0 is not squarefree, has a prime >w, or shares a prime with A, the exceptional sum is zero. Otherwise its fixed squarefree factors can be pulled out:
    E_w(A,χ_0)= [μ(q0)/φ(q0)] ∏_{ℓ≤w,ℓ∤Aq0}(1−1/(ℓ−1)).
If ω(q0)≤J₀/2, the remaining truncation at order at least J₀/2−1 has an arbitrarily log-small model tail, again by Bonferroni. If ω(q0)>J₀/2, then 1/φ(q0)≤2^{1−ω(q0)} (every odd prime contributes at least 2), while the sum of absolute model weights over the remaining primes is ≪(log w)^O(1). Both the full and truncated sums are already arbitrarily log-small in that case.

In the exceptional term, q0<R<W and q0|d's imply q0|s, since every prime factor of d' exceeds W. The residue character thus factors exactly as χ_0(A)χ_0(d), and the interval factor as (b^{β0}−a^{β0})/(β0 d^{β0}). The coefficient attached to d is always O(Z/d) in absolute scale, even in the exceptional component, because Z/d≥1 grows polynomially and β0≤1. Therefore removing the compatibility condition (d,d')=1 from the main terms costs the same negligible errors checked after (1), using the absolute Euler products as polylogarithmic majorants. This proves (2).

The two moment conditions can be realized with an actual prime coefficient minus a bounded rough proxy. For example take a full cell of length comparable to U/H. In the exceptional case split the allowed rough integers by χ_0(m)=±1 and fit one constant in each class to preserve the ordinary and exceptional harmonic means of the prime coefficient. Both classes have asymptotically half the rough mass by Bonferroni and CRT modulo q0: all q0 prime factors are below W, the total residue-count errors cost at most q0Y times a polylogarithmic factor and are negligible against the cell length, and allowed integers sharing a prime >W dividing N have total ≪ (U/H)L/W+L. The masses after weighting by 1/m and 1/m^{β0} are comparable within each sign and obey V_±/U_±≈U^{1−β0}; the 2 by 2 determinant is −U_+V_−−U_−V_+, so solving costs only a constant times the original coefficient bound. In the absence of χ_0 only the ordinary mean needs fitting. This construction does not assert arbitrary small-character/Mellin discrepancy simultaneously, nor does it replace the final rough variable by a prime.
