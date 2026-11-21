# A flat-passband major-arc formula with a moving central weight

**Results.** At a fixed dyadic scale X, an exactly flat Fourier cutoff yields a smooth major-arc approximation with no auxiliary interval-shortening parameter and works through all powers R=X^ρ with ρ<1/2. Its difference from the true central binary correlation has unconditional mean square O(X^(3+ε)/R+X^(31/12+ε)) using the cited Maynard–Pandey–Radziwiłł estimate. A second calculation gives a pointwise major-arc main term when a finite local region of Dirichlet zeros has real parts ≤θ and ρ<1−θ. This does **not** control the minor arcs at a single target. In particular it is not a Goldbach proof and does not improve the known 7/12 conditional exceptional exponent.

The starting reference is [Grimmelt–Bhowmik, arXiv:2607.27282v2, §7](https://arxiv.org/html/2607.27282v2#S7). Their printed Lemma 7.3 applies Parseval to a sum in N with a weight S_φ that still depends on N in (7.2), and in Lemma 7.2 the cutoff can also depend on N. Parseval alone is not the indicated diagonal inequality for varying functions. The proof below supplies the diagonal step explicitly with a derivative in the slow scale parameter. It also uses a signed spatial kernel to obtain an exactly flat Fourier passband, whereas the positive compactly supported spatial kernel in §7 gives a passband error and ε-like shortening parameter. This addresses those steps, not the validity of the rest of their paper.

## 1. Exact smooth frequency cutoff

Fix a nonnegative φ∈C_c^∞((1/5,4/5)) with c_φ=∫φ(u)φ(1−u)du>0, and a real even h∈C_c^∞((-2,2)) with 0≤h≤1 and h(v)=1 for |v|≤1. Throughout consider integers X/2≤N≤X and t=N/X. For t independently in [1/2,1] put

    S_t(α)=Σ_n Λ(n) φ(n/(tX)) e(nα),
    I_t(β)=∫_0^∞ φ(u/(tX))e(βu)du,
    r_φ(N)=∫_0^1 S_{N/X}(α)^2 e(−Nα)dα.

Let T_q=Xq/R and define the periodized multiplier

    H_R(α)=Σ_{q≤R} Σ^*_{a mod q} Σ_{k∈Z} h(T_q(α−a/q−k)).

If 4R²<X, its support arcs with outer radii 2R/(qX) are pairwise disjoint: distinct fractions are separated by at least 1/(q q′). The inner arcs of radius R/(qX) have H_R=1 exactly, and 0≤H_R≤1 throughout. The n-th Fourier coefficient is exactly

    b_R(n)=Σ_{q≤R} c_q(n) T_q^(−1) check h(n/T_q),

where c_q is the Ramanujan sum and check h is the inverse continuous Fourier transform. This coefficient sequence has a Schwartz rather than compactly supported envelope. Its underlying continuous function is signed, has integral 1, and has all positive integer moments zero, because h is constant near zero. Making this replacement costs no positivity in the Fourier cutoff; the frequency multiplier itself is nonnegative. It is the spatial kernel that is not nonnegative.

Write r_maj(N)=∫ H_R S_{N/X}²e(−Nα) and r_min=r_φ−r_maj. These quantities are real by reflection α↦−α.

## 2. Unconditional diagonal mean-square estimate

For any ε>0, uniformly for 1≤R with 4R²<X,

    Σ_{X/2≤N≤X} |r_min(N)|²
           ≪_{φ,h,ε} X^(3+ε)/R + X^(31/12+ε).                       (1)

Use [Maynard–Pandey–Radziwiłł, arXiv:2608.14777v1, Theorem 1.1](https://arxiv.org/html/2608.14777v1#Thmtheorem1) for prime exponential sums. On the complement of the inner arcs, let Y∈[X/10,X] and choose a reduced a/q by Dirichlet with q≤√Y, |β|≤1/(q√Y). Then B_Y=max(q,qY|β|)≳R: if B_Y<R/10 one would have q≤R and |β|≤R/(qX), contrary to the choice of α. The theorem gives the uniform bound, after summation by parts,

    |S_t(α)|+|∂_t S_t(α)| ≪_ε X^ε(X/√R+X^(19/24)).

The derivative weight −n/(t²X)·φ′(n/(tX)) has the same compact support and uniformly bounded variation. Also ∫|S_t|²+∫|∂_t S_t|²≪X log X by ordinary Parseval and the prime number theorem upper bound on ΣΛ(n)².

For the moving t, let f_n(t) be the n-th Fourier coefficient of F_t=(1−H_R)S_t². The elementary one-dimensional Sobolev inequality gives

    |f_n(n/X)|² ≪ ∫_{1/2}^1 (|f_n(t)|²+|f_n′(t)|²)dt.

For example choose a point where |f_n|² is at most twice its integral, apply the fundamental theorem of calculus and Cauchy–Schwarz. Sum over n∈[X/2,X]; only now apply Parseval in n, to F_t and ∂_tF_t at each fixed t. There is no dependence of H_R on t. Since F_t and its derivative vanish on the inner arcs and |1−H_R|≤1, the result is at most

    C∫_{1/2}^1 ∫_{outside inner arcs}
                (|S_t|⁴+4|S_t|² |∂_t S_t|²)dα dt.

Insert the preceding pointwise and L² bounds, adjusting ε to absorb logs. This gives (1), since 2·19/24+1=31/12.

## 3. A pointwise major-arc estimate from local zero information

Let θ∈[1/2,1), δ>0 be fixed and R=X^ρ with 0<ρ<min(1/2,1−θ). At scale X the following **local** zero input suffices: for every primitive χ of conductor f≤R, including the conductor-one zeta function, every nontrivial zero with

    |Im ϱ| ≤ 10 X^δ (1+R/f)

has Re ϱ≤θ. This is implied by a fixed global zero-free strip with boundary θ, but it does not require any such assertion outside the displayed region. Under just this local input,

    r_maj(N)=c_φ S(N) N+o(X), uniformly on even X/2≤N≤X.             (2)

Here is a direct analytic bound that proves (2). On an expanded arc a/q+β, write B=X|β|≤2R/q and use the primitive-character explicit formula with smooth weight φ(u/(tX))e(βu). For every character induced modulo q, its primitive part obeys

    S_{χ,t}(β)=1_{χ principal} I_t(β)
                    + O_φ(X^θ √(1+B) log(qX)).

Indeed, for a zero with imaginary part γ, substitution u=Xv leaves an integral with phase γ log v+2π Xβv and a smooth amplitude on a compact v-interval in (0,1). For |γ|≪1+B it is O((1+B)^(−1/2)): if |γ| is comparable to B use the second-derivative bound; if much smaller, the first derivative has size ≫B; bounded B is trivial. The number of zeros in that range is O((1+B)log(q(2+B))), and their real parts are ≤θ. For |γ|≫1+B repeated integration by parts gives O_A(|γ|^(−A)) on the normalized integral. Up to the local cutoff the same real-part bound applies and their sum is negligible at scale X^θ√(1+B). Beyond the local cutoff |γ|≫X^δ(1+B), use only Re ϱ<1 and choose A arbitrarily large in terms of δ; their contribution is O(X^−2). The conductor bound is correct because f≤q, so 10X^δ(1+R/f) dominates X^δ(1+B). Trivial zeros and imprimitive changes contribute at most O_φ(log²(qX)); the latter are powers of the at most O(log q) primes dividing q. The smooth explicit formula is the usual Mellin form, as recorded for example in [Grimmelt–Bhowmik, Lemma 7.4](https://arxiv.org/html/2607.27282v2#S7.SS3). The same stationary-phase estimate under global GRH for the resulting additive sum is consistent with [Maynard–Pandey–Radziwiłł, §1](https://arxiv.org/html/2608.14777v1#S1).

For reduced a mod q set P_t(a/q+β)=(μ(q)/φ(q))I_t(β) on its expanded arc. Character orthogonality **before** taking absolute values gives

    Σ^*_{a mod q} |S_t(a/q+β)−P_t(a/q+β)|²
                       ≪_φ q X^(2θ)(1+B) log² X.

For the coprime parts, this follows from (1/φ(q))Σ_χ |τ(χ)|² |E_χ|² with |τ(χ)|≤√q; the discarded prime powers contribute O(φ(q) log^4 X), already absorbed. Integrating over |β|≤2R/(qX) and summing q gives

    ∫_{expanded arcs}|S_t−P_t|² ≪_φ X^(2θ−1) R² log³X,

since each denominator contributes O(X^(2θ−1)log²X·(R+R²/q)). Continuous Parseval and Σ_{q≤R} μ(q)²/φ(q)≪log(2R) give ∫_{expanded arcs}|P_t|²≪_φ X log X. By Cauchy–Schwarz, replacing S_t² by P_t² inside the H_R integral therefore costs, uniformly in t,

    O_φ(X^θ R log² X + X^(2θ−1) R² log³ X)=o(X).

Finally the pole integral equals

    Σ_{q≤R} c_q(N)μ(q)²/φ(q)² · ∫_{ℝ} h(T_q β)I_t(β)²e(−Nβ)dβ.

In the line above the integral is over the real line. Removing h in the continuous integral gives c_φ N at t=N/X by Fourier inversion. The error per q is O_{φ,A}(X(q/R)^A), since h=1 for |β|≤1/T_q and I_t(β) decays rapidly in X|β|. For each fixed ζ>0,

    Σ_{q>R}|c_q(N)| μ(q)²/φ(q)² ≪_ζ τ(N) R^(−1+ζ),

and the same bound holds for the head weighted by (q/R)^A if A>2. To check this, bound |c_q(N)| by (q,N)≤Σ_{d|(q,N)}d and φ(q)^(−2)≪_ζ q^(−2+ζ); for each d the remaining multiple sum is O_ζ(R^(−1+ζ)). For the head sum decompose q≤R dyadically and use the tail estimate at its lower endpoint. Since τ(N)=X^o(1) and R=X^ρ, taking ζ small yields o(1). The complete Ramanujan series is the usual Euler product S(N) for even N. These estimates prove (2).

## 4. What remains

Under the zero input, positive major arcs are now uniform at the specified scales, but (1) on its own can discard only up to roughly X/R+X^(7/12) targets, never even one arbitrary target. This is the correct scope of its combination with (2). In comparison [Pintz–Althöfer, arXiv:2610.15559v1, Theorems 1 and 3](https://arxiv.org/html/2610.15559v1) already have the 7/12+ε exceptional exponent from any fixed global boundary <1 and obtain a stronger conditional exponent for θ<2/3; our more elementary direct major-arc estimate does not replace those stronger results. It also does not assume the proposed external 7/8 theorem or any unverified GRH claim.

A uniform one-sided bound ruling out r_min(N)≤−(c_φ−κ)S(N)N for a fixed κ>0, plus (2), would suffice eventually for positivity on actual primes; the total prime-power error is O(√X log²X). None of the cited L^∞ minor bounds implies this: an unsigned bound from ∫|S|² is order X log X, and the mean-square passage fundamentally averages over targets. The new cutoff and diagonal repair leave the fixed-target signed estimate exposed rather than providing it.

## Independent check and 2026H2 comparison

The review checked the disjoint rational arcs at 4R²<X, fixed-scale use of the one-variable Sobolev inequality before Parseval, uniform two-weight applicability of the cited exponential-sum estimate, and the restricted conductor/height range in the explicit formula. The signed spatial kernel has no positivity property; the Fourier mask is nonnegative. No pointwise minor-arc bound or improved exceptional exponent follows here.

The dedicated July–21 November pass checked [Grimmelt–Bhowmik, arXiv:2607.27282v2](https://arxiv.org/html/2607.27282v2#S7), updated 13 August, in particular the smoothing and moving-target norm passage; [Maynard–Pandey–Radziwiłł, arXiv:2608.14777v1](https://arxiv.org/html/2608.14777v1#Thmtheorem1), 14 August; and [Pintz–Althöfer, arXiv:2610.15559v1](https://arxiv.org/html/2610.15559v1), 11 October, whose stronger conditional exceptional estimate is not superseded. [Uniformity, Local Structure and Boundary Correlations](https://www.preprints.org/manuscript/202610.3061) uses related Fourier averages, not the same flat passband and pointwise local-zero condition. Exact keyword and repository checks located no duplicate of this formulation, a bounded comparison and not a priority claim.
