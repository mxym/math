# A crossover at the critical power

In the setup of PROOF.md let L=log n, h_m=H_{m−1} for m≥2 and h_1=0. The following conclusion is about log *clade sizes*, not the decrement in size when a sibling splits off. For every fixed continuous real test function f on [0,1] and finite q≥1,
```
X_n(f)=(nL²)⁻¹ Σ_{v internal} |v| f(log|v|/L)  →  ζ(2)⁻¹∫₀¹ x f(x) dx     in L^q.
```
In particular S_n(1+λ/L)/(nL²) converges to ζ(2)⁻¹∫₀¹ xe^{λx} dx in L^q, uniformly on every fixed compact real λ-interval in the sense that the L^q norm of the supremum error vanishes.

To see this, put one independent Exp(1) weight H_{|v|−1}τ_v on each summand conditional on the finite tree, as in the fixed-power proof. The resulting variable A_n(f) is the time integral in v∈[0,∞) of
```
I_n(v) = (1/n) Σ_{i=1}^n f(log M_i/L) h_{M_i}/L,
```
where M_i is the size of the sampled block containing label i at homogeneous fragmentation time vL. The extra factor L comes from dt=L dv. The size M=M_1 at fixed v is 1+Bin(n−1,P), conditionally on the interval containing a distinguished uniform label, where P is that interval's mass at vL. The tagged mass process is e^{-ξ_t}, with ξ a subordinator of finite mean ζ(2) per unit time: see [Aldous–Janson II, §3.1 and §5, tagged subordinator](https://arxiv.org/html/2303.02529v3). For the time sequence t=vL, the strong law gives log P/L→−vζ(2) a.s. for v>0. Thus log M/L→x_v=(1−vζ(2))_+ in probability. In detail, if vζ(2)<1, the conditional binomial mean grows as n^{1−vζ(2)+o(1)}; Chebyshev relative concentration gives the assertion. If vζ(2)≥1, for each ε>0 the conditional mean is eventually ≤n^{ε/2} and Markov's inequality bounds the conditional probability of M≥n^ε by (1+n^{ε/2})n^{-ε}. The t=0 case is deterministic. Since |h_m−log m|≤1 and f is bounded continuous, the tagged integrand converges in every finite L^q to f(x_v)x_v, by boundedness. Jensen over the n exchangeable labels gives the same conclusion for the empirical average I_n(v); tag independence is not required.

For v≥1, the two-tag identity gives P(M≥2)≤E(M−1)=(n−1)e^{−vL}≤2^{1−v}. Since h_1=0, boundedness and Jensen yield ||I_n(v)||_q≤C||f||∞2^{(1−v)/q}; at v∈[0,1] use the constant bound instead. Dominated convergence and Minkowski give
```
A_n(f)→ ∫₀∞ f(x_v)x_v dv = ζ(2)⁻¹∫₀¹ f(x)x dx
```
in every finite L^q. The finite genealogy conditional expectation is X_n(f); conditional clock variance is Σ_v [|v|f(log|v|/L)/(nL²)]² ≤ ||f||∞² X_n(1)/L². Boundedness of E X_n(1)=E A_n(1) and interpolation, using |X_n(f)|≤||f||∞ X_n(1) and conditional Jensen for the latter, give the asserted convergence. For λ in a compact interval, x↦e^{λx} varies Lipschitz-continuously in λ in the uniform norm there. The Lipschitz bound on λ↦X_n(e^{λ·}) is at most a fixed constant times X_n(1), bounded in L^q; the limit has a bounded Lipschitz constant as well. Approximating by a finite mesh and then shrinking its spacing proves the uniform claim. This does not cover diverging λ.

Source boundaries: tagged-subordinator SLLN and paintbox sampling are prior; the rate-rescaled clock device is explicit in Ma's maximum-height paper. The fixed-λ family is the transform of the normalized clade-mass empirical log-size measure, not a CLT for the size decrements of one particular ancestry. The same test-function conclusion follows by testing a uniformly tagged leaf first and averaging; it is not a new fragmentation or clock construction.
