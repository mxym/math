# Sharp dimension-uniform concavity for Rényi entropy along the linear heat flow
Private research candidate, 18 November 2026. Author-side derivation and checks only; not an external review or a priority claim.

## 1. Statement and positioning
Let `P_t=exp(t Δ)` on Euclidean space of dimension d, i.e. independent additive Gaussian noise of covariance 2tI. Given a probability density f, let h(t)=log ∫(P_t f)^α /(1−α) for finite α>0, α≠1, and use the ordinary differential Shannon entropy for α=1. The division by 1−α is outside the logarithm. For β>0 put N(t)=exp(β h(t)/d).

* **Plain entropy:** h is concave for all dimensions and data (for which the functional is finite) exactly when 1≤α≤2.
* **Entropy power:** N is concave for all dimensions and data (on its finite domain) exactly when 1≤α<2 and 0<β≤2(2−α).

Precisely, for every excluded α in the first statement, or every excluded pair (α,β) in the second, there is a finite d and a smooth strictly positive radial probability density with exponential tails so that the corresponding second derivative is **strictly positive** for all sufficiently small positive times. These statements characterize a single interval/region valid simultaneously in every dimension; they do not describe the sharp parameters in each fixed dimension. We make no claim about higher derivatives, nonlinear diffusion, or the fundamental solution alone. Absolute normalization and the choice Δ vs Δ/2 do not change the signs.

The positive directions are **prior results**, Wu–Yu [1, Thms 5, 8]; the Shannon endpoint is Costa's theorem. Our candidate contribution is the matching necessity, particularly the nontrivial sharp threshold below exponent 2 and the dimension-uniform sharpness question for general Euclidean initial data in [1, Remark 1]. The restriction of [1, Thm 3] to fundamental solutions is **not** settled by arbitrary heat flows.

## 2. An instantaneous curvature ratio
Use escort measure dμ=w² dx /U with w=(P_t f)^{α/2}, U=∫w², and expectations E, variances and covariances under μ. Put A=Δw/w, B=|∇log w|², b=EB, δ=2/α−1. For our smooth test data all integrations by parts and differentiations below are justified in §5. We first compute at such data, without any dimensional limit. Define G=∫|∇w|²=Ub. Since P_t f=w^{1+δ},
```
w_t=w(A+δB),   EA=−b,   U'=−2(1−δ)G,
G'=−2∫Δw · w_t=−2U E[A²+δAB].
```
Thus h'=(4/α)b. At α=1 this follows instead by one integration by parts in Shannon entropy, with U=1. Differentiating b=G/U gives
```
h''=−(8/α){Var(A)+δ Cov(A,B)}.
```
In particular the dimension-normalized ratio
```
T := −d h''/(h')² = (αd/2) · {Var(A)+δ Cov(A,B)}/b²              (1)
```
is meaningful for our nonconstant profiles (b>0). N''=(β/d²)N(h')²(β−T); h''>0 iff T<0. Multiplying w by a positive scalar does not affect (1). The transformation and derivative structure are related to [1, sec. VII] and [3]; we do not claim the heat identities as new.

## 3. One radial shell and exact rational moments
Select λ>0; take positive integers d→∞, and set k=λd/2, m=k−d/2. Use an auxiliary profile w=r^m exp(−r²/2), r=|x|. Do **not** presume w^{2/α} normalizable near zero: all calculations at present refer only to (1)'s static right side; actual densities are constructed below. For d>4 and k>2 all static moments exist. Under its normalized squared measure the random variable z=r² has Gamma(k,1) distribution (Lebesgue density z^{k−1} exp(−z)/Γ(k)). A direct radial Laplacian calculation gives
```
J=m(m+d−2),  H=m²,
A=z−2k+J/z,  B=z−2m+H/z,   b=k−2m+H/(k−1).
```
Put V(a,c)=Cov(z+a/z,z+c/z). Gamma recurrence gives
```
V(a,c)=k−(a+c)/(k−1)+ac/[(k−1)²(k−2)].                         (2)
```
Indeed Ez=k, E(1/z)=1/(k−1), E(1/z²)=1/[(k−1)(k−2)], and E(z²)=k(k+1). Hence all quotients T for the auxiliary profile are elementary rational expressions when α,λ are rational:
```
T(d,λ,α) = (αd/2)[V(J,J)+δ V(J,H)]/b².                         (3)
```
For fixed λ, m/k=1−1/λ; J/k²→1−1/λ² and H/k²=(1−1/λ)². Thus b/k→1/λ². If a/k²→a₀ and c/k²→c₀, equation (2) gives V(a,c)/k→(1−a₀)(1−c₀), so
```
V(J,J)/k→λ^(−4),   V(J,H)/k→(2λ−1)λ^(−4).
```
Since d/(2k)=1/λ, (3) tends to
```
(α/λ)[1+δ(2λ−1)] = 2(2−α) + 2(α−1)/λ.                        (4)
```
There is no uniformity in λ required.

## 4. Quantifiers and boundary cases
Test threshold γ=0 for plain entropy and γ=β>0 for entropy power. If 0<α<1, the limit (4) tends to −∞ as λ↓0, so take λ>0 sufficiently small that (4)<γ. If α>2, its λ→∞ limit is negative, so take λ finite sufficiently large that (4)<γ. If 1<α≤2 and β>2(2−α), the same large-λ selection works, including α=2 and every β>0. For α=1 the expression (4) is 2, and the Gaussian already shows failure for every β>2 (indeed T=2). For any such **fixed** λ choose a finite d>4 with k>2 sufficiently large for the strict inequality T(d,λ,α)<γ. Section 5 preserves it under a fixed regularization and for an interval of strictly positive times. At the allowed equality boundary we rely on [1]; β=0 as an exponential would make N identically 1, not the plain entropy, hence is deliberately excluded. For α=2 the ordinary entropy remains concave.

## 5. Making the test into an actual smooth heat trajectory
For fixed α,λ,d as chosen, let 0<ε≤1, R≥1 and use
```
w_{ε,R}(x)=(r²+ε²)^{m/2} exp(−g_R(r)),
g_R(r)=R²(√(1+r²/R²)−1)=r²/(√(1+r²/R²)+1).
```
Both factors are smooth and positive on all of Euclidean space. Let ε↓0 and R→∞, say along (ε,R)=(1/j,j). Away from r=0, w_{ε,R}, its first and second derivatives converge to those of the auxiliary profile. Globally,
```
|∇log w_{ε,R}|≤C(r+r^{−1}),  |Δ log w_{ε,R}|≤C(1+r^{−2}).
```
Indeed |g_R'|≤r, |g_R''|≤1, |g_R'/r|≤1, and the radial derivatives of the logarithmic factor obey |(log(r²+ε²))'|≤2/r and |(log(r²+ε²))''|≤2/r². Also g_R(r)≥√(1+r²)−1. For r≤1 the squared weight is bounded by C r^{2 min(m,0)}; for r≥1 it is bounded by C(1+r)^{2|m|}exp(−2(√(1+r²)−1)). Using A=Δ log w+B, all integrands needed to normalize μ and to compute E A, E B, E A², E AB are dominated at zero by C r^{2 min(m,0)−4} and at infinity by an integrable exponential times a polynomial (before multiplying by the polar Jacobian). Integrability at zero follows from d>4 and 2k=d+2m>4. Dominated convergence implies that the static ratio for these regularized profiles tends to (3). Thus some fixed finite j retains the strict sign.

For this j set f=w_{ε,R}^{2/α}/∫w_{ε,R}^{2/α}. It has positive finite mass and finite entropy moments of every positive order; the integral in the denominator can vary wildly along j, but cancels exactly from (1), and no convergence of the unregularized f is required. All spatial derivatives of log f of orders 1 through 4 are globally bounded for fixed ε,R: this follows by differentiating the smooth functions log(r²+ε²) and √(1+r²/R²), whose derivatives of those orders are bounded at infinity and on bounded sets. Hence |D^a f|≤C_a f for |a|≤4. With L=||∇log f||∞ the ratios f(x+y)/f(x) lie in [exp(−L|y|),exp(L|y|)], so, uniformly for 0≤t≤1,
```
c f(x) ≤ P_t f(x) ≤ C f(x),       |D^a P_t f|≤C_a P_t f.
```
The first bound follows by averaging over the Gaussian increment; the second follows by differentiating the convolution against derivatives of f. These derivatives are continuous down to t=0, as are ∂t P_t f=ΔP_t f and ∂tt P_t f=Δ²P_t f from the right. In particular the terms obtained by twice differentiating ∫(P_t f)^α are dominated by a constant times f^α and, for the Shannon case, by C f(1+|log f|). For G' and the integrations by parts in §2, w and its spatial derivatives up to third order and w_t,∇w_t are bounded by a constant times w; its square has exponential decay. Using cutoffs on balls and dominated convergence justifies the identities and continuity of h',h'' down to t=0. Thus the strict sign in §4 persists on 0<t<t₀ for a bona fide heat flow with general smooth initial data.

## 6. Prior results and limits
1. H. Wu and L. Yu, [On the Concavity of Rényi Entropy and Rényi Entropy Power along Heat Flows on Manifolds](https://arxiv.org/html/2611.13040v1), 9 Nov 2026. Theorem 5 (Euclidean arbitrary data) proves h''≤0 for α∈[1,2]. Theorem 8 proves entropy-power concavity for 0<β≤2(2−α). Section VI-C, Remark 1 explicitly leaves optimality of the interval open; sec. VII-A notes the prior obstruction β≥2 for α≠1. Their separate fundamental-solution theorem has different quantifiers. Costa's classic theorem is the Shannon endpoint.
2. H. Wu, L. Yu and L. Guo, [On the Complete Monotonicity of Rényi Entropy](https://arxiv.org/abs/2312.01819), IEEE Trans. Inf. Theory (2025). In one dimension there is a larger positive interval for plain entropy, including 0<α≤3. No assertion here contradicts or sharpens that fixed-dimensional result.
3. L. Sun, [Concavity of Tsallis Entropy and Tsallis Entropy Power along Heat Flow](https://arxiv.org/html/2601.12944v3), revised June 2026: the power-time evolution, square-root substitution, prior dimension-free estimates and Tsallis classification differ from the normalized Rényi curvature. Its sharp upper Tsallis endpoint already implies failure for Rényi when α>3: writing U=∫u^α and S=(1−U)/(α−1) gives h''=S''/U+(α−1)(S')²/U². The lower-index Gaussian Tsallis obstruction does not imply the analogous Rényi statement.
4. H. Wu and L. Yu, [Entropic Isoperimetric and Cramér–Rao Inequalities for Rényi–Fisher Information](https://arxiv.org/html/2504.01837v2), Thm 6 and Remark 2: the exponent β=2, in our convention, and all β≥2 were already excluded for α≠1. Their entropy-power inequality for adding a Gaussian is a different global inequality.
5. G. Savaré and G. Toscani, [The Concavity of Rényi Entropy Power](https://arxiv.org/abs/1208.1035) treat nonlinear porous-medium/fast diffusion; it is not a theorem about P_t=exp(tΔ) for general α. Higher-entropy-derivative counterexamples for Shannon entropy concern a different question.

We searched the explicit Wu–Yu sharpness question, indexed subsequent papers and earlier terms including Lᵖ norm log convexity, dimension-uniform heat-flow curvature and entropy-power exponents. These checks found no matching full classification; they cannot establish priority; no assertion of first discovery. Excludes α=0,∞, β≤0, restrictions to log-concave inputs, specified finite dimensions, and heat kernel/fundamental solution claims.
