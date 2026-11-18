# The Haar variance conjecture for Shannon entropies of projective bases

Natural logarithms. Let B_1,…,B_L be any orthonormal bases of C^d, d,L≥2. Put H_b(ψ)=−Σ_i p_{bi} log p_{bi}, p_{bi}=|〈u_{bi},ψ〉|², and H̄=Σ_b w_b H_b for positive weights of sum 1. Var is over Haar pure states, not over the labels b. If an L-tuple U of pairwise mutually unbiased bases exists, then Var_U is independent of its equivalence class and

$$
 \operatorname{Var}_{\mathcal B}(\bar H)-\operatorname{Var}_{\mathcal U}(\bar H)
 =\frac{2}{d(d+1)}\sum_{b<c}w_bw_c\sum_{k\ge2}
 \frac{\sum_{i,j}o_{bcij}^{\,k}-d^{2-k}}{k^2(k-1)^2},\qquad
 o_{bcij}=|\langle u_{bi},u_{cj}\rangle|^2.
 \tag{V1}
$$

In particular the difference is ≥ [1/(2d(d+1))] Σ_{b<c} w_b w_c Σ_{i,j}(o_{bcij}−1/d)². Equality holds exactly for pairwise unbiased bases. The equal-weight, prime-power, L=d+1 consequence is precisely Conjecture 2 of Puchała, Rudnicki, Chabuda, Paraniak and Życzkowski (2015), which was proved there for Tsallis entropy of order two rather than Shannon entropy. Variance and its nonnegative square root have the same minimizers.

**Proof.** Write g=√T ψ, g a circular complex Gaussian with density π^{−d}e^{−||g||²}. By radial symmetry T~Gamma(d,1) is independent of Haar ψ, with E T²=d(d+1). Write X_{bi}=|〈u_{bi},g〉|². All X have Exp(1) marginals and Σ_i X_{bi}=T for every basis. With f(x)=x log x−x+1, f(0)=1 and W_b=Σ_i f(X_{bi}),

    Σ_b w_b W_b = A(T)−T H̄(ψ),     A(T)=T log T−T+d.

Since E H̄ does not depend on the bases (unitary invariance), subtracting the second moments of the left sides for two tuples yields exactly E T² times the difference of the variances of H̄. The same-basis terms in that difference cancel, leaving twice the weighted sum over pairs b<c of differences E[W_b W_c] relative to an unbiased pair.

For s>0 let R_s(x)=e^{−sx}−e^{−s}+s(x−1)e^{−s}. This is nonnegative by the tangent inequality for the convex exp function. Then

    f(x)=∫₀^∞ R_s(x) ds/s² .

For x>0, both sides and their first derivatives vanish at x=1 and both second derivatives equal 1/x, by differentiation on compact subsets of (0,∞). The same identity at x=0 follows by monotone convergence as x decreases from 1. Thus f truncated to s∈[1/n,n] tends increasingly to f and in L²(Exp(1)), since 0≤f_n≤f and f is square-integrable. Work first on this finite interval for both s,t.

When expanding E[(Σ_i R_s(X_{bi}))(Σ_j R_t(X_{cj}))], everything except the product of the two exponential sums is independent of the pair of bases: Σ_i R_s(X_{bi})=Σ_i exp(−sX_{bi})−d exp(−s)+s(T−d)exp(−s), and the joint law of T and the single-basis intensity vector is basis-invariant. For unit u,v, o=|〈u,v〉|², the remaining joint transform is

    E exp(−s|〈u,g〉|²−t|〈v,g〉|²)
      = det(I+s uu*+t vv*)^{−1} = [(1+s)(1+t)−st o]^{−1}.

The first equality follows by diagonalizing the quadratic form and integrating exponential variables, the second by the rank-two determinant formula, also valid at o=0,1. Put a=(1+s)(1+t) and R=st/a∈(0,1). Subtracting the same sum for an unbiased pair gives

    a^{−1} Σ_{k≥2} R^k (Σ_{ij} o_{ij}^k − d^{2−k}).

The constant and linear terms cancel since Σ o_{ij}=d; every displayed summand is nonnegative by Jensen. Thus the integrals of the difference on the increasing square converge by Tonelli/monotone convergence and can be integrated termwise. The left side converges by L² convergence of the truncated sums. Each factor in the separated coefficient integral is ∫₀^∞ s^{k−2}/(1+s)^{k+1} ds=1/[k(k−1)], by x=s/(1+s). This proves (V1). The k=2 term alone gives the stability bound since Σ o²−1=Σ(o−1/d)². The series at o=1 is absolutely convergent. ∎

No assertion is made about existence of MUBs in any presently unknown dimension or size. Nor does minimum variance imply optimal worst-case extrema.
