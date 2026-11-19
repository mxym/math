# Non-Gaussian fluctuations of the external path length of the critical beta-splitting tree

Write T_n for the discrete n-leaf critical beta-splitting tree, EPL_n for the sum of the *edge-depths* of all its leaves, L=log n, and b=ζ(2). Use the coupled interval fragmentation and iid uniform label sequence of [Aldous–Janson III](https://arxiv.org/abs/2412.09655); P_i(t) are the interval masses. With 0 log 0=0, let
```
G(t)=−Σ_i P_i(t)log P_i(t),           M(t)=G(t)−bt .
```
**Theorem.** M is an L²-bounded martingale, with terminal value M∞. On this coupling
```
 (EPL_n−E EPL_n)/(n log n)   →   −M∞/b     in L² .
```
The limit is non-Gaussian: it has mean zero, variance (2ζ(3)−ζ(2))/ζ(2)^2 and strictly positive third moment. This does not assert third-moment convergence for the discrete sequence. The variance coefficient is already [Svihla–Lladser, Theorem 2.1 (10)](https://doi.org/10.1007/s11538-026-01655-x). The continuum martingale is minus the parameter derivative at r=1 of the classical additive fragmentation martingales exp(tκ(r))Σ_iP_i(t)^r, not a new general martingale. The new assertion is that it is the limit of the centered discrete statistic in this model.

### Shape increments

Let H_m=Σ_{j=1}^m1/j, d_m=H_{m−1} (d_1=0), and write u_m=E EPL_m/m. An m-leaf root has ordered child sizes i,j=m−i with q(m,i)=m/(2d_m i j). Define e(x)=−x log x−(1−x)log(1−x) and let μ_m=E_q e(i/m), β_m=E_q e(i/m)^2. For convenience μ_1=β_1=0. The Riemann sums with density ν(dx)=dx/[2x(1−x)] satisfy
```
 d_m μ_m → ∫e dν=b,       d_m β_m → ∫e² dν=:B.
```
For the first, symmetry writes the sum as the right-end mesh of −log x/(1−x) over x=i/m, 1≤i≤m−1. Its integral is ζ(2) by the geometric series; the logarithmic singularity at zero causes no issue because the integrand is monotone decreasing there (bound the discarded positive Riemann sum by its integral). For the second, e²/[x(1−x)] extends continuously to zero at both endpoints. In particular d_m μ_m and d_m β_m are uniformly bounded, μ_m=O(1/d_m). Integrating elementary log products gives
```
B=∫₀¹ x/(1−x) log²x dx + ∫₀¹ log x log(1−x) dx
 = 2ζ(3)−2 + 2−ζ(2) = 2ζ(3)−ζ(2).
```
The first integral uses x/(1−x)=Σ_{k≥1}x^k and ∫x^k log²x dx=2/(k+1)^3; the second uses −log(1−x)=Σ_{k≥1}x^k/k and Σ_{k≥1}1/[k(k+1)^2]=2−ζ(2).

By [Aldous–Pittel, Theorem 1.2](https://doi.org/10.1214/24-AAP2112), u_m=(log m)^2/(2b)+c₁ log m+O(1), with an absolute uniform remainder over integers m≥1. Conditional on a node of size m and writing x=i/m, its mean-zero split increment for EPL divided by m is
```
Δ_m = 1 + xu_i+(1−x)u_j−u_m
    = −(log m)/b [e(x)−μ_m] + R_m,     E_q R_m=0, |R_m|≤C .
```
Indeed the uncentered quadratic expansion contributes −(log m)e(x)/b and a bounded term since x log²x is bounded; the lower-order terms are bounded after cancellation. Center this bounded remainder. Revealing splits node by node, in breadth-first order for definiteness, these centered increments telescope exactly to EPL_n−E EPL_n after multiplying by each node size m, with independent conditional split law at each step. Both indicated pieces are martingale differences. We need the standard bound EΣ_v (m/n)^2=O(log n) (sum over all internal v, m its size). It follows e.g. from [Fuchs–Steel, Proposition 10 and Theorem 11](https://arxiv.org/html/2501.09270v2) for the pairwise MRCA: conditional on the tree, the sum is the expected number of common internal ancestors of 2 iid labels with replacement. Conditional on distinctness their number is one plus the MRCA's edge-depth, whose annealed mean is O(log n); the probability 1/n of equality adds at most (n−1)/n to the unconditional expectation since a binary n-leaf tree has maximum height at most n−1. Thus the squared L² norm contributed by Σ_v (m/n)R_m/L is O(1/L).

Put U_n=Σ_v(m/n)[e(i/m)−μ_m]. We next justify discarding log m/L in the centered increments. By martingale orthogonality the squared error is bounded by
```
 E Σ_v (m/n)^2 (1−log m/L)^2 β_m .                     (1)
```
A clade of size m, conditional on the discrete tree, has independent lifetime τ_v with mean 1/d_m in continuous time. Thus (1) equals the expected time integral over blocks of sampled size m≥2 of
```
 Σ (m/n)^2 (1−log m/L)^2 d_m β_m .
```
For fixed time this tends to zero: empirical frequencies of all positive-mass fragments converge to their true masses and in ℓ¹, by truncation to finitely many intervals of total mass ≥1−ε; on each such interval log m/L→1. The rest is bounded by a constant times its empirical mass. The expected integral over all time t is dominated pointwise by C e^{−t}: for m≥2, (m/n)^2≤2m(m−1)/[n(n−1)], and two distinct labels are in the same block at t with probability e^{−t}. Dominated convergence proves (1) vanishes. Altogether
```
 (EPL_n−E EPL_n)/(nL) + U_n/b →0 in L².                (2)
```

### The empirical entropy and removal of the clocks

Write G_n(t)=−Σ(m/n) log(m/n) over occupied sampled blocks at t. A visible split of a size-m block increases G_n by (m/n)e(i/m), with predictable rate d_m and split law q(m,i). The compensated process
```
 M_n(t)=G_n(t)−∫₀ᵗ Σ(m/n)d_m μ_m ds
```
is a mean-zero martingale. Its squared increment variance from t up to any later time is the integral of EΣ(m/n)^2 d_m β_m. By the same two-label bound, the tail from t to ∞ is O(e^{-t}) uniformly in n. Since the terminal sampled entropy is log n, telescoping the actual entropy jumps yields
```
 U_n=log n−Σ_v(m/n) μ_m,
 M_n(∞)=log n−Σ_v(m/n) μ_m d_m τ_v .
```
Their squared L² difference equals EΣ_v(m/n)^2 μ_m² by conditional independence of the unit exponentials. On m≤n^{1/4} this is O(n^{-1/2}) by counting at most n−1 nodes and μ_m≤log 2. On larger m it is O(L^{-2}) EΣ(m/n)^2=O(1/L). Therefore U_n−M_n(∞)→0 in L².

At fixed t the empirical entropy converges to G(t) in L². Indeed, condition on the interval masses p=(p_i). For a uniform label in block I, −log p_I is a tagged subordinator at time t with Lévy density dy/(e^y−1); it has finite moments of every order (positive exponential moments of order <1). Thus conditional entropy G(t) is finite a.s. By coordinatewise convergence and nonnegativity, liminf G_n(t)≥G(t) almost surely. By Gibbs' inequality empirical entropy is at most the empirical mean of −log p_I over the n labels, which conditional on the fragmentation converges a.s. to G(t) by the iid strong law. These empirical means have uniformly bounded fourth moments by Jensen, yielding L² convergence. The compensator integrand converges to b at fixed time, since Σ(m/n)=1, d_m μ_m is uniformly bounded and tends to b for every positive mass (truncate as above). Bounded convergence on the finite interval gives M_n(t)→G(t)−bt in L².

The fragmentation branching property and the tagged mean imply E[G(t+s)|F_t]=G(t)+bs, so M(t) is a martingale in the fragmentation filtration. Passing the finite-n tail bound to its increments via fixed-time L² convergence gives E|M(t+s)−M(t)|²≤Ce^{-t} uniformly in s≥0. Hence M(t)→M∞ in L² and a.s. Taking fixed t and then t→∞ shows M_n(∞)→M∞ in L². Equation (2) proves the limit assertion.

### Non-normality and sign

Write Z_r(t)=Σ P_i(t)^r. For r>1, E Z_r(t)=exp(−κ_rt), with κ_r=∫(1−x^r−(1−x)^r)ν(dx)=ψ(r)+γ; in particular κ₂=1 and κ₃=3/2. Let B_j=∫e(x)^j ν(dx) (thus B_1=b,B_2=B). The Poisson splitting representation has at a block of mass y a jump in entropy of y e(x) with dislocation intensity ν(dx)dt. Indeed, integrate the negative log tagged mass over uniform tags; along each tag this is the sum of its log jumps with no continuous drift, and summing nonnegative jumps over all tags gives exactly the mass-weighted entropy jumps. Their compensator is B_1 Z_1(t)dt=b dt. The predictable second moment is B_2 Z_2(t)dt, giving Var M∞=B/κ₂=B.

The jump product rule with this compensator gives, for K(t)=E[M(t)Z_2(t)],
```
K'(t)=−κ₂ K(t) + c E Z_3(t),    c=∫e(x)[x²+(1−x)²−1]ν(dx)
                                      =−∫₀¹ e(x)dx=−1/2;
(E M(t)^3)'=3B_2 K(t)+B_3 E Z_3(t).
```
For example, the product's cross jump at mass y is y³ e(x)[x²+(1−x)²−1]. The finite-interval expectations and compensator manipulations are justified by localization: entropy is increasing and its moments at time T are bounded by the moments of the tagged log mass there by Jensen; all the jump integrands above are absolutely integrable in dislocation x. In the same way
```
(E M(t)^4)' = 6 B_2 E[M(t)^2 Z_2(t)]+4 B_3 E[M(t)Z_3(t)] + B_4 E Z_4(t).
```
Since 0≤Z_r≤1, E Z_r²≤e^(−κ_rt); also sup_t E M(t)^2≤B. Cauchy–Schwarz bounds this derivative above by C(1+E M(t)^4)e^{−δt} for fixed δ>0. Grönwall then gives sup_t E M(t)^4<∞, justifying convergence of third moments at ∞. K(0)=0, and the first linear equation shows K(∞)=0 and ∫K=c/(κ₂κ₃). Consequently
```
 E M∞³ = (B_3−3B_2/2)/κ₃ < 0 ,
```
since 0≤e(x)≤log 2<3/2 and B_2>0. The centered limit −M∞/b therefore has positive third moment and cannot be normal.

The entropy-martingale identification concerns the whole tree, not the Gaussian edge-depth fluctuation of a tagged random leaf (scale (log n)^{3/2} in Aldous–Pittel). The tagged central limit theorem does not give the law of its conditional tree-average at this smaller scale.
