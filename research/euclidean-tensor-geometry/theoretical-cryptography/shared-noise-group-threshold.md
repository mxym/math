# Shared versus refreshed noise parameters: exact grouping thresholds

A mixture of independent batches is not the product of its one-sample mixture. We give a sharp statistical transition for weak, bounded changes of the conditional noise law, valid for arbitrary varying group sizes. The scale counts **pairs of samples sharing the latent parameter**, not just the total number of samples. A wrapped canonical Gaussian example also gives the exact profile for one large shared batch.

This compares standalone synthetic noise distributions. It is not a distinction or an algorithm on full Ring-LWE observations or a claim about parameters of any scheme. In [Lyubashevsky–Peikert–Regev, definitions 3.3, 3.5 and 5.10](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf), the error distribution itself is selected once per decision instance, and successive errors are conditionally drawn from that distribution. The separate per-sample-parameter experiment below is not that definition. In particular our bounded local theorem does not analyze LPR's full prior over Gaussian widths or their reductions. For the general shared-component sampling concept see [Vandermeulen and Scott, On the Identifiability of Mixture Models from Grouped Samples](https://arxiv.org/abs/1502.06644); their question is recovering an unknown mixture from grouped data, rather than the weak-perturbation TV comparison below. Classical local tests for variance components are also related, e.g. [The Use of Score Tests for Inference on Variance Components](https://doi.org/10.1111/1541-0420.00032); we do not assert priority for the underlying second-order score.

## Model and exact finite bound

Let Q be a one-sample law, π a latent parameter law, and write the conditional one-sample laws as
```
dP_θ/dQ = 1 + ε f_θ,           |f_θ|≤C,
E_Q f_θ=0 for π-almost every θ,  E_π f_θ(x)=0 for Q-almost every x.
```
The second centering means Q is exactly the one-sample mixture. Take 0<ε→0 if considering limits, and εC≤1/2 for the local calculations. Q, π and the scores may depend on ε; assume joint measurability. Compare:
- **Shared within groups:** draw one θ for each group of size m, then draw m conditionally IID samples from P_θ. Draw the latent parameters independently across groups.
- **Refreshed for every sample:** draw a fresh θ independently every time. Its joint law is the product reference Q.

For independent θ,θ' from π, put K(θ,θ')=⟨f_θ,f_θ'⟩ under Q and κ=E K². If P_[m] denotes the law of one shared group, its likelihood ratio is L_m=E_θ∏_(j=1)^m(1+ε f_θ(X_j)), and exactly
```
χ²(P_[m],Q^m) = E_(θ,θ') (1+ε²K(θ,θ'))^m − 1
              = Σ_(r=2)^m binom(m,r) ε^(2r) E K^r.
```
For the first equality expand the square of L_m and use independence under Q^m. The linear term vanishes because E_π f_θ(x)=0. No assumption K≥0 is needed: each moment E K^r is nonnegative, since by Fubini it equals
```
∫ [E_θ ∏_(j=1)^r f_θ(x_j)]² dQ^r(x).
```
Therefore for m≥2
```
binom(m,2) ε⁴ κ ≤ χ²(P_[m],Q^m)
                ≤ binom(m,2) ε⁴ κ (1+C²ε²)^(m−2).
```
For the upper bound use |K|≤C², E K^r≤(C²)^(r−2)κ, and binom(m,r)≤binom(m,2)binom(m−2,r−2). Singletons have zero distance exactly, as they must. Since one plus χ² multiplies across independent groups, these estimates immediately give a finite TV upper bound via TV≤sqrt(χ²)/2. This upper bound is valid also for very small κ and does not require the critical assumptions below.

## Sharp many-small-groups transition

Assume κ is bounded below by a fixed positive constant. Ignore singleton groups and allow the number of nontrivial groups and their sizes m_i to vary with ε. Suppose max_i m_i ε²→0. Define
```
J = κ ε⁴ Σ_i binom(m_i,2).
```
If J→v∈[0,∞], the TV distance between the two joint laws tends to
```
2 Φ(√v/2) − 1 ,
```
with value one at v=∞. In particular the fourth power of the small latent perturbation is multiplied by the number of pairs sharing a parameter.

We give a moment bound to justify a log-likelihood limit, not just the leading χ². Under Q^m write for fixed θ
```
S=ε Σ_j f_θ(X_j),       W=Σ_j log(1+ε f_θ(X_j)) − S.
```
Then |W|≤C' m ε² deterministically. The centered sum S is sub-Gaussian with variance proxy O(mε²) by the bounded-variable exponential moment inequality (Hoeffding); in particular E|S|^16=O((mε²)^8) and E exp(8|S|)=O(1) whenever mε²≤1, uniformly in θ. For Δ=mε², the error e^(S+W)−1−S is bounded in absolute value by a constant times (Δ+S²)e^(|S|+C'Δ). Cauchy–Schwarz on its fourth moment gives L⁴ norm O(Δ). Since the average over θ of S vanishes pointwise, averaging over θ via Jensen gives
```
‖L_m−1‖_4 = O(m ε²).
```
The exact χ² estimate shows that its variance is uniformly (1+o(1)) κ ε⁴ binom(m,2) along the prescribed regime, and is comparable to (m ε²)² for m≥2. Thus a finite total J implies that the variance sum tends to v, while the sums of third and fourth moments tend to zero via the maximum m_i ε². Under the reference the group likelihood differences are independent and centered. For 0<v<∞ Lyapunov gives a centered normal limit for their sum, and the sum of their squares tends in probability to v. Their maximum magnitude tends to zero by the third moments, so the log of the full likelihood converges in law under the reference to N(−v/2,v). TV is the expectation of the bounded continuous function (1−exp(x))_+ of that log-likelihood. Evaluating against the limiting normal gives the displayed expression.

At v=0 use the exact product χ² bound. For v=∞ use squared Hellinger distance per group h²=1−E_Q sqrt(L_m). The identity 2h²=E[(L_m−1)²/(sqrt(L_m)+1)²] and the third moment estimate give h²=(1/8+o(1)) Var(L_m), uniformly over m≥2 (split at |L_m−1|=1/2). Hence product affinity is exponentially small in J, and TV≥h² tends to one.

## One fully shared Gaussian covariance choice

Use the compact torus V/L of a canonically embedded cyclotomic lattice (for example, take L to be the codifferent), with fixed dimension. Choose a positive definite canonical covariance A, and a nonzero symmetric matrix S that is scalar in each conjugate complex embedding plane. Let p_+, p_- denote the Gaussian laws with covariances A±εS, wrapped on that torus. These are positive definite for ε small. Put q_ε=(p_++p_-)/2 and f_ε=(p_+−p_-)/(2ε q_ε), using Haar densities. The scores in the above general theorem are +f_ε and −f_ε with equal weights. The densities and derivatives in that fixed neighborhood are smooth and uniformly bounded, by summing their Gaussian derivatives over lattice translates; the wrapped density is also bounded below by a positive constant on the compact torus. Thus f_ε are uniformly bounded and converge uniformly to the wrapped covariance score f=(∂_t p_(A+tS)|_(t=0))/p_A, with centered second moment v_ε=E_(q_ε) f_ε² → v_0=E_(p_A) f²>0. Positivity follows by Fourier transform: at a dual lattice frequency ξ, the covariance derivative multiplies the positive Gaussian coefficient by −2π² ξᵀSξ. A nonzero quadratic form cannot vanish on a full-rank lattice, as seen on a lattice basis and on pair sums.

The many-groups theorem above therefore applies with κ=v_ε². For a **single** fully shared group of size m and m ε²→λ∈[0,∞), the exact TV limit is
```
E [(1 − exp(−λ v_0/2) cosh(√(λ v_0) Z))_+],   Z∼N(0,1).
```
Indeed under q_ε^m the two conditional log-likelihoods are the opposite linear sums ±ε Σ f_ε, with a common quadratic term −ε² Σ f_ε²/2 and uniform remainder O(m ε³). Boundedness gives the usual triangular-array central limit and concentration of the quadratic sum. The shared likelihood is their arithmetic average after exponentiation, so its limiting likelihood is exp(−λv_0/2)cosh(√(λv_0)Z). Using the bounded positive-part formula for TV avoids any unbounded likelihood convergence assumption. The analogous refreshed group instead has likelihood exactly 1. For λ>0 this profile is strictly positive, since the nonconstant limiting likelihood has mean 1.

When m ε²→∞, the raw-noise TV tends to one. Under the refreshed law the average of f_ε has mean zero and variance O(1/m); under the two shared components its mean is ±ε v_ε with variance O(1/m). By Chebyshev, the event that its absolute value exceeds ε v_ε/2 has probability tending to zero under refresh and to one under shared. All one-sample marginals, however, agree exactly for every ε. This example takes place entirely on a wrapped error torus, without any public rows or secret signal.

For transferring an already-proved conditional comparison, there is a simpler bound: if both models draw the same single latent parameter with prior π and have conditional batch laws P_θ and R_θ, then TV(∫P_θ dπ, ∫R_θ dπ) ≤ ∫TV(P_θ,R_θ)dπ by convexity. No independence after averaging is required. This is not a license to replace a shared prior on the group by independent per-sample latent draws: that changes the conditional construction on the other side of the comparison.

Finally, if raw errors in two models are passed through the same randomized channel with independent auxiliary variables, the TV distance of the resulting distributions cannot exceed their raw TV distance. Thus small-distances above transfer to any such output comparison, even with common side information generated independently and identically in both experiments. Large raw distance does not imply that the same information remains after a hidden signal is added and the errors are removed from observation. In particular the large-distance results are not ways to distinguish actual Ring-LWE data.

[The exact toy verifier](verify-shared-noise-groups.js) checks direct finite event enumeration against the moment formula for two synthetic binary mixtures (one symmetric and one asymmetric), including equality at the two-sample boundary. No real samples, schemes, or attack routines are involved.
