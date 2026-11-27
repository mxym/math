# Tagged torus noise priors: dense-grid simulation and joint Fourier obstructions

For a fixed public row, an abstract continuous Ring-LWE response is a torus translation of a noise law by a signal. If one insists on preserving *each* signal translation with the same one-response channel, when can the source noise law be replaced by a different law? We state the optimal simulation error on the dense torsion grid, give a finite-grid Fourier constraint that applies even to nonlinear randomized channels, and exhibit smooth Gaussian noise laws for which every separate Fourier-magnitude comparison passes but simulation still fails.

This is a defensive comparison of explicitly tagged, synthetic noise experiments. The tag names the condition under which conversion is checked; it is **not** supplied as input to the Markov channel. The result does not test a hidden secret, model a channel modifying the public rows, or optimize a many-sample computational reduction. In particular matching only the marginal averaged over an unobserved random secret is a different problem.

The independent-dither criterion in the limit is part of classical comparison of translation experiments, particularly [Torgersen (1972), Comparison of Translation Experiments](https://doi.org/10.1214/aoms/1177692372), and the group-convolution reasoning of [Le Cam, An Infinite Dimensional Convolution Theorem](https://www.stat.berkeley.edu/~rice/LeCam/papers/tech269.pdf). The finite torsion alias bound and the centered wrapped-Gaussian mixture counterexample below are the scope of this note. For the underlying response format see [Lyubashevsky–Peikert–Regev, Definition 3.1](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf), and [Peikert–Regev–Stephens-Davidowitz, Definition 2.14](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf). Standard changes to the Ring-LWE secret distribution such as the multi-sample normal-form construction in [A Toolkit for Ring-LWE Cryptography](https://sites.cc.gatech.edu/fac/cpeikert/pubs/toolkit.pdf) are not of this form.

## Experiment and limiting optimality

Let T=(ℝ/Z)^d with Haar probability U and H_q=q⁻¹Z^d/Z^d its q-torsion subgroup, for positive integer q. A fixed codifferent lattice basis gives these coordinates for the Ring-LWE error torus; a hypothetical unit public row has the entire torsion grid as its set of possible signal shifts. The full model also has nonunit and other rows; the restriction here is to a channel with this pointwise requirement for a row having all shifts.

Let P and Q be two fixed noise laws on T, with P absolutely continuous relative to U. For a shift h write P_h for the law P translated by h and similarly Q_h. Define
```
δ_q(P,Q) = inf_K (1/|H_q|) Σ_(h∈H_q) TV(P_h K,Q_h),
δ_∞(P,Q) = min_D TV(P*D,Q),
```
where K ranges over arbitrary Borel Markov channels T→T, and D over probability laws on T. One may use worst-case h in place of the average for δ_q. One may also require that K preserve Haar in both definitions and conclusions about the dense-grid limit, though the lower bounds require no such assumption. Then
```
0 ≤ δ_q ≤ δ_∞,       lim_(q→∞) δ_q = δ_∞.
```
In particular vanishing-error conversion along dense torsion grids is possible exactly when Q=P*D for an independent additive dither. This holds even if every finite-grid channel is different and all are nonlinear and unrestricted computationally.

If both P and Q have densities, there is also a simple finite-rate bound. For a probability law R let ω_R(r)=sup_(‖h‖≤r) TV(R_h,R), with distance on the flat torus. Then
```
δ_∞−δ_q ≤ ω_P(√d/(2q)) + ω_Q(√d/(2q)).
```
For densities with integrable weak gradients one gets O(q⁻¹), using the L¹ translation estimate along each segment. Fourier tests below can give much stronger finite-q obstruction for smooth noise.

## Symmetrization and finite Fourier bound

For any K, average the conjugated kernels K(x+h,B+h) over h∈H_q to obtain K̄. The channel K̄ is H_q-equivariant: shifting x by a subgroup element translates its output by that same element. Symmetrization preserves the Haar-preserving property when present. Moreover TV(P K̄,Q) is at most the original average error by convexity, and all shifted errors of K̄ are equal to this zero-shift error. This proves the interchangeability of average and worst case.

For s∈Z^d write χ_s(x)=exp(−2πi⟨s,x⟩), and let p̂_s=E_P χ_s. If X is Haar-uniform and Y conditional on X is drawn from K̄, let D_q be the law of Y−X, and d̂_s its Fourier coefficient. Suppose P has square-integrable density p. For any s,
```
| E_(P K̄)χ_s − p̂_s d̂_s | ≤ A_q(s),
A_q(s) = [Σ_(z∈Z^d\{0}) |p̂_(s+qz)|²]^(1/2).
```
Indeed g_s(x)=E[χ_s(Y)|X=x] is bounded by one and satisfies g_s(x+h)=χ_s(h)g_s(x) for h∈H_q. Thus in the negative-character Fourier basis its expansion is supported on ℓ≡s mod q. Its coefficient at s is precisely E[χ_s(Y−X)]=d̂_s. Integrate g_s against p and use Parseval/Cauchy–Schwarz on the other aliases, noting that the squared norm of g_s is at most one. Passing from P K̄ to Q costs at most twice their TV distance on any bounded character. Consequently an error bound ε entails the simultaneous inequalities
```
| q̂_s − p̂_s d̂_s | ≤ 2ε + A_q(s)   for every s,
```
where the *same sequence* (d̂_s)_s must be the transforms of a probability law. Applying Cauchy–Schwarz including the main coefficient also gives the individual test
```
ε ≥ (|q̂_s| − [Σ_z |p̂_(s+qz)|²]^(1/2))_+ /2 .
```
The joint constraint is stronger, as the example below shows.

For each fixed s, A_q(s)→0 when p∈L². The same vanishing discrepancy between E_(P K̄)χ_s and p̂_s d̂_s holds uniformly in the channel when p∈L¹: approximate p in L¹ by a finite trigonometric polynomial and integrate against the bounded function g_s. For sufficiently large q that polynomial has no nonmain alias in the class of s, and the error from the approximation is at most twice its L¹ error. This argument does not require that the approximating polynomial itself be a density.

## Proof of the dense-grid limit

Any independent dither is a channel exact in its response to shifts, giving δ_q≤δ_∞ also for Haar-preserving channels. The minimizer over D exists by compactness of probability laws on T in the weak topology and lower semicontinuity of TV under weak convergence of the first law (use bounded continuous tests and regularity of finite measures on T).

Along a subsequence approaching liminf δ_q choose nearly optimal K_q and symmetrize. The increment laws D_q have a weakly convergent subsequence with limit D. The preceding fixed-frequency alias argument shows that P K̄_q converges weakly to P*D, since the Fourier coefficients converge and trigonometric polynomials approximate every continuous function uniformly. Thus δ_∞≤TV(P*D,Q)≤liminf δ_q by lower semicontinuity and the symmetrized error bound. This proves the claimed limit even if Q is singular.

For the translation-modulus inequality, the zero-shift error of the symmetrized channel bounds its error on H_q; every t∈T lies within √d/(2q) of some h∈H_q. TV contraction by a channel and the triangle inequality bound the error at t by the subgroup error plus ω_P+ω_Q at that radius. Now average conjugates over *all* translations of T. The resulting channel is fully equivariant and therefore has the form of adding an independent increment D, so its zero-shift error is at most the bound. To check this last fact for a Borel channel, define its averaged law at each x by the integral over all translates; translating both the input and output by a fixed t leaves that integral unchanged by Haar invariance. Equivariance therefore prescribes the law at x as the translate of its law at zero.

## Smooth Gaussian example: separate Fourier attenuation is insufficient

Take d=1. For 0<a<1 let G_a be a centered real Gaussian, wrapped on the circle, with variance −log(a)/(2π²). Its Fourier coefficient at k is a^(k²). Consider
```
P=(G_(1/2)+G_(1/32))/2,     Q=G_(51/256).
```
For every nonzero integer k one has 0<q̂_k<p̂_k: since (51/256)/(1/2)=51/128<1/2, its k²-th power is below 1/2, while P has the half-weight component G_(1/2). Nevertheless no independent dither exists. It would require d̂_1=3/4 since p̂_1=17/64 and q̂_1=51/256. Also d̂_2=q̂_2/p̂_2<1/16: q̂_2<(1/5)^4 and p̂_2>1/32, so the ratio is below 32/625<1/16. For any probability D on the circle, the identity cos(2x)=2cos²x−1 gives
```
Re d̂_2 ≥ 2 (Re d̂_1)^2 − 1 .
```
The required value of d̂_1 forces the right hand side to be 1/8, contradicting the required d̂_2. Separate Fourier tests omit this cross-frequency positivity requirement.

There is a uniform finite-grid discrepancy for this example. For q≥6 and s=1,2 all nonmain aliases have |ℓ|≥4, and p̂_ℓ≤2^(−ℓ²). Thus A_q(s)≤[2 Σ_(j≥4)2^(−2j²)]^(1/2)<2⁻¹⁵, by comparison with the geometric series of common ratio 2⁻¹⁸. If a conversion achieved ε≤1/2048, the joint bounds would give
```
Re d̂_1 ≥ 3/4 − 4·(33/32768) > 37/50,
Re d̂_2 < 1/16 + 32·(33/32768) = 97/1024.
```
But 2(37/50)²−1=119/1250>97/1024. So the infimum simulation error for every such finite grid is at least 1/2048, even though the separate (all-frequency) attenuation inequalities hold.

As a special case, for two *nonmixed* centered wrapped Gaussians with covariance A and B, the dense-grid limit permits vanishing error exactly when B−A is positive semidefinite. Sufficiency follows from Gaussian dither. If it fails, some integer character has a negative quadratic difference (use density of rational directions), so its required dither coefficient would have magnitude greater than one. The mixture example explains why a pointwise magnitude argument is generally not sufficient, even for smooth centered Gaussian mixtures.

[The toy checker](verify-torsion-noise-prior-coupling.js) verifies the rational counterexample constants and the exact finite-grid symmetrization identities on small synthetic probability tables. No data from a cryptosystem or secret-recovery code are used.
