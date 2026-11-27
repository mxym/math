# Overlapping noisy folds: a fractional-basis bound and a sharp obstruction

The [single-fold and sparse-shell note](folded-error-information-limit.md) used disjoint supports to show that a transcript of folded errors can lose nearly all statistical information. This note handles deterministic families of folds that overlap even on every input. The relevant resource is not the length of an individual relation: it is how often the family contains independent sets of input columns. The result concerns only the joint distribution of the folds, not the original noisy samples, general distinguishing algorithms, or the complexity of Ring-LWE.

## A Fourier bound without disjoint supports

Let G be a finite abelian group. There are B independent G-valued errors with common law μ. Fix m jointly measured folds F=(F₁,…,F_m) in G^m. Each input error E_j contributes via a homomorphism C_j:G→G^m, so F=Σ_j C_j(E_j). The choices of C_j are fixed, or conditioned on side data independent of the errors. Let L_j be the induced dual map from the character group of G^m to that of G, and let ψ(u)=|μ̂(u)|² (thus 0≤ψ≤1).

Call an m-subset T of inputs a basis if the map ξ↦(L_j ξ)_{j∈T} is injective. In the finite setting this map is between groups of equal size, so this is equivalent to it being a bijection. Assign nonnegative weights b_T to bases, subject to Σ_{T:j∈T} b_T≤1 on each input j. Put κ=Σ_T b_T>0. Integral weights simply pack disjoint bases; fractional weights are allowed. Against the uniform law U on G^m,
```
1+χ²(law(F),U) ≤ (Σ_{u∈Ĝ} ψ(u)^κ)^m.                 (1)
```
Indeed Parseval gives exactly Σ_ξ ∏_j ψ(L_j ξ) on the left. The per-input capacity and ψ≤1 bound its summand by ∏_{T:b_T>0}(∏_{j∈T}ψ(L_j ξ))^{b_T}, omitting factors with zero exponent. Generalized Hölder with weights b_T/κ then bounds the sum by
```
∏_T (Σ_ξ ∏_{j∈T} ψ(L_j ξ)^κ)^(b_T/κ).
```
In each factor the basis change of variables makes the inner sum (Σ_u ψ(u)^κ)^m. This proves (1). No independence between the different output folds is asserted. This argument is an elementary basis-interpolation instance of discrete Hölder–Brascamp–Lieb, not a new general form of that inequality; see [Michael Christ, The optimal constants in Hölder–Brascamp–Lieb inequalities for discrete Abelian groups](https://arxiv.org/abs/1307.8442).

A rectangular variant handles composite moduli without a common unit minor. Allow any input set T whose columns together generate G^m, so its dual block map is injective into Ĝ^{|T|}. In the Hölder step the sum over the image is at most the sum over all of Ĝ^{|T|}. Under the same capacity constraints, the resulting bound is

    1+χ² ≤ (Σ_{u∈Ĝ} ψ(u)^κ)^b_eff,    b_eff=Σ_T b_T |T|/κ.

For example 3 and 5 together give a surjective one-output map over Z/15 although neither singleton is invertible; this example illustrates the general additive theorem, not a signed-monomial shell. Replicating this two-input block n times gives κ=n and b_eff=2.

For the negacyclic coefficient model take G to be the additive group of R=(Z/Q)[Y]/(Y^d+1), d a power of two, and let μ have iid coefficient law η. A matrix of ring coefficients defines the homomorphisms C_j. A square submatrix invertible over R qualifies as a basis; in particular its determinant must be a unit in R, not merely a nonzero ring element. No splitting assumption is made. If θ is the scalar Fourier transform of η, put S_κ=Σ_{u≠0}|θ(u)|^{2κ}. Then (1) is
```
1+χ² ≤ (1+S_κ)^{dm},    TV ≤ ½ sqrt((1+S_κ)^{dm}−1).
```
Thus dm S_κ→0 suffices for joint convergence to uniform even if *no* fold has a private input. At fixed Q and fixed aperiodic noise (the support differences span Z/Q), if ρ=max_{u≠0}|θ(u)| is strictly between 0 and 1, a sufficient condition is dm(Q−1)ρ^{2κ}→0. Uniform noise gives exactly uniform folds whenever a basis exists.

For a public-row relation list constructed without using errors, condition on the public data. Given a basis, folds of independent uniform input outputs are themselves jointly uniform by surjectivity. For random lists the conditional bound may be averaged, truncating TV at one and charging probability one on any nonempty list for which no positive packing was shown. A relation list chosen using noisy outputs is not covered. Matrix right-surjectivity, or the existence of a basis, alone does not quantify closeness to uniform.

## Sharpness, fractional gain, and failure of marginal criteria

Work over any odd Q and take m=2. Use r columns of type (1,1) and t columns of type (1,−1), r,t≥1, with elements interpreted in R. Both folds have the same support, with no private inputs. One column of each type forms an invertible pair (determinant −2), and no same-type pair does; the optimal packing value is min(r,t). Group input sums of each type into S and T. The folds have law (S+T,S−T), and the invertible transformation preserves the uniform reference and all statistical distances to it. Hence for iid coefficient errors
```
1+χ² = (1+S_r)^d (1+S_t)^d.
```
When r=t, (1) is an equality, although the folds overlap everywhere. In contrast, if t=1 and r→∞ at fixed Q,d and a fixed nonuniform aperiodic μ of the stated iid form, the r-fold sum approaches uniform, so the joint TV tends to TV(μ,uniform on R)>0. Both single folds meanwhile approach uniform. This is a full-rank obstruction to substituting row weight r+1 for κ. These examples are distributions of abstract linear images; no claim is made that a particular public input produces these relation coefficients.

Fractional packing can exceed integral packing: columns (1,0),(0,1),(1,1) support three invertible pairs. Each with weight 1/2 gives κ=3/2, as opposed to at most one disjoint pair. The total column capacity 3 proves κ cannot exceed 3/2 in this example.

More simply, if the image of (C_1,…,C_B) is a proper subgroup of index h, its output law has TV at least 1−1/h from uniform whatever the noise. This support statement is distinct from the full-rank example above; it is not a converse to (1). In general, failure to find an invertible square submatrix is not evidence that the whole map is not surjective over a finite ring.

## Continuous canonical noise is a different model

For the continuous error in [Lyubashevsky–Peikert–Regev](https://sites.cc.gatech.edu/fac/cpeikert/pubs/ideal-lwe.pdf), use the compact additive torus G=V/L, with L the canonically embedded codifferent and V its ambient real space. Fix a positive definite covariance Γ shared by independent centered Gaussian errors before reduction. The dual group is the discrete lattice L*. The same Fourier/Hölder proof works with an upper bound instead of equality in the basis change-of-variables step: an injective map of (L*)^m into itself may have proper image, but summing a nonnegative function over the image only decreases its sum. The Gaussian Fourier tail is summable; alternatively one can first truncate the nonnegative sums. If a qualifying block exists the output density is square integrable by this estimate. For a block of integral cyclotomic ring coefficients, nonzero determinant over the number field gives dual injection, since its real-linear map is nonsingular and its dual acts on the lattice. It need not have determinant a unit *modulo Q*, which was a condition in the finite model.
```
1+χ²(law(F),Haar) ≤ (Σ_{u∈L*} exp(−4π² κ ⟨u,Γu⟩))^m.
```
The estimate does not assume Γ is spherical or that its canonical coordinates are iid; indeed it was derived before invoking any coefficient factorization. For a common covariance drawn independently of the public data, average the conditional TV bounds. In the usual continuous sample model, relation cancellation also requires the appropriate dual secret and the Q⁻¹-scaled public inner product as in the preceding note. This is a sufficient mixing criterion for a restricted statistic, not a new Ring-LWE reduction.

[The toy verifier](verify-overlapping-fold-packing.js) checks 39 exact count/inequality identities on synthetic probability tables over Z/3, including full overlap with equal and unequal block sizes, the fractional packing example, and failure of uniformity for a rank-one map. No deployed scheme, ciphertext, parameters, or key are used.
