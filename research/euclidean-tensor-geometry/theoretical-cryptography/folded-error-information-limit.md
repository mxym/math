# Information loss in a transcript of sparse signed-monomial folds

This is an information-theoretic theorem about a restricted transcript, not an algorithm, a hardness reduction, or a lower bound against general Ring-LWE methods. In particular, the transcript does **not** include any of the individual noisy outputs used to form the folds. The main conclusion concerns the whole critical-window shell, not just a chosen example.

## Models and exact folding law

Write S=Z[Y]/(Y^d+1) with d a power of two, R=S/QS for Q≥2, and identify the additive group R with (Z/Q)^d by coefficients. Let E_1,…,E_B be independent, each with iid coordinates of law η on Z/Q. One may generate public uniform rows A_i in R^t independent of those errors and consider the symbolic noisy values B_i=⟨A_i,s⟩+E_i for some s∈R^t; only the folds of B_i, not B_i themselves, are observed. For a fixed relation c with Σ_i c_i A_i=0 and w nonzero coefficients c_i=±Y^j, the folded value is F_c=Σ_i c_i E_i. The same description holds after conditioning on A and any relation-list selection made independently of the errors given A.

Multiplication by a signed monomial is an exact signed permutation of the coefficient coordinates. Hence the d coordinates of F_c are independent, and each is a sum of w independent η draws with prescribed signs. Let θ(u)=E[exp(2πiuE/Q)] for a single coordinate E, and let a_j be the number of plus signs landing in output coordinate j. The exact additive Fourier transform is

    hat P_c(u_1,…,u_d) = ∏_j θ(u_j)^a_j overline{θ(u_j)}^(w−a_j),
    |hat P_c(u_1,…,u_d)| = ∏_j |θ(u_j)|^w.

There is no assumption of coefficient error symmetry, prime modulus, or complete splitting. The law itself can vary with the signs, even though its Fourier magnitudes do not. With U the uniform law on Z/Q, set

    S_w = Σ_(u≠0)|θ(u)|^(2w),   ε_w = Σ_(u≠0)|θ(u)|^w.

Each coordinate has χ² to U exactly S_w by Parseval and density f_j=dP_(c,j)/dU satisfying ||f_j−1||∞≤ε_w by Fourier inversion. Tensorization gives χ²(P_c,U^d)=(1+S_w)^d−1. Also TV(P_c,U^d)≤min(1,√(d S_w)), a convenient bound when summing many disjoint folds. For the latter, write h²(P,U)=1−∫√(dP dU). Then h²≤χ²/2, affinities multiply, and TV≤√(2h²).

## Exact transition profile

Along any parameter sequence with ε_w→0, if d S_w→τ∈[0,∞], then uniformly over the signed-monomial choices,

    TV(P_c,U^d) → 2Φ(√τ/2)−1,

where the value at τ=∞ is 1. At τ=0 the upper bound above suffices. At τ=∞, h²(P_(c,j),U)≥S_w/[2(√(1+ε_w)+1)²] follows by writing (√f_j−1)²=(f_j−1)²/(√f_j+1)², so the product affinity tends to zero and TV≥h²→1.

For 0<τ<∞, under the uniform reference let X_j=f_j(U_j)−1, with U_j iid uniform. These are independent, centered, bounded by ε_w, and each has variance S_w. The triangular Lindeberg theorem gives Σ X_j⇒N(0,τ), and Σ X_j²→τ in probability because Var(Σ X_j²)≤ε_w² d S_w. The Taylor remainder in L=Σ log(1+X_j) is bounded by a constant times ε_w Σ X_j² for large indices. Thus L⇒N(−τ/2,τ) under the uniform reference. The identity TV(P_c,U^d)=E_U[(1−e^L)_+] uses a bounded continuous function of L, so passes to the limit without an unbounded likelihood expectation. The normal integral is 2Φ(√τ/2)−1. All bounds are independent of the signs, proving uniformity.

For a fixed modulus and fixed nonuniform η with support differences generating Z/Q, 0<ρ=max_(u≠0)|θ(u)|<1, ε_w→0, and S_w∼mρ^(2w) where m counts the maximizers. Thus the threshold for one fold is exactly d m ρ^(2w) on this scale. If η is uniform, all folds are exactly uniform. If the support differences generate a proper subgroup H, each coordinate remains in a translate of H, and TV≥1−(|H|/Q)^d instead; this also explains why aperiodicity is required for the mixing conclusion. The Fourier upper bound is the standard finite-abelian walk calculation (see [Diaconis, Group Representations in Probability and Statistics](https://books.google.com/books/about/Group_Representations_in_Probability_and.html?hl=en&id=nfvuAAAAMAAJ)); the explicit Gaussian transition here is the consequence for these product marginals.

## Whole-window obstruction for the public-row relation law

Assume Q≥3 odd and use precisely the prior random finite-module shell: the A_i are iid uniform in R^t, there are N=binom(B,w)(2d)^(w−1) normalized signed-monomial candidates, and λ_w=NQ^(−dt). Let C(A) list all feasible shell relations, in any deterministic order; Z=|C(A)|. Each pair of distinct normalized candidates has a unit two-minor in every odd-prime residual component, so the two feasibility events are exactly independent (this is the previous shell result and also follows by CRT and surjectivity). Among two independently drawn shell candidates, the probability that their supports overlap is at most w²/B. Consequently

    Pr(some pair in C(A) shares a row) ≤ λ_w² w²/(2B).

This is a bound on the actual complete list of feasible shell relations, despite their possible higher-order dependence.

Compare the restricted real transcript (A,C(A),(F_c)_(c∈C(A))) to (A,C(A),(U_c)_(c∈C(A))), with all U_c independently uniform in R given A and the list. Condition on A. When all relation supports are disjoint, all dZ output coordinates are independent under the real law, and each has χ²=S_w to its uniform reference coordinate. Tensorized affinity bounds the conditional TV by √(d Z S_w); otherwise bound by 1. Jensen and E Z=λ_w imply the rigorous transcript bound

    TV(transcripts) ≤ λ_w² w²/(2B) + √(d λ_w S_w).

If one instead defines an underlying reference of independent uniform B_i∈R, its conditional folded transcript agrees with the independent-fold reference whenever all supports are disjoint, because every nonempty fold includes a unit coefficient, and different folds use disjoint B_i. This alternative comparison differs by at most another overlap probability. No individual B_i is released in either comparison.

In particular under the previously proved sparse critical assumptions B/w²→∞, B≤w^C, λ_w→λ∈(0,∞), with fixed odd Q and fixed aperiodic coefficient error, the bound tends to zero: d=O(w log w) and S_w decays exponentially in w. This means the nontrivial Poisson supply of shell relations does not automatically transfer to retained information in these noisy folds, even if the complete list is given. The bound counts neither relation-search time nor other summaries of B. It does not apply to adaptive relations selected using the errors, larger collections of overlapping relations, variable noise laws without the smallness condition, or the original full-data search or decision problems. For overlap in general, individual fold marginals can obey the exact law while their joint law fails to factor.

## Canonical Gaussian variants and comparison to LPR

In a power-of-two cyclotomic, the full canonical embedding of the power basis is orthogonal up to a common scale: summing across all embeddings shows ||σ(Σ a_jY^j)||²=dΣ a_j². Thus the centered spherical discrete Gaussian on S (and likewise on the scaled codifferent basis of S^∨=(1/d)S) is a coefficient-iid discrete Gaussian under the appropriate scale. Modulo the corresponding integer Q lattice the preceding finite result applies. A general canonical ellipse is not coefficient-iid, nor can arbitrary discretization or rounding be assumed to preserve such a factorization.

The continuous dual formulation of [Lyubashevsky–Peikert–Regev](https://sites.cc.gatech.edu/fac/cpeikert/pubs/ideal-lwe.pdf), §3 and Definitions 3.4–3.5, instead adds continuous elliptical Gaussian error modulo the codifferent lattice L=σ(S^∨). In its continuous model, condition on the Gaussian covariance Γ, common and fixed for the independent rows. For Γ scalar in each complex embedding plane (including spherical Γ), multiplication by ±Y^j rotates each plane and preserves Γ. Therefore the folded continuous Gaussian before quotient has covariance wΓ, and on the torus the exact Fourier coefficient at ξ∈L* is

    exp(−2π² w ⟨ξ,Γξ⟩).

For positive definite Γ, the χ² to Haar probability is thus the theta tail T_w(Γ)=Σ_(ξ∈L*,ξ≠0) exp(−4π²w⟨ξ,Γξ⟩), by the usual Gaussian characteristic function and Fourier Parseval. In the spherical case the lattice has an orthogonal equal-length basis, so this also gives a one-dimensional product profile after expressing the coordinates relative to S^∨ and reducing modulo 1. For general canonical ellipses use the theta expression, not the coefficient-iid finite theorem. LPR already notes the general smoothing phenomenon for error modulo the codifferent; the present observation is its exact covariance scaling for these signed-monomial folds, followed by the disjoint-shell transcript restriction. For the analogous continuous comparison, represent the signal term as Q⁻¹⟨A_i,s⟩ modulo the codifferent, with s in the codifferent modulo Q times the codifferent; any relation modulo Q cancels this term exactly. With the public rows modulo odd Q as above, the continuous transcript bound is the overlap bound plus √(λ_w T_w(Γ)) conditional on Γ; if Γ is a common random parameter independent of A, one can average the conditional bounds by convexity of TV. This does not assert that LPR's own asymptotic noise widths make T_w small in any application. In particular LPR's hardness theorem has its own completely split-prime and error hypotheses; the additive fold identities themselves do not require splitting or instantiate the hardness theorem.

The [tiny exact checks](verify-folded-error-toy.js) enumerate a non-symmetric toy η over Z/3, compare direct negacyclic counts to the independent-coordinate predictions, verify that differently signed marginals share χ² but not densities, and test both disjoint and overlapping folds. They use no public or private instances, parameters, secret values, or estimators.
