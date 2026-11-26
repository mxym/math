# Signed Fourier-Laplacian duals for Paley two-localization

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review or priority claim. The notation and baseline dual follow [the projective reduction](PaleyLocalizationProjectiveSymmetry.md).


Let p ≡ 1 mod 4 be prime, B the squares in F_p^* of order m=(p−1)/2, f(u)=χ(1−u), and S={x:χ(x)=χ(x−1)=1}, of order n=(p−5)/4. Write q(z)=(z+2+z⁻¹)/4; B\{1,−1} modulo inversion is S. For z,w put u=w/z, v=wz; χ(q(z)−q(w))=f(u)f(v). All the functions below live on B; both f and our chosen real g are inversion-even.

Define E_g(z,w)=(f(u)−f(v))(g(u)−g(v)) on all of B. This is symmetric and unchanged under inversion of either variable: z→z⁻¹ exchanges u,v; w→w⁻¹ exchanges their inverses. Its rows and columns at ±1 vanish since u=v. It vanishes on the distinct Paley edges, where f(u)=f(v)∈{−1,1}. On S define Δ_g by any lift for distinct vertices and make its diagonal zero. On the diagonal before repair e_g(q(z))=f(z²)(g(z²)−g(1)), hence |e_g|≤osc(g). Consequently I+C_S+Δ_g is a Lovász-theta dual witness for the complement, where C_S is the zero-diagonal Seidel matrix. Every scalar dual is included because Δ_f=4 A_complement. One can additionally average over the projective S₃ action without increasing λ_max (this may reduce the parameter span).

Use normalized Fourier coefficients β_a=f̂(a), γ_a=ĝ(a) for cyclic characters ψ_a indexed by Z/m, with basis ψ_a/√m in ℓ²(B). f,g real even imply β,γ real even. Let T_h(z,w)=h(w/z), H_h(z,w)=h(wz), and R be inversion, so H_h=T_h R. On the inversion-even subspace T_h and H_h coincide; the two mixed terms g(u) f(v) and f(u) g(v) also coincide there, by substituting w→w⁻¹. Hence E_g/2 on that subspace equals T_fg−F where F(z,w)=g(w/z)f(wz). Put D_a=diag(ψ_a). F R=Σ_a γ_a D_−a T_f D_−a, since F=Σ_a γ_a D_−a H_f D_a and R D_a R=D_−a. Thus E_g/2 restricted to inversion-even vectors is the following signed weighted Laplacian in frequency:
\[
(L_g\xi)_\ell=m\sum_{a\bmod m}\gamma_a\beta_{\ell-a}(\xi_\ell-\xi_{\ell-2a}).
\]
Indeed the convolution term has diagonal m(fg)^∧(ℓ), and F R couples modes ℓ−2a and ℓ with midpoint ℓ−a and weight m γ_a β_{ℓ−a}. The restriction further deletes physical ±1, equivalently requiring zero sums of Fourier coordinates in each parity. L_g preserves index parity, annihilates each parity-constant vector, preserves frequency inversion symmetry, and leaves this quotient subspace invariant. Under the isometric lift (assign each point's coordinate divided by √2 to each of its two inverse representatives), E_g/2 is exactly Δ_g+diag(e_g), as its two identical entries add and the factor 2 cancels. Thus the norm bound below includes precisely one diagonal repair, not two.

Extend characters on B to F_p^*, insert the indicator (1+χ)/2 to express m β_b as half the sum of two Jacobi sums with second character χ. The standard Jacobi bound is |m β_b|≤√p for all b, including the trivial or inverse special cases (absolute value ≤1); m β_0=−1. A row sum of absolute entries of L_g is at most 2√p Σ_{a≠0}|γ_a|, so by symmetry its operator norm has this bound. Thus
\[
 \|\Delta_g\|\le 2\sqrt p\sum_{a\ne0}|\gamma_a|+\operatorname{osc}(g).
\]
In particular any trigonometric polynomial (in multiplicative Fourier coordinates) of bounded ℓ¹ mass gives an unconditional O(√p) perturbation, with no O(p) constant-vector spike; for fixed Fourier support the correction is exactly a short collection of midpoint-weighted shifts, not a dense two-dimensional kernel. In contrast no claim is made that the original Seidel matrix itself becomes sparse.

The map g↦Δ_g has rank exactly n−1 for p≥17. Label parity by the two cosets of B² in B. Both signs of f occur in each coset: their imbalance is the absolute value of half the sum or difference of m β_0 and m β_{m/2}, at most (1+√p)/2, whereas the count of nonzero f values is at least (p−5)/4, strictly larger for p≥17. Every mixed-sign pair u,v of the same parity can be realised as w/z=u,wz=v with z,w∈B: solve z²=v/u (possible by same parity), w=uz. Neither z nor w is ±1 since that would imply v=u or v=u⁻¹, inconsistent with signs, and their quotient points are distinct because f(u),f(v) are both nonzero (so u≠1 and v≠1). Accordingly Δ_g=0 equates g on all bipartite cross-sign edges in each parity coset, making it constant there except for free g(1); the converse is immediate. The inversion-even g-space has dimension (m+2)/2 (fixed points ±1); the nullspace has dimension 3, so the rank is (m−4)/2=n−1. No θ upper bound with a new leading constant follows from these exact identities alone. Prior art checked: Kunisky arXiv:2303.16475 App. A; Randomstrasse101 arXiv:2603.29571 Conj. 27; Magsino–Mixon–Parshall arXiv:1907.05971 is a one-localization Schrijver LP and does not give this two-localization family.


## A uniform character-shift dictionary

For t in B let g_t(u)=(f(tu)+f(t⁻¹u))/2. When t≠1 these inversion-even functions supply a second unconditional norm bound, independent of their Fourier ℓ¹ norms:
\[
\|\Delta_{g_t}\|\le4\sqrt p+2.
\]
For the mixed part first take the unsymmetrized single translate f(tu). Choose a∈F_p^* with a²=t⁻¹. Replacing the row representative z by z'=az and column representative w by w'=a⁻¹w sends w/z to t w/z and preserves zw. Both relabeled representatives run through the same coset aB, since a⁻¹B=aB. For z',w' in this coset,
\[
 f(w'/z')f(z'w')=\chi(a)\chi(q(z')-q(w')).
\]
Indeed the two factors of the difference (z'-w')(1-(z'w')⁻¹)/4 have characters χ(a)f(w'/z') and f(z'w'), because z'w' is a square. The formula also covers duplicate images. The incidence lift of the Paley Seidel compression to q(aB) has norm multiplication at most 2 because each fiber of q has at most two points. Row and column relabelings do not affect the singular norm. Thus the mixed matrix for each translate, and their symmetrized average F for g_t, have norm at most 2√p.

Likewise the convolution T_fg_t has norm at most 2√p: its eigenvalues are averages of sums over B of ψ(u)χ((1-u)(1-tu)), or the same with t⁻¹. Extend ψ to F_p^*, insert the square indicator (1+χ(u))/2, then apply the ordinary multiplicative Weil bound to a primitive-character product with distinct roots 0, 1, 1/t (and analogously 1/t⁻¹). If the character multiplying the quadratic factors is nontrivial, the root at 1 has exponent exactly (p−1)/2, so the polynomial is not a (p−1)-st power. The bound is 2√p for at most three distinct roots. If that multiplying character is trivial, the full-field quadratic sum has absolute value 1 and excluding u=0 changes it by at most 1. Combining these two norm bounds on T_fg_t−F, then adding the oscillation repair ≤2, proves the displayed claim.

The dictionary spans the entire dual subspace, even after removing t=1. To see it, every Fourier coefficient β_a of f is nonzero. The constant coefficient is −1/m. For a nontrivial character on B take an extension A to F_p^*; neither A nor Aχ is trivial. The two Jacobi sums in m β_a satisfy J(A,χ)J(Aχ,χ)=p, by the Gauss-sum quotient formula and g(χ)²=p. If their sum vanished, then J(A,χ)²=−p in Q(ζ_(p−1)), which is impossible: p is unramified in that field, so the valuation of −p at every prime above p is 1, while a square has even valuation. Nonzero Fourier coefficients imply the translates f(tu) span all functions on B, and their inversion-even averages g_t span the even functions. Finally Σ_{t∈B}g_t=−1 is constant, hence Σ_{t∈B}Δ_{g_t}=0 and the scalar direction Δ_f can be discarded from the generating list. This enables uniform bounds on arbitrary finite combinations by the ℓ¹ norm of their dictionary coefficients. It does not assert that some fixed combination improves the asymptotic constant.

## An exact finite separation from every scalar dual

At \(p=601\), \(|S|=149\), the signed Fourier-Laplacian family achieves an upper bound strictly below \(73/4\), and every scalar dual has largest eigenvalue strictly above \(73/4\). The [standalone exact checker](verify-paley-fourier-laplacian-601.js) supplies the rational even function \(g\) with denominator 16 and checks the whole witness, including the Paley sign formula and edge constraints. It tests that the integer matrix \(16(73I-4(I+C_S+\Delta_g))\) is positive definite by verifying all 149 positive leading pivots and all divisions in fraction-free symmetric elimination.

Write a scalar dual as \(I+C_S+4tA_{\overline{G_{p,2}}}\). At the all-ones vector and a second fixed integer vector orthogonal to it, respectively, the Rayleigh quotients are
\[
\frac{-143+44688t}{149},\qquad
\frac{21264216-42528432t}{1002892}.
\]
The maximum of these affine functions is minimized at their intersection, where its exact value is \(944173718832/51153974064>73/4\). This certificate separates the finite feasible families without relying on a solver's floating-point optimum. It does not assert a new asymptotic leading constant, and \(73/4\) is still above the \(p=601\) target of Conjecture 27.


A compact second witness uses only one character shift beyond the scalar term. Take \(t=245=10^{36}\bmod601\) and \(g=(19/400)f+(3/40)g_t\). The [second exact checker](verify-paley-single-character-shift-601.js) verifies \(\lambda_{\max}<96/5=19.2\) by 149 positive fraction-free pivots, and certifies the stronger lower bound \(1355868942120581952/69368131028563872>39/2=19.5\) for all scalar duals using two new integer Rayleigh vectors. Thus one explicit nonscalar generator suffices for a strict finite separation of at least \(0.3\). The denser certificate above still gives the smaller upper bound.
