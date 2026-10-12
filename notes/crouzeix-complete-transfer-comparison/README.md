# Complete similarity transfer and the scope of the strict bound

7 October 2026. Addendum to [Quantitative strict bounds in complete numerical range calculus](https://github.com/mxym/math/blob/3a1dbb9bab7ef72db726e8221deec925e0938c8d/notes/complete-crouzeix-deficit/README.md).

The general existence of a coefficient-independent bound strictly below two on a larger enclosing convex domain follows by combining an existing complete similarity-transfer theorem with the attributed complete constant-two theorem. Norm-perturbation robustness follows as well. These broad conclusions should therefore not be presented as new results of this note. The precise retained-deficit formula, reduced-density estimate and intrinsic μ/M certificate remain its specific candidate refinements; their novelty and priority are unestablished.

The norm-margin formula below is a documented deduction from those ingredients. It is not a formula located verbatim in the cited papers, and no first-result claim is made. This addendum supplements the literature discussion; the published proof, PDF and source archive remain unchanged.

## The complete inputs

1. OpenAI, [A direct proof of the complete Crouzeix inequality](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/main.tex), 26 September 2026, Theorem 1.1, supplies complete constant two for every finite base dimension, coefficient size and polynomial degree. Its [structural companion](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/build/main.tex), Section 6, also states the rational and holomorphic complete spectral-set formulation and the Hilbert-space extension. Both sources are pinned at adc7f1241b42e322a6451854ab7e4b4c146bf78a.

2. Åhag–Czyż–Virtanen, [arXiv:2608.27346v3](https://arxiv.org/html/2608.27346v3), 9 September 2026, Theorem 8.2, fixes a base dimension n. For every B∈M_n(ℂ), suppose K(B) is a compact complete C-spectral set, with C independent of B. If K(S⁻¹AS) lies compactly inside a bounded convex domain Ω containing σ(A) for every invertible base matrix S with cond(S)<γ, where γ>1, then the optimal complete Ω constant is at most max{1,C/γ}. Corollary 8.1 and Theorem 5.5 supply exact inflation of the complete norm, when it exceeds one, by similarities on the base space. These results have no restriction n≤3. Their construction uses orthogonal base Schmidt supports; matrix coefficients remain unchanged.

The universal complete-two premise here is specifically the OpenAI result; the arXiv paper's own complete-two theorem covers base dimensions at most three.

Here cond(S)=||S||·||S⁻¹||. In the base-first tensor convention, the corresponding identity is

    F[S⁻¹AS] = (S⁻¹⊗I_m) F[A] (S⊗I_m).

Thus this comparison uses a complete theorem with the needed base-similarity quantifiers. It does not obtain completeness by amplifying a scalar commutation argument.

## A norm-margin deduction

Let A be a bounded operator on a nonzero complex Hilbert space H. Let Ω⊂ℂ be bounded, open and convex, and assume

    K = closure W(A) ⊂ Ω,
    d = dist(K,∂Ω) > 0.

Choose any c∈ℂ and put N=||A−cI||. For N>0 define

    C_margin = max{1, 2/(1+d/N)} < 2.

Then, using the complete inputs above, for every positive integer m, every nonnegative integer L and every polynomial F(z)=Σ_{j=0}^L z^j C_j with C_j∈M_m(ℂ),

    ||F[A]|| ≤ C_margin · max_{z∈closure Ω} ||F(z)||,
    F[A] = Σ_{j=0}^L A^j⊗C_j.

The factor is independent of coefficient size, degree and base dimension. No boundary smoothness or exterior conformal collar is needed for this deduction. If A=aI is scalar, F[A]=I⊗F(a), so factor one holds for every c. In particular, N=0 is handled this way, without division by N. Constant polynomials explain the lower floor one.

### Finite base spaces

First take H=ℂ^n. The complete-two input makes W(B) a compact complete 2-spectral set for every B∈M_n(ℂ). Equivalently, its polynomial estimate extends to rational functions with poles outside W(B). One may approximate each entry uniformly on a slightly enlarged compact convex neighborhood of W(B), so polynomial evaluations converge by the holomorphic functional calculus. This includes point and segment numerical ranges.

Let S be any invertible base matrix and κ=cond(S). Write S=UP with U unitary and P positive. Rescale P, which leaves conjugation unchanged, so its extreme eigenvalues are κ⁻¹/² and κ¹/². Set G=U*(A−cI)U. Then ||G||=N and

    ||P⁻¹GP−G||
    ≤ ||P⁻¹||·N·||P−I|| + ||P⁻¹−I||·N
    ≤ [√κ(√κ−1)+(√κ−1)]N
    = (κ−1)N.

Unitary conjugation preserves the numerical range. For any two matrices T,V, each unit-vector numerical value of T differs from the corresponding value of V by at most ||T−V||. Writing D̄ for the closed unit disk therefore gives

    W(S⁻¹AS) ⊂ K+(κ−1)N D̄.

For κ<γ:=1+d/N, the right-hand side is a compact subset of Ω: every point within a distance strictly less than d of K stays inside Ω. The transfer theorem applies with K(B)=W(B), C=2 and this γ, giving C_margin. Its condition is strictly κ<γ; containment at κ=γ is unnecessary. When γ≥2, the maximum in its conclusion gives factor one. There is no inference of a factor below one.

### Arbitrary Hilbert spaces

Fix F and a unit vector x=Σ_{i=1}^m x_i⊗e_i. Let

    E = span{A^j x_i : 1≤i≤m, 0≤j≤L},
    B = P_E A|_E.

This is a nonzero finite-dimensional compression. For j≤L, induction gives B^j x_i=A^j x_i, so F[B]x=F[A]x. Also W(B)⊂K and ||B−cI_E||≤N. The preceding containment argument consequently works for B with the same conservative d,N and γ, even if B is scalar. Apply the finite bound to x and take the supremum over unit x. This proves the stated polynomial inequality without separability or norm attainment. The space E depends on F and x; no single finite compression is asserted to preserve the entire calculus.

## Perturbations on the same domain

If ||R||≤e<d, then

    closure W(A+R) ⊂ K+e D̄ ⊂ Ω,
    dist(closure W(A+R),∂Ω) ≥ d−e,
    ||A+R−cI|| ≤ N+e.

The same deduction therefore gives the uniform certificate

    ||F[A+R]|| ≤ max{1, 2/[1+(d−e)/(N+e)]}
                 · max_{z∈closure Ω} ||F(z)||.

The displayed factor is strictly below two whenever N+e>0. If N+e=0, then e=0 and A=cI, so factor one applies directly. Any other scalar perturbed operator also has factor one. These are conservative estimates, with no optimality claim.

## What remains specific to the note

Under the analytic convex collar hypotheses of [Section 2 of the published source](https://github.com/mxym/math/blob/3a1dbb9bab7ef72db726e8221deec925e0938c8d/notes/complete-crouzeix-deficit/research.tex), the note defines

    R_A(λ) = λh′(λ)(h(λ)I−A)⁻¹,
    M = max_{|λ|=1} ||R_A(λ)||,
    μ = min_{|λ|=1} λ_min(R_A(λ)+R_A(λ)*) > 0,

and proves the intrinsic factor

    C_intrinsic = 2/√(1+min{μ²,3}/M²).

Its quantitative step retains the nonnegative deficit and cancels the product of the purities of the reduced singular-vector densities. The four resolvent block fields, separate ordered FG/GF tests, weighted coefficient-dual estimates and positive-block comparison already occur in Section 3 of the attributed OpenAI direct proof. The precise density estimate and resulting μ/M certificate are the narrower subjects for further comparison and verification.

This bounded comparison found no exact earlier μ/M formula or identical retained-deficit identity in the sources checked. That is not evidence sufficient to establish priority, optimality or superiority of either certificate. No general ordering between C_margin and C_intrinsic is proved here. The note's necessary near-equality inequalities do not classify extremizers or establish stability to a prescribed model.

All strict estimates concern a larger enclosing domain. They do not give a universal constant below two on K itself. As d decreases to zero with N fixed, C_margin tends to two. The matrix A=[[0,2],[0,0]] with F(z)=z has ratio two on its numerical range, the closed unit disk. Finally, the deduction depends on the cited complete inputs; this addendum is neither an independent proof of all their premises nor a proof-assistant verification.
