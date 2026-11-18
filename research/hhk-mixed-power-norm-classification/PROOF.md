# The Hilbert–Schmidt norm is the unique interior monotone mixed-power norm

Research draft. The argument was independently checked in an internal AI review, not externally peer reviewed. See [the review](REVIEW.md) and [prior work](SOURCES.md).

Put Mᵤ(A,B)=AᵘB+BA¹⁻ᵘ, where A is positive semidefinite, B is Hermitian, and both are complex square matrices of the same size. Positive real matrix powers are defined by spectral calculus. All norms below are matrix norms; “unitarily invariant” means invariance under independent left and right unitaries.

**Theorem.** Fix d≥2 and any one pair 1/2≤s<t<1. Among unitarily invariant norms on M_d, N(Mₛ)≤N(Mₜ) for every A≥0 and Hermitian B if and only if N is a positive scalar multiple of the Hilbert–Schmidt norm. For each non-Hilbert–Schmidt Schatten norm (1≤p≤∞, p≠2) there are already strict failures with A real positive definite diagonal and B real symmetric of order two, for **every** such interior pair. The sufficiency (even through t=1) is due to Hayajneh–Hayajneh–Kittaneh. The original all-norm conjecture had already been refuted by a trace-norm example, so its bare refutation is not the claim here. Corner erasure and entrywise norm monotonicity also have classical predecessors; see [SOURCES.md](SOURCES.md).

## 1. The known positive side

In the eigenbasis of A with eigenvalues aᵢ>0 set wᵢⱼ=|Bᵢⱼ|²=wⱼᵢ. Expanding and interchanging i,j shows

  ‖Mᵤ‖²_HS=∑ᵢⱼwᵢⱼ(aᵢ²ᵘ+aᵢ²⁻²ᵘ+aᵢᵘaⱼ¹⁻ᵘ+aᵢ¹⁻ᵘaⱼᵘ).

The two pairs are respectively 2aᵢ cosh((2u−1)log aᵢ) and 2√(aᵢaⱼ)cosh((u−1/2)log(aᵢ/aⱼ)); each is nondecreasing for u≥1/2. For the stated range s<t<1, singular A follows by continuity from A+εI. This is a reproof of the 2018 result.

## 2. Necessity for every unitarily invariant norm in fixed dimension

Write N(X)=g(σ(X)), where g(u)=N(diag u) is a symmetric gauge. This identity follows directly from the SVD; g is a finite-dimensional norm, hence Lipschitz in Euclidean distance. Singular values may be fed to g in any order.

Assume the universal inequality at the fixed s,t. For any x,y>0, h real and spectator coordinates z₁,…,z_{d−2}≥0, put a=x−y, b=√(xy), D=diag(z₁,…,z_{d−2}). For 0<δ<1 choose the real matrices

  Aδ=diag(1,δ) ⊕ I,     Bδ=[[a/2,b],[b,h/δ¹⁻ᵗ]] ⊕ D/2.

Although a diagonal entry of Bδ may grow as δ↓0, each Bδ is a finite Hermitian matrix allowed by the universal quantifiers; positive definiteness is needed only for A. Each spectator block in Mᵤ is exactly D. Its active two-by-two block is

  [[a, b(1+δ¹⁻ᵘ)], [b(1+δᵘ), h(δᵘ+δ¹⁻ᵘ)/δ¹⁻ᵗ]].

At u=s the bottom-right tends to zero since s≥1/2>1−t and 1−s>1−t. At u=t it tends to h since t>1/2. All off-diagonal entries tend to b since t<1. Therefore, by continuity,

  N(H(0)⊕D) ≤ N(H(h)⊕D) for all h,     H(h)=[[x−y,√(xy)],[√(xy),h]].   (1)

The eigenvalues at h=0 are x and −y, simple even when x=y. Near zero, label them U(h)>0 and −V(h)<0. The Taylor expansion of the quadratic eigenvalue equation, or the diagonal entries y/(x+y), x/(x+y) of the bottom-coordinate weights in the two spectral projectors, gives

  (U(h),V(h))=(x,y)+h (y,−x)/(x+y)+O(h²).                              (2)

Fix r>0, set x=r cos θ, y=r sin θ in the open first quadrant, and define F(θ)=g(x,y,z₁,…,z_{d−2}). Applying (1) at this θ with h=−(x+y)k and using (2), the two active singular values differ from (r cos(θ+k),r sin(θ+k)) by Oθ(k²) as k→0. Lipschitzness and permutation invariance thus imply

  F(θ+k) ≥ F(θ)−Oθ(k²),    for both signs of k.

The **one-dimensional** function F is Lipschitz on [0,π/2]. At each of its differentiability points the right and left limits in the last inequality imply F′=0; absolute continuity implies F is constant on the entire arc. This does not restrict a multidimensional almost-everywhere statement to a curve. Endpoints follow by continuity. Hence any two coordinates of a nonnegative vector may be replaced by (√(x²+y²),0) without changing g, even with arbitrary other zero coordinates. Fold coordinates successively: g(w)=g(e₁)‖w‖₂ on the positive orthant, and so on all vectors by sign symmetry. This proves the necessity. In particular, if N is not of this form, the assumed comparison cannot hold on all the real two-by-two-active-block positive definite diagonal tests above. In dimension one all norms in question are proportional.

## 3. Explicit fixed B for each Schatten p; strict counterexamples

Fix s,t as in the theorem. In two dimensions let Aδ=diag(1,δ), B=[[3/2,2],[2,c]], with c to be specified **independently of δ**. Set uδ=δ¹⁻ᵗ; for fixed c, the same entrywise evaluation gives

  Mₛ=H+o(uδ),    Mₜ=H+uδE+o(uδ),    H=[[3,2],[2,0]],   E=[[0,2],[0,c]].

Its eigenvalues are 4,−1; the corresponding orthogonal unit eigenvectors are (2,1)/√5, (1,−2)/√5. For small real u the two positive singular values of H+uE are simple and smooth near 4,1 (the matrix is invertible). At a simple signed eigenvalue λ of H with unit real eigenvector v, differentiating the simple eigenvalue of (H+uE)ᵀ(H+uE) gives 2λ vᵀEv; the corresponding singular-value derivative is sign(λ) vᵀEv. Thus, if 1≤p<∞, the first derivative of ∑σᵢᵖ at H in direction E is

  (p/5)[4(4ᵖ⁻¹+1)+(4ᵖ⁻¹−4)c].

This applies at p=1 since neither singular value is zero. For p≠2 choose

  c=−[4(4ᵖ⁻¹+1)+5]/[4ᵖ⁻¹−4].

The derivative is −p. For p=∞ the larger singular value is simple and has directional derivative (4+c)/5; taking c=−8 gives −4/5. In each case all o(uδ) terms remain negligible by local smoothness (or Lipschitzness), so for the specified B and **all sufficiently small δ>0**, ‖Mₛ‖ₚ>‖Mₜ‖ₚ. There is no uniform threshold in p,s,t asserted. B is indefinite for p>2 and p=∞; no positive-semidefinite-B requirement is being claimed there. (For 1≤p<2 the displayed B happens to be positive definite, since c>8/3.) The dimension-two tests extend to higher Schatten dimensions by adding zero B blocks.

For a single fully rational operator-norm witness take s=1/2,t=3/4, c=−8 and δ=8⁻⁴. In this case

  L=Mₛ=[[3,65/32],[65/32,−1/4]],    R=Mₜ=[[3,9/4],[513/256,−65/64]].

Set q=79/20. Then det(qI−L)=−3481/25600<0, so the larger real eigenvalue of L exceeds q. For Q=q²I−RᵀR, Q₁₁=4238311/1638400 and det Q=193986147/81920000 are positive. Sylvester's test gives ‖R‖op<q<‖L‖op. No numerical optimization is needed.

**Boundaries.** The strict pairs classified here have t<1. The endpoint s=1/2,t=1 holds for every unitarily invariant norm by the original authors; no claim here is made for 1/2<s<t=1. For s=t all comparisons are equalities. The examples do not impose a two-sided spectral window independent of δ, B≥0 in the high-p tests, or A≥I.
