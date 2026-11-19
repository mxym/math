# A parity compatibility graph that binary qubit measurements cannot realize

**AI-assisted research note, internally checked and not externally peer reviewed.** We use two prior theorems: the full biased binary-qubit coexistence criterion of Busch–Schmidt, and Forster's sign-rank lower bound. The claimed consequence is an obstruction to a **stronger binary restriction**, not a counterexample to the finite-outcome qubit conjecture as stated. No smallest example or optimal rank bound is asserted.

**Claim.** On disjoint parts X,Y equal to two copies of the 128 vectors of the seven-dimensional binary vector space, put an edge from x to y exactly when their binary inner product is zero, and put no edges within a part. Not even the pairwise compatibility graph of binary POVMs on one complex qubit can equal this graph. In particular its flag complex (here, just its vertices, edges, and empty face) cannot be the joint-measurability complex of such POVMs. This includes biased POVMs, non-real effects, arbitrary joint parents and pair-specific parents.

## Pairwise kernel

An effect 0≤E≤I determines the binary POVM (E,I−E). In the Pauli basis write E=e₀I+e₁σ₁+e₂σ₂+e₃σ₃, i.e. e∈R⁴ and e₀=tr(E)/2. Put u=(1,0,0,0), e′=u−e, and g=diag(1,−1,−1,−1). Brackets [a,b]=aᵀgb satisfy [e,e]=det E≥0 and [e′,e′]=det(I−E)≥0. Define r_e=√([e,e][e′,e′]), taking the nonnegative square root, including zero.

Busch–Schmidt's Theorem 3, Eq. (55) in [arXiv:0802.4167](https://arxiv.org/pdf/0802.4167), states that E,F are coexistent precisely when

    K(e,f) = r_e r_f − [e,e′][f,f′] + [e,f][e′,f′] + [e,f′][e′,f] ≥ 0.

Their theorem applies to *all* effects, including singular effects and commuting or comparable pairs. Coexistence of a pair of effects is identical to joint measurability of the two binary POVMs: simultaneous events for E and F have the four Boolean cells as parent outcomes; conversely a four-cell parent realizes both events. Equivalently, both conditions mean that there is a positive G with G≤E,F and I−E−F+G≥0; the four effects are G,E−G,F−G,I−E−F+G.

Write T_e=(e(e′)ᵀ+e′eᵀ)/2∈Sym₄(R), let τ(T)=tr(gT), and define the real bilinear form
L(T,S)=tr(gTgS). The trace identities on rank-one tensors give

    τ(T_e)=[e,e′],
    2L(T_e,T_f)=[e,f][e′,f′]+[e,f′][e′,f].

So Φ(e)=(T_e,r_e) is a vector in a real space of dimension 10+1=11 and
K(e,f)=2L(T_e,T_f)−τ(T_e)τ(T_f)+r_e r_f is bilinear in the two features. No positivity property of this bilinear form is required. The feature and K are unchanged by swapping the two outcomes.

## Making the signs strict without increasing the dimension

For two finite families of binary qubit POVMs form their rectangular cross-compatibility matrix S, with Sᵢⱼ=+1 for compatible and −1 for incompatible. Its sign-rank means the minimal real rank over matrices A with SᵢⱼAᵢⱼ>0 at **all** entries.

Deterministic row effects E=0 or I are compatible with all POVMs and have Φ(e)=0. For the purpose of producing a sign witness only, replace each such row effect with I/2: this is still compatible with every column POVM (for a parent, split each column effect in half), hence does not change its row of S. There is no need to change the column effects. Now 0<e₀<1 for every row: for an effect, trace zero or trace two forces E=0 or E=I. Therefore h(e)=(T_e)₀₀=e₀(1−e₀)>0 is a fixed **linear** coordinate of Φ(e).

For each negative cell, K(e_i,f_j)<0. Choose a single δ>0 smaller than every −K(e_i,f_j)/h(e_i) in this finite collection (take δ=1 if there are no such cells). The scores

    Aᵢⱼ=K(e_i,f_j)+δ h(e_i)

are strictly positive in each compatible cell, including K=0, and strictly negative in every incompatible cell. For each j the map Φ(e_i)↦Aᵢⱼ is a linear functional of the same 11 features: it is the original j-th functional plus δ times coordinate T₀₀. Hence rank A≤11. We stress that this is not an unqualified addition of a new dimension for an arbitrary rank-one shift: the shift column already factors through the **left feature matrix**. We have proved sign-rank(S)≤11 for every finite rectangular cross-table of binary qubit POVMs, even if no restrictions at all are placed within either family.

## Parity witness

For H_{xy}=(−1)^(x·y) on F₂⁷, row orthogonality follows from character cancellation: two distinct rows have product a nontrivial character, which sums to zero. Thus HHᵀ=128 I and ||H||₂=√128. By [Forster (2002)](https://www.sciencedirect.com/science/article/pii/S0022000002000193), the real sign-rank of an a×b sign matrix S is at least √(ab)/||S||₂, where the norm is the operator (largest singular value) norm. In particular sign-rank(H)≥√128>11 since 128>121. The cross-table of the conjectured binary realization would be exactly H, contradicting the rank bound. Specifying no edges within the parts gives a single explicit graph; the impossibility actually holds for **every** way of choosing the within-part edges. No claim of binary universality at any smaller number of measurements follows.

**Optional check of the Forster step.** His normalization lemma permits the r-dimensional row factor vectors of a strict sign realization to be placed in radial isotropic position: after perturbing into general position (strict signs persist), applying an invertible map on row vectors and the inverse transpose on column vectors, and rescaling each to norm one, one has Σ_i u_i u_iᵀ=(a/r)I. Write mᵢⱼ=⟨u_i,v_j⟩. Then ab/r=Σmᵢⱼ²≤Σ|mᵢⱼ|=ΣSᵢⱼmᵢⱼ≤||S||₂√(ab) by Frobenius Cauchy–Schwarz on the two factor matrices. This recovers exactly the stated constant. An independently checkable source for the normalization and inequality is [Alon, Moran and Yehudayoff, Appendix A.2](https://proceedings.mlr.press/v49/alon16.pdf).

**Elementary but larger alternative.** Take 12 anchor vertices, and one vertex for each of their 4096 subsets; declare its cross-neighborhood to equal that subset. A realization would give anchors Φ₁,…,Φ₁₂ in R¹¹. Choose a nontrivial linear dependence ΣcᵢΦᵢ=0; orient it to have some negative cᵢ. The query for {i:cᵢ≥0} gives Kᵢ≥0 there and Kᵢ<0 for all cᵢ<0, so Σ cᵢKᵢ>0, contradicting linearity. This does not require strictification or any sign-rank lower bound, but uses 4108 vertices instead.

## Scope

[Andrejić and Kunjwal (2020), Conj. 4](https://doi.org/10.1103/PhysRevResearch.2.043147) asks about qubit POVMs, without a requirement that they be binary. Their principal constructive examples are binary. [Kunjwal (2025), §§5.1, 5.3](https://arxiv.org/pdf/2512.10063) specifies finite measurement sets and general outcome sets, differentiating a binary-specific sufficient condition. This obstruction is for two outcomes, not for unrestricted finite outcomes, infinite settings, or higher Hilbert dimension. [Kunjwal, Heunen and Fritz (2014)](https://arxiv.org/abs/1311.5948) give universal realizations in growing dimension; this does not imply universal binary realizability in dimension two. We do not claim a new pair-compatibility criterion, new Hadamard sign-rank bound, or any priority guarantee.
