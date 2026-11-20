# An integral coordinate bound for a six-vertex motif in a hypothetical Conway 99-graph

**Theorem.** In any strongly regular graph with parameters (99,14,1,2), let n₃ count unordered pairs of disjoint triangles with exactly two edges between them. Then n₃≥858. Hence the number of induced six-cycles is at least 210144. No symmetry hypothesis is made; existence and nonexistence remain unresolved.

We use the projector and trace identities of [Wave 20](https://github.com/YesterdaysLemon/conway-99-research/blob/main/agents/2026-07-23-wave20-global-schur.md) and the local tensor interpretation of [Wave 21](https://github.com/YesterdaysLemon/conway-99-research/blob/main/agents/2026-07-23-wave21-local-diagonal.md), rederived below. The additional step is to use the actual vertex-coordinate realization of the incidence projector. Its constant denominator three supplies a lower bound on every tensor row, while the even triangle Gram forces every squared row norm to be divisible by fourteen.

## 1. An integral projector on triangles

A graph edge lies in exactly one triangle, and its 14 neighbors pair off, so each vertex is in seven triangles. There are 99·7/3=231 triangles. Let N be the vertex–triangle incidence matrix and A adjacency. Then NNᵀ=7I+A and A²+A=12I+2J. The restricted eigenvalues are 3 and −4, so E=(3I−A+J/9)/7 is the orthogonal projector onto the −4 space (it is zero on the constant line). Define the symmetric matrix

    M=7NᵀEN=Nᵀ(3I−A+J/9)N.

It is positive semidefinite and integral, satisfies M1=0 since N1=7·1, and satisfies M²=21M since E(7I+A)=3E. On a triangle its diagonal is 9−6+1=4. For two distinct triangles sharing a vertex, three times their intersection size is 3, the adjacency term is 4, and the all-one term is 1; no other cross-adjacency can occur since it would give the shared vertex's edge two common neighbors. Thus M=0 on intersecting distinct triangles. On two disjoint triangles M=1−j, where j is the number of cross edges. Distinct cross edges cannot share an endpoint since that would put an edge of the opposite triangle in two triangles, hence 0≤j≤3.

For a triangle T let a_j be the number of other disjoint triangles with j cross edges. The row sum M1=0 and row squared length (M²)TT=84 give

    4+a₀−a₂−2a₃=0,       16+a₀+a₂+4a₃=84.
    a₂=36−3a₃,             a₀=32−a₃≥20.

It follows that 3 divides n₃ since 2n₃=Σ_T a₂. Every row has an odd entry. The row cubic sum is

    Σ_U M_TU³=64+a₀−a₂−8a₃=2a₂−12.

With W=M∘M the entrywise square and B=MWM, cyclicity of trace therefore gives the unrestricted identity

    tr B=21 tr(MW)=21 Σ_T,U M_TU³=84(n₃−693).       (1)

## 2. The local Gram tensors are nonzero, traceless, and have squared norm divisible by four

Realize M as the Gram of vectors u_T. Their integer span Λ is an even integral positive-definite lattice: all mutual pairings are integers, each generator has squared norm four, and the radical has already been removed by realizing the Gram in its real span. For discreteness, any independent spanning sublist has integer nonsingular Gram, so every u_T has bounded-denominator coordinates in that basis.

Identify the ordinary real tensor product of the Euclidean span with its space of linear maps by x⊗y ↦ (v↦(y,v)x). Give the tensor product the usual Hilbert–Schmidt inner product: (x⊗y,x'⊗y')=(x,x')(y,y'). For each T form

    S_T=Σ_U M_TU u_U⊗u_U   in   Λ⊗_ℤ Λ.

It is self-adjoint, trace zero since Σ_U 4M_TU=0, and the Gram of the S_T is B: the Gram of u_U⊗u_U is exactly W. In particular ||S_T||²=B_TT.

Set D=(W−M)/2. This is an integral symmetric matrix with diagonal (16−4)/2=6, so zᵀDz is even for every integral z. Consequently

    B=M³+2MDM=441M+2MDM.

Its diagonal entries are multiples of four. Moreover B≡M mod2, and each row of M has a₀≥20 entries equal to 1. Therefore B has no zero row. As it is a Gram matrix, a vanishing S_T would give a zero row. This proves the nonvanishing and positive divisibility at every T, without assuming anything about n₃.

## 3. Coordinate coset and integral row norm

For each triangle T (indicator vector n_T on the 99 vertices), use the actual vertex realization
```
w_T=7E n_T=(3I−A)n_T + (1/3)1 = s_T+(1/3)1.
```
Here s_T is an integer vector and w_T is perpendicular to the constant line. The 99×231 matrix H with columns w_T satisfies
```
HᵀH=7M,      H M=21H.
```
The first follows from E²=E and M=7NᵀEN. For the second, H M=49E NNᵀE N=147 EN, since NNᵀ=7I+A and (7I+A)E=3E.

Consider the real symmetric matrix on vertices
```
P_T=Σ_U M_TU w_U w_Uᵀ.
```
The squared Frobenius norm is 49 B_TT since the Gram of the rank-one matrices w_U w_Uᵀ is 49W. Also P_T1=0. Since Σ_U M_TU=0 and Σ_U M_TU s_U=21w_T, direct expansion gives
```
P_T=Σ_U M_TU s_U s_Uᵀ +7(w_T1ᵀ+1w_Tᵀ).
```
The first summand is integral. The second has entries in 14/3+ℤ. Therefore every entry of P_T is in −1/3+ℤ. Every row has length 99 and sum zero. Write one such row as (m_i−1/3), m_i integers. Then Σm_i=33 and
```
Σ_i(m_i−1/3)² = 22 + Σ_i m_i(m_i−1) ≥22.
```

The columns w_U generate a lattice L with Gram 7M. Every element of L has squared norm divisible by 14: the diagonal of M is even, and distinct Gram entries occur twice in the norm of an integer combination. Moreover the ith column p_i of P_T belongs to L, since
```
p_i = Σ_U M_TU s_U(i) w_U + (1/3)Σ_U M_TU w_U
    = Σ_U M_TU s_U(i) w_U + 7w_T.
```
Thus each of the 99 columns has squared norm at least 28, the first multiple of 14 at or above 22. Consequently
```
49 B_TT = ||P_T||_F² ≥ 99·28 = 2772 > 49·56.
```
As B_TT is a multiple of four, B_TT≥60. Now 84(n₃−693)=tr B≥231·60, so **n₃≥858**. The separately established [six-vertex count relation](https://github.com/YesterdaysLemon/conway-99-research/blob/main/verification/wave23-literature-audit/2026-07-23-wave23-literature-audit.md) gives number of induced six-cycles = 209286+n₃ ≥ **210144**. The graph-specific doubling and coset arguments here do not depend on the earlier integral-tensor rank inequality or on any classification of lattices.
