# Dimension-independent incompressibility of a binary cq source

The trace norm is the sum of singular values (no factor 1/2). Mutual information is in bits. For a matrix K on dimension D, write K°=K−(Tr K/D)I and use the unnormalized Hilbert–Schmidt norm ||K||₂.

**Theorem.** For every sufficiently large integer k there are two positive definite density matrices σ₀,σ₁ on B of dimension D=8k. Put
`ω_AB=(|0><0|⊗σ₀+|1><1|⊗σ₁)/2`, with A classical. For every c between 1 and D and every pair of channels T:B→C, R:C→B with dim(C)≤c,

    ||ω−(id_A⊗R T)(ω)||₁ ≥ 10^(−19)(1−c/D).                              (1)

The same bound holds for the stronger finite flagged model: the output of T is diagonal in a classical register X of arbitrary finite size, and each quantum block C_x has dimension at most c; R sees X and the quantum block. The source is fixed for each k, independent of the choice of c, encoder, decoder, or flag alphabet. T and R may be tailored to the source but act locally on B, without access to A. There is no free shared entangled state. For every encoder in either model, writing Y for its entire output,

    I(A:B)_ω − I(A:Y)_(id⊗T)(ω) ≥ [10^(−38)/(4 ln 2)] (1−c/D)^2.          (2)

In particular there is no bound on the output dimension depending only on the allowed information loss when A is classical binary. The unbounded subsequence D=8k suffices: for any proposed finite bound c at a fixed error smaller than 10^(−38)/(16 ln 2), take D≥2c. This is the binary-classical case asked just after Theorem 1 and Eq. (1) of [Wolff et al.](https://arxiv.org/html/2611.28361v1); it is not the problem of attainment of the bottleneck optimum for one fixed input in their Appendix G. The displayed proportional bounds are asserted on D=8k, not at all dimensions.

## 1. A sign witness gives a commutator cost

Let Λ be a channel on matrices of size D with Kraus operators K_l, and let L be an invertible Hermitian matrix with sign S=sgn(L) and |L|≥gI/D. The adjoint Λ* is unital, hence T_S=Λ*(S) is Hermitian of operator norm at most 1. Write Q=I−(S T_S+T_S S)/2, which is positive since the symmetrized term has norm at most 1. Using S²=I and [|L|,S]=0 gives

    ||L−Λ(L)||₁ ≥ Tr S(L−Λ(L)) = Tr |L|Q
                ≥ (g/D) Tr Q = (g/(2D)) Σ_l ||[K_l,S]||₂².              (3)

The last identity follows by expanding each squared commutator: the two squared terms sum to 2D since Σ_l K_l* K_l=I, and the two cross terms sum to 2 Tr S Λ*(S). No unitality of Λ is needed.

If Λ=R T and dim(C)≤c, products of encoder and decoder Kraus operators have rank at most c. For the flagged model, decompose T into a completely positive instrument T_x with block outputs on C_x, and restrict R to each embedded block to get the channels R_x. Then Λ=Σ_x R_x T_x, and the branchwise Kraus products again have rank at most c regardless of the number of flags. Any Kraus representation obeying that rank bound satisfies

    Σ_l ||K_l°||₂² = D−Σ_l |Tr K_l|²/D ≥ D−c,                            (4)

since |Tr K_l|²≤||K_l||₁²≤rank(K_l)||K_l||₂² and the total squared Kraus norm is D.

## 2. Uniform gap for four involutions

By the Hermitian quantum-expander theorem of Hastings (the degree-four case with two independent Haar unitaries and their adjoints), for every sufficiently large k there exist U,V on ℂ^k such that the self-adjoint averaging channel (Ad_U+Ad_U*+Ad_V+Ad_V*)/4 has largest eigenvalue on traceless matrices at most 7/8. This uses 7/8>√3/2. Expanding squared commutators then shows that for every k-by-k matrix M,

    ||[U,M]||₂²+||[V,M]||₂² ≥ (1/2)||M°||₂².                            (5)

This also holds for non-Hermitian M under the complex Hilbert–Schmidt inner product.

On the space H=ℂ²⊗ℂ^k, of dimension n=2k, use the four Hermitian unitaries
`R₁=Z⊗I, R₂=X⊗I, R₃=[[0,U],[U*,0]], R₄=[[0,V],[V*,0]]`.
They are traceless. For a traceless matrix M on H let P(M)=I₂⊗N, with N=(M₀₀+M₁₁)/2. In block coordinates the Z commutator controls the two off-diagonal blocks, and the X commutator has both diagonal-block differences in its off-diagonals. In particular

    ||M−P(M)||₂² ≤ (||[M,R₁]||₂²+||[M,R₂]||₂²)/4.

Let E_R=Σ_i ||[M,R_i]||₂². Tr N=0, and Σ_{i=3}^4 ||[P(M),R_i]||₂² equals twice the left side of (5) for N, so is at least ||N||₂². It is at most `2 E_R+16||M−P(M)||₂²≤6 E_R`, by (a+b)²≤2a²+2b² and ||[R_i,F]||₂≤2||F||₂. Thus ||P(M)||₂²=2||N||₂²≤12 E_R and the four-reflection gap is

    Σ_i ||[M,R_i]||₂² ≥ (4/49)||M°||₂²,                                 (6)

by orthogonality, extending to arbitrary M by subtracting its scalar part.

## 3. The frame, the pencil, and ideal sign operators

Write J for the four-by-four all-ones matrix. Let V₀=(I+J)/√7, with unit columns v_i of pairwise inner product 6/7, and let W=V₀^(−*)=√7(I−J/5), with columns w_i. Thus <v_i,w_j>=δ_ij. Set P_i=v_i v_i*, B₀=W W*, A₀=W diag(1,2,3,4)W*. The eigenvalues of B₀ are 7/25 and 7, with multiplicities 1 and 3. In particular µ=7/25 is its least eigenvalue. On B=ℂ⁴⊗H put

    B_raw = B₀⊗I,
    A_raw = A₀⊗I + κ E,      E=Σ_i w_i w_i*⊗R_i,      κ=10^(−10).

Equivalently A_raw is the congruence by W⊗I of the block diagonal blocks i I+κR_i; hence it is positive definite, as is B_raw. Set σ₀=B_raw/Tr B_raw and σ₁=A_raw/Tr A_raw. Tr R_i=0 gives Tr A_raw=n·266/5 and Tr B_raw=n·532/25; their trace ratio Tr B_raw/Tr A_raw=2/5. Both density matrices are full rank and normalized individually.

For i∈{1,2,3,4} and f∈{−2,0,2}, let λ=i+κ f and
`L_{i,f}^{raw}=A_raw−λ B_raw`. Let G_i=(A₀−i B₀)⊗I, and F_{i,f}=E−f B_raw, so L_raw=G_i+κ F_{i,f}. Its unperturbed kernel is range(P_i⊗I). The compression of F_{i,f} there is P_i⊗(R_i−fI). By the same congruence, the full L_raw is the congruence of diagonal blocks (j−i)I+κ(R_j−fI). For j=i all absolute eigenvalues of the block are at least κ, and for j≠i they are at least 1−3κ≥κ. Hence |L_raw|≥µ κ I, using the smallest singular value under the congruence. The nonzero singular values of G_i similarly have minimum at least µ: use the inequality s_j(W X W*)≥s_min(W)² s_j(X), valid by the variational characterization of singular values. On the kernel put sgn(G_i)=0.

The twelve *ideal* Hermitian unitaries on B are

    J_{i,f} = sgn(G_i) + P_i⊗sgn(R_i−fI).

The signs in the last term are +I, R_i, −I for f=−2,0,2 respectively. In particular the difference of the two extreme witnesses equals 2P_i⊗I. We next check a uniform commutator gap for the ideal family and perturb it to the actual signs.

### 3.1. Fixed-frame gap

For a four-by-four matrix Z let a_i=v_i* Z v_i, write Z v_i=a_i v_i+e_i and v_i* Z=a_i v_i*+f_i*, where e_i and f_i are perpendicular to v_i. Set E_F=Σ_i||[P_i,Z]||₂²; it equals Σ_i(||e_i||²+||f_i||²) by the off-diagonal block decomposition at P_i. For distinct i,j,
`(a_i−a_j)<v_i,v_j>=v_i* e_j−f_i* v_j`.
If ā is the average of the a_i, the identity Σ_i|a_i−ā|²=(1/8)Σ_{i,j}|a_i−a_j|² gives Σ_i|a_i−ā|²≤(7/6)² E_F. The columns of (Z−ā I)V₀ are (a_i−ā)v_i+e_i with orthogonal terms, and ||V₀^(-1)||²=7. The closest scalar is the trace mean, so

    ||Z°||₂² ≤ ||Z−ā I||₂² ≤ 7(1+(7/6)^2) E_F = (595/36) E_F.

On B the tensor extension says that squared distance from the subspace I₄⊗M_n is bounded by (595/36) times Σ_i||[P_i⊗I,K]||₂²: expand the second tensor factor in an orthonormal matrix basis and apply the inequality to every coefficient.

### 3.2. Ideal gap on the full matrix space

For traceless K on B let Q=I₄⊗N be the Hilbert–Schmidt projection onto I₄⊗M_n, so Tr N=0. With E_J=Σ_{i,f}||[K,J_{i,f}]||₂², the extreme-sign difference and §3.1 give

    ||K−Q||₂² ≤ (595/72) E_J < 9 E_J      if E_J>0,

and ≤9 E_J in all cases. On Q the commutators with J_{i,0} reduce to P_i⊗[N,R_i] because sgn(G_i) is driven by the first factor only, and ||P_i||₂=1. By (6) their total squared norm is at least (4/49)||N||₂²=||Q||₂²/49. It is at most 2E_J+32||K−Q||₂² by comparing Q with K and using ||J_{i,0}||=1 for four i. Therefore

    ||K||₂² = ||K−Q||₂²+||Q||₂²
            ≤ [9+49(2+32·9)] E_J <15000 E_J     if E_J>0.

For E_J=0 the same non-strict inequalities force K=0. This yields E_J≥||K°||₂²/15000 for all K.

## 4. Uniform perturbation of the twelve signs

Here all unscripted operator norms in estimates for matrices are spectral norms. We show that S_{i,f}=sgn(L_{i,f}^{raw}) differs from J_{i,f} by at most 855300κ in operator norm. Fix i,f, abbreviate G=G_i and F=F_{i,f}, and split into the kernel of G and its orthogonal complement. In this splitting write

    G=[[0,0],[0,H₀]],     F=[[F₁,Y],[Y*,F₂]].

The norm of both G and F is at most 21 (each comes from a W-congruence of blocks of norm at most 3). Also ||H₀^(-1)||≤1/µ. The anti-Hermitian
`Z=[[0,−Y H₀^(-1)],[H₀^(-1)Y*,0]]`
has norm at most 21/µ=75. Its commutator [Z,G] cancels the off-diagonal block of F. Conjugating by exp(κZ) therefore gives

    exp(κZ)(G+κF)exp(−κZ) = diag(κF₁,H₀+κF₂)+Err,
    ||Err|| ≤ κ²(2·75²·21+2·75·21)=239400κ².

Indeed the conjugation second derivative on G has norm at most 4||Z||²||G||, and the conjugation first derivative on F has norm at most 2||Z||||F||; the maps are unitary conjugations, so these bounds hold at every intermediate time.

For two invertible Hermitian matrices with minimum absolute eigenvalue at least h, the difference of their signs has norm at most ||M−N||/h. For completeness, apply the resolvent identity in the symmetric improper integral `sgn(M)=π^(-1)∫_(−∞)^∞(M−itI)^(-1)dt`; the difference integrand has integrable norm bounded by ||M−N||/(h²+t²). The scalar integral gives this sign convention by the spectral theorem. The block-diagonal matrix on the right has gap at least κ, since min|F₁|≥1 and the gap of H₀+κF₂ is at least µ/2. The rotated actual pencil has gap at least µκ by §3. Comparing its sign to the block-diagonal sign costs at most (239400/µ)κ. Comparing sgn(H₀+κF₂) to sgn(H₀) costs at most (42/µ)κ. Conjugating back a Hermitian unitary by exp(−κZ) costs at most 150κ by the first-derivative bound. These sum to 855300κ.

On traceless matrices the ℓ² direct-sum norm of the discrepancy in the twelve commutator maps is at most `2 sqrt(12)·10^6κ < 1/(2 sqrt(15000))`, because each error matrix has norm at most 10^6κ. The discrepancy annihilates scalars. Hence the exact sign family satisfies

    Σ_{i,f} ||[K,S_{i,f}]||₂² ≥ ||K°||₂²/60000                          (7)

by the triangle inequality for the linear commutator maps. In particular the perturbation does not introduce an additive error proportional to D into the final lower bound.

## 5. Recoverability and mutual information

Let Λ=R T. The cq recovery norm δ, without dividing by 2, is exactly
`δ=(||σ₀−Λσ₀||₁+||σ₁−Λσ₁||₁)/2`, by the equal-probability classical direct sum. For each of the twelve thresholds use

    L=σ₁−tσ₀=L_raw/Tr A_raw,      t=(2/5)(i+κ f).

Here 0<t≤2, so ||L−Λ(L)||₁≤4δ. The normalized matrix sign is S_{i,f}, and §3 gives |L|≥(2κ/95)I/D because D=4n. Put g=2κ/95 in (3), and sum all twelve inequalities. By (7) and (4),

    48δ ≥ (g/(2D)) Σ_l Σ_{i,f}||[K_l,S_{i,f}]||₂²
        ≥ g(D−c)/(120000 D).

This is stronger than (1) with κ=10^(-10), since g/(96·60000)=κ/273600000≥10^(-19). Neither averaging across thresholds nor replacing the average cq error with a maximum across its two blocks is implicit.

For any encoder T, apply the approximate-recovery implication of [Wolff et al. Lemma 3](https://arxiv.org/html/2611.28361v1) to the true full output Y. In the cited base-2 convention, information loss ε yields a channel with cq recovery norm at most 2 sqrt(ε ln 2). In the flagged case this channel is evaluated on inputs diagonal in X, so its restriction to each flag is indeed a decoder of the allowed type; no additional classical storage enters (4). Combine with (1) to get (2). The rank and recovery arguments apply to all source-dependent choices simultaneously, with c any legal dimension and c=D giving a vacuous zero lower bound.
