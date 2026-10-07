# A polynomial-dimensional refinement of sharp simplex stability

Date: 7 October 2026. Status: separate written mathematical refinement; independent analytic model audit passed. This is not human peer review. This file does not modify the published/frozen proof or constants, and is not a Lean proof or a priority claim.

## Result

Use exactly the invariant and excess of the supplied manuscript:

- R_proj(K) = |ΠK| / |K|^(d−1).
- a(K) = (d/(d+1))^d R_proj(𝒫K)/R_proj(K) − 1.
- e(K) = a(K) − 1/(d+1).
- E(K,S) = inf{t≥0 : K⊂z_S+(1+t)(S−z_S)}.

For every d≥3, every full-dimensional convex body K⊂R^d, and every maximum-volume inscribed simplex S,

    E(K,S) ≤ G_d e(K)^(1/(d−1)) ≤ 2^20 d^6 e(K)^(1/(d−1)).

The exponent is unchanged and optimal, by the actual simplex-truncation family in the supplied manuscript. The novelty asserted here is only a proved refinement relative to that supplied argument; no first-discovery or best-known-result claim is made.

Exact constants for the refinement are:

    m = d−1,
    R = d sqrt(d+2),
    M = 4dR,
    C = (d+1)^2(d+2),
    J = (d/2)(2R)^d [1+M+d 2^(d−1) M],
    L = 2 sqrt(m)(R+1),
    G_d = 8(R+1)d L (JC)^(1/m),
    e_0 = 1 / [JC (8dL)^m].

For 0≤e≤e_0, the stronger local estimate with coefficient G_d/2 holds. Moreover G_d e_0^(1/m)=R+1, which makes the global branch transparent.

The main structural strengthening is valid for probability laws, without any convex-body realization assumption: a centered full-dimensional probability law of bounded support admits an assignment to d+1 affinely independent support points with mean distance at most

    diam(supp ν) · [(d+1)(d+2)/2] · (B−A)/B.

Distances and diameter may be taken in any fixed norm. Unlike the original anchor selection, there is no dispersion assumption, inverse determinant, covariance estimate, second determinant moment, or small-probability conditioning loss in this assertion.

## 1. The stronger integrated assignment theorem

Let ν be centered with bounded support spanning R^d. Let X_1,… be iid ν, and define the FIRST absolute determinant moments

    A = E |det(X_1,…,X_d)|,
    B = E |det((X_0,1),…,(X_d,1))|,
    D = B−A.

Full-dimensionality and centering imply A>0 and B>0. Set n=d+1 and N=n(n+1)/2. For an ordered d-tuple x, define

    F_x(y)=det((x_1,1),…,(x_d,1),(y,1)),
    P(x)=E(F_x(X))_+,
    N_−(x)=E(−F_x(X))_+.

Centering gives D=2E min(P,N_−)≥0. For independent test points Y,Z define the nonnegative witness

    ψ_x(Y,Z)=min((F_x(Y))_+,(−F_x(Z))_+)
             +min((−F_x(Y))_+,(F_x(Z))_+).

Its expectation over all d+2 iid samples is at most D.

For anchors W=(w_0,…,w_d), let V(W) be the absolute lifted determinant, NOT the simplex volume V(W)/d!. Define H(W) by integrating in x the sum of these N witnesses:

1. For every i, base = the d other anchors; tests = w_i,x.
2. For every i<j, base = x and the d−1 anchors other than i,j; tests = w_i,w_j.

Order bases by a fixed convention; ψ is unaffected by changing the overall determinant sign. Each summand uses d+2 iid samples before conditioning, so E H≤ND.

### Selection without an expectation-of-ratio error

On anchor tuples define the probability measure

    dP_V(W) = [V(W)/B] dν^(d+1)(W).

This is a probability because E V=B. It gives full mass to support tuples with V>0. Define H/V only there. Then

    E_{P_V}(H/V) = E[H 1_{V>0}]/B ≤ ND/B.

Consequently some support tuple with V>0 satisfies H/V≤ND/B. Indeed, if the integrable ratio were strictly larger everywhere on a full-measure set, its expectation would be strictly larger too. No compact minimum on the open set {V>0} is assumed. When D=0, the ratio is zero P_V-almost surely.

### Pointwise clipped-witness bound

Fix such a tuple and let α_i(x) be its affine barycentric coordinates. Let r(x) be the first index attaining the largest positive coefficient; some positive coefficient exists because Σα_i=1. This is Borel measurable. Put

    φ(x)=Σ_i min(1,(−α_i(x))_+)
         +Σ_{i<j} min((α_i(x))_+,(α_j(x))_+).

The first witnesses equal V min(1,(−α_i)_+). When α_i,α_j>0, the pair witness is V min(α_i,α_j), because the two tested determinants have opposite signs. When either is nonpositive, the displayed lower bound is zero. Thus V Eφ≤H.

Let Δ=diam(supp ν). If some α_i≤−1, then φ≥1 and ||x−w_r||≤Δ≤Δφ. Otherwise every negative magnitude is below 1, so clipping is inactive. Let N_x=Σ(−α_i)_+ and U_x=Σ_{i≠r}(α_i)_+. The pairs containing r give U_x≤Σ_{i<j}min((α_i)_+,(α_j)_+). Also

    x−w_r = Σ_{i≠r} α_i(x)(w_i−w_r),

so ||x−w_r||≤Δ(N_x+U_x)≤Δφ. Therefore in all cases

    h:=E||X−w_{r(X)}|| ≤ Δ Eφ ≤ Δ H/V ≤ Δ N D/B.

This is the entire stronger assignment theorem. In the Euclidean unit ball, Δ≤2, giving h≤(d+1)(d+2)D/B.

### Quantitative origin inclusion when dispersion is supplied

If E(u·X)_+≥η for every unit u and h≤η−b with b>0, then the assigned law has E(u·w_r)_+≥b. At least one anchor has u·w_i≥b in every direction. Thus bB_2^d⊂T=conv(w_i). This implication is separate from the assignment theorem and is exactly where cone-body geometry will enter.

## 2. Prescribed-simplex normalization and two elementary improvements

Fix the user's originally prescribed maximum simplex S; do not select a replacement maximum. Apply an invertible affine map sending S to the regular simplex Δ centered at zero with inradius 1. Its vertices v_i have ||v_i||=d and v_i·v_j=−d for i≠j.

For every x∈K, replacing vertex i by x changes the simplex volume by |α_i(x)|. Maximality gives |α_i(x)|≤1. Since Σα_i=1,

    ||x||^2 = d[(d+1)Σα_i(x)^2−1]
             ≤ d[(d+1)^2−1] = d^2(d+2).

Therefore

    B_2^d⊂Δ⊂K⊂R B_2^d,     R=d sqrt(d+2).

Also, dilation of Δ by 1+t about its centroid is equivalent to α_i≥−t/(d+1). The same |α_i|≤1 immediately yields the GLOBAL bound

    E(K,Δ)≤d+1.

This is stronger than using K⊂RΔ for the global branch.

## 3. Actual cone-law dispersion: no arbitrary-law substitution

For this normalized convex body define ν as the pushforward of h_K(u)dS_K(u)/(d|K|) under u↦u/h_K(u). The classical identities ∫h_K dS_K=d|K| and ∫u dS_K=0 make it a centered probability law, supported on ∂K°⊂B_2^d. Its support spans R^d because every orthogonal projection of K has positive (d−1)-volume. The supplied cone representation gives

    a(K)=B/[(d+1)A],
    D/B = (d+1)e/[1+(d+1)e].

Thus Section 1 gives anchors and a measurable assignment satisfying

    h ≤ C e/[1+(d+1)e] ≤ C e,
    C=(d+1)^2(d+2).

Cauchy's projection formula, including its factor 1/2, gives

    E|u·X| = 2π_K(u)/(d|K|),
    E(u·X)_+ = π_K(u)/(d|K|)

for unit u, where centering gives the second equality.

The geometric lower bound is particularly simple. Slice K by lines parallel to u over K|u⊥. Every nonempty chord has length at most the directional width w_K(u)=h_K(u)+h_K(−u). Fubini therefore gives

    |K|≤w_K(u)π_K(u)≤2Rπ_K(u).

It follows that

    E(u·X)_+≥1/(2dR)=2/M,     M=4dR.

This is valid for actual convex-body cone laws. It is NOT asserted for arbitrary centered laws merely because their support lies in a ball.

If h≤1/M, Section 1 implies M^(-1)B_2^d⊂T⊂B_2^d. Hence P=T° is a genuine enclosing simplex with

    B_2^d⊂K⊂P⊂M B_2^d.

Each selected anchor lies on ∂K°, so h_K(w_i)=h_P(w_i)=1.

## 4. Complete assignment-to-projection conversion

Let q_i be the vertex of P opposite w_i and λ_i>0 the barycentric coordinates of zero in T. The cone law of P is Σλ_iδ_{w_i}: it is supported on exactly these facet polar images, centered, and barycentric weights are unique.

Let p_i=P(r(X)=i) and c=Σp_iw_i. Centering gives ||c||≤h. The barycentric functions of T are

    α_i(x)=λ_i(1−q_i·x).

Thus p_i−λ_i=−λ_i q_i·c and Σ|p_i−λ_i|≤Mh. Comparing the assigned law and ν_P, for every unit u,

    |E_ν|u·X|−E_{ν_P}|u·X||≤(1+M)h,

and consequently

    |π_K(u)/|K|−π_P(u)/|P||≤(d/2)(1+M)h.

Since h_P is M-Lipschitz and h_P(w_i)=1,

    0≤z:=∫(h_P(x)−1)dν(x)≤Mh≤1.

By homogeneity in x=u/h_K(u), its left side equals V(K[d−1],P)/|K|−1. Minkowski's first inequality, equivalently the first variation of Brunn–Minkowski, yields

    |P|/|K|≤(1+z)^d,
    |P|−|K|≤d 2^(d−1) Mh |K|.

Because ν_P⊂B_2^d, π_P(u)/|P|≤d/2. Combining these facts and |K|≤(2R)^d proves

    0≤π_P(u)−π_K(u)≤Jh

with J as stated. Nonnegativity uses the genuine inclusion K⊂P.

## 5. An improved projection cap using K's radius

Suppose B_2^d⊂K⊂P, K⊂R B_2^d, and all projection deficits are ≤ε. Let s=d_H(K,P). The conclusion is

    s≤2 sqrt(d−1)(R+1) ε^(1/(d−1))

whenever sqrt(d−1) ε^(1/(d−1))≤1/2. No bound on P's outer radius is needed for this statement, apart from compactness.

Proof: for s>0 choose a farthest q∈P, its nearest k∈K, and n=(q−k)/s. The projection optimality condition gives n·k=h_K(n). Crucially,

    ||q||≤R+s.

Choose a unit u⊥n and project onto u⊥, of dimension m=d−1. Let τ=s/[2(R+s+1)]<1. The projected P contains the ball (1−τ)q̄+τB_2^m. Its lowest n-coordinate is at least

    n·q−τ(||q||+1)≥h_K(n)+s/2,

so the ball is disjoint from projected K. It contains a cube of side 2τ/sqrt(m), hence

    ε≥[s/(sqrt(m)(R+s+1))]^m.

Putting t=sqrt(m) ε^(1/m), we have s≤t(R+s+1). If t≤1/2, this rearranges to s≤2t(R+1). The case ε=0 follows from the same cap inequality. This proves the claim.

This step avoids transporting the large polar radius M into every geometric factor. Hereafter L=2sqrt(m)(R+1).

## 6. Local gate and retention of the original maximum simplex

Assume 0≤e≤e_0. Since J≥M and 8dL≥1,

    h≤Ce≤1/[J(8dL)^m]≤1/M.

Section 4 applies with ε=Jh. Write y=(JCe)^(1/m). Then

    y≤1/(8dL),
    sqrt(m)y≤1/[16d(R+1)]≤1/2.

The improved cap gives

    s≤L(Jh)^(1/m)≤Ly≤1/(8d).

In particular P⊂(R+s)B_2^d⊂(R+1)B_2^d. Also h_K≥h_P−s≥(1−s)h_P, because h_P≥1, so (1−s)P⊂K.

The fixed original Δ is maximum. Therefore

    |Δ|/|P|≥(1−s)^d≥1−ds.

Put δ=ds≤1/8. Express the vertices of Δ in barycentric coordinates in P, producing a nonnegative column-stochastic (d+1)×(d+1) matrix W with |det W|=|Δ|/|P|≥1−δ. Hadamard gives each column norm≥1−δ, and its largest coordinate is at least the squared norm, hence at least 1−2δ.

These dominant coordinates occupy distinct rows: if two occupied the same row, the independent-row-selection interpretation of the permanent would give

    |det W|≤per(W)≤1−(1−2δ)^2≤4δ<1−δ,

a contradiction. Match vertices using these distinct rows. Each vertex of Δ differs from its matched vertex of P by at most

    2δ diam(P)≤4(R+1)ds.

Every vertex of P is matched. Thus

    K⊂P⊂Δ+4(R+1)ds B_2^d⊂[1+4(R+1)ds]Δ,

using B_2^d⊂Δ. This proves

    E(K,Δ)≤4(R+1)dL(JC)^(1/m)e^(1/m)=(G_d/2)e^(1/m).

All inequalities include e=0: then h=0, projection deficits vanish, s=0, and the same matching identifies the simplices.

## 7. Global branch and original centroid

By the exact definitions,

    G_d e_0^(1/m)=R+1≥d+1.

For e>e_0, the universal maximality bound E(K,Δ)≤d+1 therefore gives E(K,Δ)≤G_d e^(1/m). For e≤e_0 Section 6 applies. This closes the global theorem without any enormous minimum threshold entering the final constant.

The affine normalization used the prescribed S throughout. An invertible affine map sends its centroid to the centroid of Δ and intertwines homotheties about these centroids. Pulling back the final containment gives exactly the stated dilation about z_S. The supplied invariant a, hence e, is affine invariant. No assertion that an original Euclidean unit ball is preserved under affine pullback is needed.

## 8. Explicit polynomial bound for G_d

For d≥3,

    C≤3d^3,
    M≥1,
    1+M+d2^(d−1)M≤d2^d M,
    J≤d^2M(4R)^d,
    R+1≤2R,
    L≤4sqrt(d)R.

Consequently

    G_d≤256 d^(3/2)R^3 [12d^5MR]^(1/(d−1))
       =256 d^(3/2)R^3 [48d^6R^2]^(1/(d−1)).

Since R^2=d^2(d+2)≤(5/3)d^3,

    G_d≤256(5/3)^(3/2)d^6 [80d^9]^(1/(d−1)).

For integer d≥3, d≤3^((d−1)/2): this follows by induction, since (d+1)/d≤4/3<sqrt(3). Therefore

    [80d^9]^(1/(d−1))≤sqrt(80)·3^(9/2)<1280.

Also (5/3)^(3/2)<9/4. Hence

    G_d<576·1280 d^6=737280d^6<2^20d^6.

This polynomial is deliberately nonoptimized. The exact displayed G_d is substantially smaller in many dimensions.

## 9. Sharpness, the stronger realized lower bound, and remaining scope

The exponent cannot improve: the pinned equal-intercept simplex truncations have E=(d+1)t and e~[d(d−1)/(d+1)^2]t^(d−1). The direct actual-polytope construction proved in SQUARE_PYRAMID_LOWER_BOUND.md gives the stronger global coefficient obstruction

    G_d ≥ (d+1)[d(d+1)]^(1/(d−1)).

Its order is d+1+2 log d+O((log d)^2/d), leaving a gap between linear and d^6 growth. It rules out a dimension-free coefficient, while the theorem above rules out the necessity of superpolynomial dimension dependence for this invariant and every-maximum-simplex metric.

The abstract assignment theorem controls mean transportation distance, not support Hausdorff distance. Rare atoms can remain far away while carrying negligible mass. The cone identities, centering, enclosing inclusion, first variation, and projection caps are essential to the geometric conversion. The companion weighted_anchors.md gives the detailed arbitrary-law theorem and exact stress tests.

This is a written refinement that passed independent analytic model review. It is not a Lean formalization, human peer review, a priority claim, or a result about a different projection-body invariant. The cone-law identity and affine invariance are imported from the pinned source; the classical Cauchy, surface-area, first-variation, and Brunn–Minkowski identities are explicitly identified inputs.

The release basis intentionally omits separate anisotropic and simultaneous-truncation research. No theorem from that material is needed here or endorsed by this release basis.

A focused next target is G_d=O(d), which remains open here. The exact G_d above is asymptotic to 64d^6. The remaining loss lies in Euclidean cap and retention geometry. A relative cap estimate intrinsic to the selected polar simplex could be investigated using the general-norm assignment theorem; such an improvement is not proved here.

## 10. Sources and literature positioning

The exact source bytes and available public commit URLs are recorded in SOURCE_PINS.json. The original sharp manuscript is supplied as sources/sharp-simplex-proof.tex; its verified public reference is https://github.com/mxym/math/blob/e4352dd1a3415ee0dbe3213e13932173d879fe10/notes/sharp-simplex-stability/proof.tex . The pinned sources entry005-v3.md and released-explicit-modulus.md supply the invariant's cone representation, its affine invariance, and the older stability argument. The new argument changes anchor selection and dimension estimates, not the definition of the invariant.

Primary literature inspected on 7 October 2026 includes:

- K. Böröczky, Jr., “The stability of the Rogers–Shephard inequality and of some related inequalities,” https://www.renyi.hu/~carlos/rogerstab.pdf . Theorem 3 concerns |K|^(d−1)|Π*K|, the POLAR projection-body volume, and a Banach–Mazur distance with a selectable simplex. Its stated upper modulus is d^(88d) ε^(1/d). This is a different deficit from e(K); no comparison identifying them has been proved here. Therefore the present refinement is not asserted to improve that theorem.
- K. J. Böröczky and M. Henk, “Cone-volume measure and stability,” https://www.renyi.hu/~carlos/cone-volume-stability.pdf . Its stability setting involves cone-volume concentration and the U-functional, rather than the first absolute determinant difference used here. It does not by itself give a realization theorem for arbitrary centered laws on prescribed polar support points.
- K. J. Böröczky, F. Fodor and D. Hug, “Strengthened inequalities for the mean width and the ℓ-norm,” https://arxiv.org/abs/2001.10706 . It studies different extremal functionals and John/Löwner positioning. It provides context, not an imported estimate for e(K).

A targeted primary-source search did not establish a prior theorem identical to the weighted first-moment assignment theorem or the polynomial constant above. This is not an exhaustive literature search and does not justify a novelty claim.
