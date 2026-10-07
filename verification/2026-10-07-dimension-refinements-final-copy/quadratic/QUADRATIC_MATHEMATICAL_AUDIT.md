# Final-copy mathematical audit

Date: 7 October 2026. Verdict: **PASS; no mathematical or mathematical-reference correction required.**

Audited release: `quadratic-dimensional-simplex-stability/source.zip`, SHA-256 `d79b07df28ad259f6f02c396335a69a9a3bff98b0a98dfd17d89e5199d4b980d` (342,836 bytes).

Frozen basis archive: SHA-256 `e4692f094731baa994ae10a2d81bc0b50334ed65bb5e5f676c3e48d5b21fe978`. Its 33 manifested payload records were checked against the actual frozen files. The original theorem, intrinsic conversion, relative-cap proof, independent audit, and original audit source manifest agree byte-for-byte with that basis.

This review independently checked the written reasoning, hypotheses, coefficients, branches, imported mathematical inputs, original/public fidelity records, and relevant references against the actual earlier polynomial-dimensional public supplement. It is an analytic model audit, not human peer review, formal proof-assistant verification, or novelty certification. Finite arithmetic checks are supplemental and are not the justification for the unrestricted theorem.

## 1. Exact result and scope

`QUADRATIC_DIMENSION_THEOREM.md`, lines 7–22 and 48–85, establishes the stated result with precisely

    G_d = 16(d+1)^2 [3d^2(d+1)^3(d+2)]^(1/(d−1)) ≤ 4096 d^2,
    G_d ~ 16 d^2.

The quantifiers are every integer d≥3, every full-dimensional convex body K, and every prescribed maximum-volume inscribed simplex S. The homothety uses the original centroid of that same S. The invariant remains the projection-body/pyramid invariant, with E the excess over dilation factor one. No polar-projection invariant, selected favorable maximum, or different centering is substituted.

A maximum S exists by compactness and has positive volume. Its centroid is an interior point of K. Replacement maximality gives |α_i(x)|≤1, the universal E(K,S)≤d+1, and, after translation by that centroid, −K⊂dS⊂dK. Relabeling S's vertices later changes neither S nor its centroid.

## 2. Imported first-moment theorem and actual cone law

The complete proof in `imports/weighted_anchors.md`, Sections 1–5, is valid for every bounded centered probability law with full-dimensional affine support, in any fixed norm. In particular:

- A and B are first absolute determinant moments; V is the unnormalized lifted determinant.
- Centering gives D=B−A=2 E min(P,N)≥0, including singular base tuples.
- The n(n+1)/2 witnesses have total expected cost at most n(n+1)D/2.
- The probability tilt is V/B, with E_tilt(H/V)=E[H 1_{V>0}]/B. Singular tuples are not incorrectly assigned a ratio or assumed to have zero witness cost.
- The diameter-capped pointwise inequality controls large negative barycentric coordinates, and the largest-coordinate assignment with deterministic tie breaking is measurable.
- Existence of a qualifying nonsingular support tuple uses an integrable tilted expectation, not an unproved compact minimum near degeneracy. The zero-defect case is included.

`imports/POLYNOMIAL_REFINEMENT.md`, Section 3, and `sources/entry005-v3.md`, Section 4, supply the actual cone law and its exact identity. At the chosen interior origin the pushforward of h_K(u)dS_K(u)/(d|K|) under u↦u/h_K(u) is centered, compactly supported on ∂K°, and full-dimensional. Centering upgrades linear span to affine span. The boundary identity h_K(X)=1 holds on the closed support by continuity. The representation a=B/[(d+1)A] yields

    D/B = (d+1)e/[1+(d+1)e],   e≥0.

The polytope factorial factors and the passage to arbitrary convex bodies in Proposition 4.1 are correctly normalized. Abstract-law stress tests are not used as convex-body examples. The cited classical surface-area, Cauchy, mixed-volume, and Minkowski identities are appropriate for arbitrary convex bodies, with no smoothness assumption.

## 3. Intrinsic conversion

`INTRINSIC_NORM_CONVERSION.md`, lines 9–108, passes throughout.

For Q=K−K, N=h_Q has unit ball Q° and dual norm p_Q. Maximum-simplex asymmetry gives N(X)≤n=d+1, hence support diameter at most 2n. The anchor coefficient is exactly

    (2n) [n(n+1)/2] [ne/(1+ne)] = n^3(n+1)e/(1+ne).

Fiber integration bounds the length of each chord in direction v by the radial function ρ_Q(v), yielding π_K(u)/|K|≥p_Q(u). This is a radial-length statement, not an unsupported replacement of radial length by width. Cauchy's formula gives E(u·X)_+≥p_Q(u)/d, so the assigned anchors contain (1/d−h)Q°. When h<1/(2d), their polar is a genuine enclosing simplex with K⊂P⊂2dQ and h_P(w_i)=1.

The anchor barycentric identity α_i(x)=λ_i(1−q_i·x) gives the multiplicative comparison p_i≥(1−r)λ_i, r=2dh<1. Thus

    [π_P/|P|]/[π_K/|K|] ≤ (1+r/4)/(1−r).

The mixed-volume excess is z=V(K[d−1],P)/|K|−1, with 0≤z≤r. Minkowski's inequality has the correct direction and gives |P|/|K|≤(1+r)^d. Therefore

    1−π_K/π_P ≤ (d+5/4)r = 2d(d+5/4)h ≤ 3d²h.

The last inequality holds for all d≥3. The deficit is relative to the unnormalized projection volume π_P, as the cap proof requires. With C=n³(n+1), H=3d²C and e≤1/H, h≤1/(3d²)<1/(2d); every strict gate remains strict at e=1/H.

## 4. Relative caps and every-maximum retention

`intrinsic_caps/INTRINSIC_GEOMETRIC_BRIDGE.md`, lines 7–128, passes, including the closed local endpoint.

The projection direction parallel to the opposite facet makes its barycentric coordinate constant on projection fibers. The projected body is a pyramid, even if its projected base is not a simplex. The missing apex cap has exactly fraction t^(d−1) of its projection volume. Consequently each vertex has a point k_i∈K with λ_i(k_i)≥1−ρ, where ρ=δ^(1/(d−1)).

For ρ≤1/(16n), the nonnegative stochastic comparison matrix Q satisfies det Q≥1−2nρ≥7/8. For the arbitrarily prescribed maximum S, its stochastic vertex matrix W therefore has |det W|≥1−η with η=2nρ≤1/8. Hadamard's inequality and the permanent collision bound force the dominant entries into distinct rows. The collision contradiction remains strict at η=1/8.

After relabeling, ||W−I||₁≤8nρ≤1/2. Column sums, inversion, and the zero-sum half-column estimate give

    β=max |(W⁻¹−I)_ij| ≤ 4nρ/(1−8nρ) ≤ 1/2.

For r_i=1−W_ii, (W⁻¹W)_ii=1 yields B_ii−1≥(1−β)r_i/(1−r_i)≥r_i/2. Replacement maximality applied to the same S and k_i gives |(BQ)_ii|≤1 and B_ii−1≤2ρ. Hence every r_i≤4ρ. A second inversion bounds every negative entry of B by 8ρ. The exact barycentric description of centroid dilation gives P⊂z_S+[1+8nρ](S−z_S).

For larger ρ, E≤n<16n²ρ. Together these prove the uniform coefficient 16n². The optional general support-width cap in Section 7 is also correct under the inherited full-dimensional compact-convex hypotheses. Affine invariance of the relative projection supremum is valid; the main proof does not require it.

## 5. Assembly, zero, endpoints, and sharpness

The conversion branch is 0≤e≤1/H, and its strict anchor gate is valid at the closed endpoint. The geometric branch is ρ≤1/(16n), also including its endpoint, independently of the conversion branch. No proof step incorrectly forces the conversion into the much smaller local geometric regime.

For e≤1/H, the uniform bridge gives E≤16n²H^(1/(d−1))e^(1/(d−1)). For e>1/H, the universal E≤n is dominated by that same coefficient. At e=0, the first-moment selection has h=0, relative deficits vanish, the cap points are exactly P's vertices, K=P, and every maximum S equals P up to relabeling. Thus E=0 without taking a limit or choosing a different maximum.

The dimension bound is analytic for every d≥3: C<4d⁴, H<12d⁶ and d≤3^((d−1)/2) imply H^(1/(d−1))≤54√3. Consequently G_d≤1536√3 d²<4096d². Also log H=6log d+O(1), yielding G_d=16d²[1+O(log d/d)].

The actual family in `sources/truncation-proof.tex` has e(K_t)~[d(d−1)/(d+1)²]t^(d−1), and the prescribed maximum with p=e_1 has E=(d+1)t. Its facet computation, maximum-simplex classification, and barycentric excess calculation support the sharp exponent. The argument does not incorrectly assert that all its maximum simplices have the same excess.

The actual square-pyramid body in `imports/SQUARE_PYRAMID_LOWER_BOUND.md` has a=1/d, e=1/[d(d+1)], and E=d+1 at the displayed maximum simplex. Its direct facet certificate establishes the asymptotically linear lower obstruction. Neither that construction nor the local coefficient establishes a uniform linear upper bound. The separately scoped new construction and open-route work were excluded from this review and are unnecessary to the retained theorem.

## 6. Public-copy fidelity and reference audit

All seven derivative files were reconstructed from their actual originals by replaying the **36 ordered ledger edits**. Each removed fragment hash and byte count, each replacement hash, each declared line number, and the resulting complete public bytes matched. All **64 line-segment records** were independently checked on both the original and public files, with contiguous complete coverage. Every segment marked unchanged is byte-identical. No mathematical equation, hypothesis, gate, or conclusion was silently altered.

All 18 files classified as unchanged match their actual frozen or existing public-source counterparts. All 13 current source-pin records match the included bytes. The 11 original-audit records map correctly to the original and public hashes without conflating them. The four historical source-pin records resolve from the release root as documented. Every archive entry matches its staged file.

The actual `polynomial-dimensional-simplex-stability` sibling was read directly from its current staged bytes (source archive SHA-256 `4fc6de94915be740c03f48e4b437b5481c3dbcddef946c86aaee78494264820a`), without relying on a transport handoff inventory. It confirms the d^6 theorem, invariant, sharp exponent, every-maximum quantifier, centroid convention, and imported statements. In the copied polynomial proof, the only changes are removing the contextual word “user's” and relocating source links. The weighted-anchor changes are link/context changes only. The square-pyramid proof and all four shared historical mathematical sources are byte-identical. The cited cone-law Section 3 and v3 Section 4 are correct; Section 2 of the polynomial proof is its normalization section.

All **41 relative file links outside the historical-source copies resolve**. The unchanged v3 source retains its two original `../v2/` repository-context references. Their unbundled status is explicitly disclosed in `SOURCE_GUIDE.md`; the exact commit pin preserves their original context. They do not represent broken new-proof links or silently promised bundled files. The mathematical dependency boundary is the expressly identified prior cone-law theorem and classical geometric inputs.

## Required changes

**None.** The final public copy preserves the audited theorem and proof and accurately distinguishes original, derived, imported, historical, and excluded material. No source file was modified during this review.
