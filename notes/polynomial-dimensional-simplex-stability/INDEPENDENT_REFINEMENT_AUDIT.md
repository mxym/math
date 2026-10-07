# Independent analytic audit of the polynomial refinement

Date: 7 October 2026.

Public derivative of the independent analytic model audit. Source locators have been mapped to the exact local public-source copies, and discussion of a broader construction class outside this supplement has been omitted. The upper-bound analysis in Sections 1–7 and the square-pyramid calculation in Section 8 are unchanged. See SANITIZATION_LEDGER.json for the source hash and each editorial operation.

## Verdict

**No substantive mathematical gap was found in Sections 1–8 of `POLYNOMIAL_REFINEMENT.md`.** The written argument establishes, using its stated classical convex-geometric inputs and the supplied invariant identity, the following theorem:

For every integer d ≥ 3, every full-dimensional convex body K in R^d, and every prescribed maximum-volume inscribed simplex S,

E(K,S) ≤ G_d e(K)^(1/(d−1)) ≤ 2^20 d^6 e(K)^(1/(d−1)).

The exact G_d and e_0 displayed in the refinement are consistent with the local estimate G_d/2 and the global threshold calculation. The argument retains the originally prescribed simplex and its original centroid. Its probability-law strengthening is genuinely independent of convex-body realizability; the later geometric conversion explicitly uses properties of actual cone laws.

I also independently checked the newly added square-based iterated-pyramid example. It gives the stronger realized lower bound

G_d ≥ (d+1)[d(d+1)]^(1/(d−1)).

This is an analytic model audit, not human peer review or proof-assistant verification. No priority or literature-completeness conclusion is established by this audit.

## Material examined and scope

Primary target:

- `POLYNOMIAL_REFINEMENT.md`, Sections 1–8 in full and its sharpness/lower-bound conclusions
- `weighted_anchors.md`, especially the exact witness identities and the singular-anchor issue
- The square-pyramid construction, reproduced in `SQUARE_PYRAMID_LOWER_BOUND.md`; the broader construction-class discussion is outside this supplement

Imported reference checked:

- [sources/sharp-simplex-proof.tex](sources/sharp-simplex-proof.tex)
- The pinned [sources/entry005-v3.md](sources/entry005-v3.md), Section 4, including the d! and (d+1)! determinant factors and arbitrary-body passage
- [sources/entry005-v2.md](sources/entry005-v2.md), Sections 2–5, including the facet normalization, pyramid formula, affine invariance, and continuity passage

The original `proof.tex` was read only. Its SHA-256 is

9361999cfa4337500041da4b3fc824cd3676a07a22ffad0274e38346bf301b98.

The audit made no changes to the source proofs. Its independent regression script and recorded output are included below. Separate anisotropic and simultaneous-truncation research is not part of this supplement and is not a dependency of the polynomial theorem.

## 1. The determinant-weighted selection is valid

Let μ = ν^(d+1), V be the absolute lifted determinant, and H the integrated nonnegative sum of N = (d+1)(d+2)/2 witnesses.

The cancellation identity is exact. Conditional on the d-point base, affinity and centering give |E F(X)| = |det(X_1,…,X_d)|. Subtracting this from E|F(X)| and averaging yields D = 2 E min(P,N_−). The witness expectation is bounded by D because each of its two minima has expectation at most min(P,N_−). Singular bases cause no failure.

Each summand defining H has precisely the same d+2-independent-sample distribution before conditioning, even when the integrated point is placed inside the base. Consequently E_μ H ≤ ND. The number of summands is correct: (d+1) + binomial(d+1,2) = N.

Full-dimensional support and centering imply A > 0 and B = E_μ V > 0. For B, an affinely independent support tuple has an open product neighborhood of positive μ-measure on which V > 0.

The selected probability law is μ_V = (V/B)μ. Under this law,

E_μV(H/V) = E_μ[H 1_{V>0}]/B ≤ ND/B.

**The restriction indicator is essential and is present in the proof.** H need not vanish on singular tuples. There is no substitution of E(H/V) by E(H)/E(V), and no inverse-determinant integrability assumption under μ. The ratio is integrable under μ_V by the displayed calculation.

Existence of a tuple with ratio at most the stated bound follows from elementary integration: if the ratio exceeded the bound almost surely, its expectation would exceed the bound. This argument handles nonatomic measures and does not require a minimum on the open set V > 0. If D = 0, H/V = 0 almost surely under μ_V, so the zero-defect endpoint is also covered.

## 2. The clipped barycentric estimate closes the suspected gap

For fixed nonsingular anchors, the first witness is exactly V min(1,(−α_i)_+). A pair witness is exactly

V [min((α_i)_+,(α_j)_+) + min((−α_i)_+,(−α_j)_+)].

The pair identity follows by determinant multilinearity: up to a common sign, its two tested determinants are V α_j and −V α_i. It is valid for all signs of the barycentric coordinates. Discarding its negative-negative contribution preserves a lower bound.

Let r maximize α_i, with deterministic ties. Its coefficient is positive because the coefficients sum to one. The pairs containing r sum to U = Σ_(i≠r)(α_i)_+. With N_x = Σ_i(−α_i)_+, the affine identity implies

||x−w_r|| ≤ diameter(supp ν)(N_x+U).

Separately, x and w_r both belong to the support, so their distance is at most its diameter. Thus the left side is bounded by diameter times min(1,N_x+U).

There are two equivalent valid ways to finish:

- If some α_i ≤ −1, a clipped witness contributes one and pays for the entire support-diameter bound.
- Otherwise every negative term is unclipped, and N_x+U is bounded by the displayed witness sum φ.

This is why large negative barycentric coordinates do not cause a condition-number loss. Integrating and then using μ_V selection proves h ≤ diameter·N·D/B. The argument works in every fixed norm. Borel measurability follows because the α_i are continuous affine functions and the tie-breaking rule is fixed.

Small mean transportation error does not, by itself, control support Hausdorff distance. The refinement does not make that invalid inference.

## 3. Normalization and the actual cone-law dispersion

### Prescribed maximum simplex

Fixing the prescribed S and mapping it to a regular inradius-one simplex Δ gives |α_i(x)| ≤ 1 for every x in K by vertex replacement. For its vertices, ||v_i||² = d² and v_i·v_j = −d when i ≠ j. Therefore

||x||² = d[(d+1)Σ_i α_i²−1] ≤ d[(d+1)²−1] = d²(d+2).

Hence R = d√(d+2) is valid. This estimate uses the Gram matrix; it does not silently discard the barycentric sum condition. Inradius one gives B_2^d ⊂ Δ ⊂ K.

Centroid dilation is equivalent to α_i ≥ −t/(d+1). The same vertex-replacement bound therefore gives E(K,Δ) ≤ d+1 globally. This is valid for every maximum simplex.

### Cone law and correct factors

The pushforward measure is a centered probability by ∫h_K dS_K = d|K| and ∫u dS_K = 0. It is supported on ∂K° ⊂ B_2^d. The radial image is compact, so support points selected by the weighted theorem still satisfy h_K(w_i) = 1. Cauchy's projection formula shows full span.

The supplied determinant identity gives

D/B = (d+1)e/[1+(d+1)e].

With diameter at most two, the abstract theorem becomes h ≤ C e/[1+(d+1)e], where C = (d+1)²(d+2). Both the denominator and the extra factor d+1 are correct.

Cauchy's formula gives E|u·X| = 2π_K(u)/(d|K|). Centering therefore gives E(u·X)_+ = π_K(u)/(d|K|), with no missing factor two.

Fubini along fibers parallel to u gives |K| ≤ w_K(u)π_K(u) because each fiber length is at most the directional width. Since w_K(u) ≤ 2R,

E(u·X)_+ ≥ 1/(2dR) = 2/M, where M = 4dR.

This argument is specifically about an actual convex body. Bounded support of an arbitrary centered law would not imply this bound.

If h ≤ 1/M, Lipschitz comparison with the assigned law yields a positive-part moment at least 1/M in every direction. Some anchor has scalar product at least 1/M in that direction, so support functions give M^−1 B_2^d ⊂ T. Polarizing yields the genuine enclosing simplex B_2^d ⊂ K ⊂ P ⊂ M B_2^d.

## 4. Assignment, scale, and absolute projection deficits

For the polar simplex, the law ν_P = Σ_i λ_i δ_(w_i) is correct: the polar images of its facet normals are exactly w_i, and its centered probability weights are uniquely the barycentric coordinates of zero in T.

The exact affine-coordinate formula α_i(x) = λ_i(1−q_i·x) has the right orientation. Indeed q_i·w_j = 1 for j ≠ i, while centering yields q_i·w_i = 1−1/λ_i. Substituting c = Σ_i p_i w_i gives

p_i−λ_i = −λ_i q_i·c, and Σ_i|p_i−λ_i| ≤ Mh.

Since ||c|| ≤ h and the anchors have norm at most one, the two transportation/weight comparisons give the claimed normalized-projection error (d/2)(1+M)h.

The integrand h_P(x)−1 is nonnegative on the cone-law support because K ⊂ P and h_K(x) = 1 there. It is at most M times distance to an assigned anchor because h_P(w_i) = 1 and P ⊂ M B_2^d. Homogeneity cancels h_K in the cone-law integral, proving

z = V(K[d−1],P)/|K|−1, with 0 ≤ z ≤ Mh ≤ 1.

Minkowski's first inequality has the required direction: |P|/|K| ≤ (1+z)^d. The mean-value bound on [0,1] gives (1+z)^d−1 ≤ d2^(d−1)z. Finally π_P/|P| ≤ d/2 follows from ν_P being supported in the unit ball.

Combining these inequalities and |K| ≤ (2R)^d gives precisely

J = (d/2)(2R)^d[1+M+d2^(d−1)M].

Nonnegativity of the absolute projection deficits comes from K ⊂ P, not from the signed normalized-projection estimate.

## 5. The improved projection cap is not circular

For a farthest q in P and nearest k in K, compactness gives existence and convex nearest-point optimality gives n·k = h_K(n), with n = (q−k)/s. Because k belongs to K ⊂ R B_2^d,

||q|| ≤ ||k||+s ≤ R+s.

Choose u perpendicular to n. In the m = d−1 dimensional projection, the ball (1−τ)q̄+τB_2^m lies in the projection of P by convexity, with τ = s/[2(R+s+1)]. Its lowest n-coordinate is at least h_K(n)+s/2, so it is disjoint from the projection of K. The inscribed cube of side 2τ/√m is valid: its vertices have norm τ.

Thus ε ≥ [s/(√m(R+s+1))]^m. Setting t = √m ε^(1/m) gives s ≤ t(R+s+1); for t ≤ 1/2 this implies s ≤ 2t(R+1).

No prior bound P ⊂ (R+1)B is used. That improved radius is deduced only after the cap and local gate give s ≤ 1/(8d). Consequently there is no circular replacement of M by R+1. The cap also handles ε = 0, when a positive s would contradict its volume lower bound.

## 6. Local gate, matching, and the original centroid

The stated e_0 gives h ≤ Ce ≤ [J(8dL)^m]^−1 ≤ 1/M because J ≥ M and 8dL ≥ 1. Thus all preceding estimates are available.

Writing y = (JCe)^(1/m), the gate gives y ≤ 1/(8dL) and √m y ≤ 1/[16d(R+1)] ≤ 1/2. The cap gives s ≤ Ly ≤ 1/(8d). Only now is P ⊂ (R+1)B_2^d deduced.

From h_K ≥ h_P−s and h_P ≥ 1 follows h_K ≥ (1−s)h_P, so (1−s)P is an inscribed simplex. Its volume is bounded by that of the originally fixed maximum Δ. Hence |Δ|/|P| ≥ (1−s)^d ≥ 1−ds.

For δ = ds ≤ 1/8, the nonnegative column-stochastic coordinate matrix W has |det W| ≥ 1−δ. Each column has Euclidean norm at most one, so Hadamard gives norm at least 1−δ individually. Its largest entry is at least its squared norm, hence at least 1−2δ.

Two such entries cannot occupy the same row. The permanent is the probability that independent row choices from the columns are all distinct; a repeated dominant row would imply

|det W| ≤ per(W) ≤ 1−(1−2δ)² ≤ 4δ < 1−δ.

The resulting bijective vertex matching has error at most 2δ diam(P) ≤ 4(R+1)ds. Convex combinations and B_2^d ⊂ Δ give P ⊂ [1+4(R+1)ds]Δ. Therefore the local coefficient is exactly G_d/2.

The proof includes e = 0: h = 0, projection deficits vanish, s = 0, and the matrix matching gives Δ = P = K.

Finally, G_d e_0^(1/m) = R+1 ≥ d+1. The global maximality estimate therefore covers e > e_0 with coefficient G_d. All affine changes were made using the initially prescribed S; affine maps preserve centroids and intertwine centroid homotheties. The helper simplex P does not replace S in the final metric.

## 7. Universal polynomial estimate

I rederived the arithmetic independently. For d ≥ 3,

C ≤ 3d³, J ≤ d²M(4R)^d, R+1 ≤ 2R, and L ≤ 4√d R.

Starting with the exact G_d gives

G_d ≤ 64d^(3/2)R²[3d^5M(4R)^d]^(1/(d−1))
    = 256d^(3/2)R³[12d^5MR]^(1/(d−1))
    = 256d^(3/2)R³[48d^6R²]^(1/(d−1)).

Since R² ≤ (5/3)d³, this is at most

256(5/3)^(3/2)d^6[80d^9]^(1/(d−1)).

The induction d ≤ 3^((d−1)/2) starts at equality for d = 3 and uses (d+1)/d ≤ 4/3 < √3. It gives [80d^9]^(1/(d−1)) ≤ √80·3^(9/2) < 1280. Also (5/3)^(3/2) < 9/4. Thus

G_d < 576·1280 d^6 = 737280 d^6 < 2^20 d^6.

No finite numerical check is needed for this universal bound. The inequalities deliberately leave slack and do not claim d^6 is optimal.

## 8. Independent verification of the stronger realized lower bound

Set C_d = conv(0,e_1,e_2,e_1+e_2,e_3,…,e_d) and S_d = conv(0,e_1,…,e_d).

A full-dimensional vertex simplex must include every e_i for i ≥ 3, since it is the only vertex with a nonzero ith coordinate. The remaining three vertices are a triangle in the square, with determinant magnitude one. Separate affinity and the triangle inequality then bound arbitrary inscribed-simplex determinants by the same maximum. Hence S_d is maximum and |S_d| = 1/d!.

The omitted square vertex has barycentrics (−1,1,1,0,…,0), so E(C_d,S_d) ≥ d+1. The global maximality bound proves equality.

The square has a = 1/2 and each pyramid adds one to 1/a, giving a(C_d) = 1/d. I also checked the direct facet certificate independently of this recursion. With c = 1/(d−1)!, the claimed area-normal/support vectors are correct. The volume is 2/d!. Their horizontal minors sum to c^d d2^(d−1), and their lifted minors sum to c^(d+1)2^d. Therefore a = L/[d|C_d|H] = 1/d and e = 1/[d(d+1)].

It follows that every possible universal coefficient must satisfy

G_d ≥ (d+1)[d(d+1)]^(1/(d−1)).

Its (d−1)st-power ratio to the small-truncation lower bound is d²(d−1)/(d+1) > 1 for d ≥ 3. Its asymptotic form d+1+2 log d+O((log d)²/d) is correct. It strengthens the constant but not the linear order of the obstruction.

[Editorial omission: the broader construction-class discussion is outside the scope of this supplement.]

## 9. Independent regressions and remaining qualifications

New files:

- `check_independent_refinement_audit.py`
- `verification/check_independent_refinement_audit.log`

The script imports no producer or inherited checking code. It uses exact rational determinants to test:

- asymmetric centered laws, equality laws with rare atoms, a nearly flat law with singular tuples of positive H, and simplex-plus-origin laws in dimensions 1–4;
- the exact pair-witness identity, clipped metric bound, weighted mass normalization, weighted ratio integral, and selected h bound;
- the direct square-pyramid facet sums in dimensions 3–12.

It separately checks the constants and local/global gate in log arithmetic for every integer d from 3 through 10000. All tests passed. The largest tested G_d/d^6 was approximately 96394.6502644 at d = 3; this is only a finite diagnostic, not a claim about the exact global maximum.

The finite law tests expressly exhibit a positive singular contribution E[H 1_{V=0}], confirming why the selection proof's indicator cannot be omitted. Near-singular anchors and zero defect were both covered.

Remaining qualifications are about scope, not an identified gap:

1. The arbitrary-body cone-law identity and the classical surface-area, Cauchy, first-variation, and Brunn–Minkowski facts remain identified inputs. Their required normalizations and directions were checked against the supplied sources.
2. The result is not a Lean formalization and has not been independently human-refereed by this audit.
3. The polynomial constant is nonoptimal. The gap between its d^6 upper order and the realized linear lower order remains open here.
4. Literature priority and claims about different projection-body deficits require a separate literature comparison; this audit supplies none.
5. The refinement is separate from the earlier sharp-exponent proof, which is preserved unchanged as a pinned source.
