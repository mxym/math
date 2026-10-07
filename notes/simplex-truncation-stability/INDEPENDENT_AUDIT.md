# Independent audit of the simplex truncation obstruction

7 October 2026. Independent AI-assisted review; not human peer review or proof-assistant verification.

## Verdict and limits

No mathematical gap was found in the exact invariant calculation, classification of all maximum simplices, centroid excesses, translated homothets, unrestricted simplex-distance bounds, exponent ceiling, necessary constants, Minkowski asymmetry, or dimension-three difference-body calculation. The arguments establish the stated all-dimensional conclusions independently of the finite regression tests.

The received self-audit was treated as a list of claims to check, not as evidence of correctness. The public v2–v3 facet identity was read independently at repository commit 3360e7191cf564a46d09edcbfbd107c9178bd98f. The archived source snapshots were verified against their own pinned commits and against that checked repository commit.

The lower endpoint of the interval of admissible powers uses the separately released quantitative theorem as an input. This audit verifies its statement, normalization, pinned source and applicability; it does not present a new complete independent audit of that entire quantitative theorem. The main obstruction theorem does not depend on that theorem.

No exact formula for the unrestricted Banach–Mazur distance, universal upper bound at exponent 1/(d-1), optimal universal constant, or priority claim is supported or asserted.

## 1. Normalization and determinant calculation

The public convention is a(K) = (d/(d+1))^d R(PK)/R(K) - 1, where R(K) = |Pi K|/|K|^(d-1). Public v2 derives the facet expression and v3 states it in exactly the normalization used here.

For facet area-normal vectors u_i and area-support numbers b_i, write H for the sum of absolute horizontal d-minors and L for the sum of absolute lifted (d+1)-minors. Cauchy's formula and the zonotope volume formula give H = |Pi K|. The pyramid has side area-normal vectors (u_i,b_i)/d and bottom vector -|K|e_(d+1), so its projection-body volume is |K|H/d^d + L/d^(d+1). Substituting its volume |K|/(d+1) yields a(K) = L/(d|K|H), with no omitted factor of 2, d!, or d+1.

For K_t, the coordinate facet area is (1-t^(d-1))/(d-1)!. The top and bottom area-normal vectors and signed supports in (14) are correct. The negative bottom support is harmless: translating an interior point to zero only adds a linear combination of horizontal rows to the lifted support row. No signed support is used as a probability weight.

The horizontal top-and-bottom minors vanish because the two normals are parallel. Their lifted counterparts generally do not vanish and contribute q-t^d = q(1-t), where q=t^(d-1). Including all such minors gives (15)–(16), hence (4). Subtracting 1/(d+1) gives the bracket in (5). Its derivative is negative for every d>=2 and t>0, and its value at t=1 is zero, proving positivity. The limit coefficient is exactly c_d = d(d-1)/(d+1)^2.

## 2. Every maximum simplex, including nonvertex vertices

A nonzero vertex-simplex determinant must use every coordinate ray. With d+1 chosen vertices there is exactly one doubled ray; its determinant has absolute value (1-t)t^k. For 0<t<1, equality with 1-t occurs precisely for all d top vertices and one bottom vertex.

The extension to arbitrary inscribed simplices is valid. Independently sampling the extreme-point representation of each vertex preserves the determinant in expectation by multiaffinity. Equality in the bound forces every positive-probability sampled tuple to be a maximizing vertex tuple. In particular, the sum of the independent bottom-slot indicators equals one almost surely. Its zero variance makes each indicator deterministic. The d top-slot supports must be nonempty and disjoint in a d-element set, hence singletons. Thus all top vertices are fixed and the remaining vertex is any point tp on the bottom face. The converse follows from the fixed height above the top hyperplane.

This proves both M(K_t)=(1-t)/d! and the complete classification S_p=conv(e_1,...,e_d,tp), rather than merely finding a convenient selection of maximizers.

## 3. Containment and distance to all simplices

The barycentric coordinates (19) sum to one and recover x. Their minima on K_t are 0 and -tp_i; the latter are attained at te_j with j!=i. The availability of this vertex is why d>=2 is stipulated. Centroid dilation corresponds to all barycentric coordinates being at least -E/(d+1), giving E(K_t,S_p)=(d+1)t max p_i. Its best and worst maximum-simplex values are respectively (d+1)t/d and (d+1)t.

For any simplex, a translated homothet is described by independent barycentric thresholds whose sum is 1-lambda. Optimizing these thresholds gives lambda=1-sum_i min_K beta_i. Applied to S_p, this is exactly 1+t, with the explicit translate -tp+(1+t)S_p.

The lower Banach–Mazur estimate quantifies over every inscribed simplex S, with arbitrary translation of the outer homothet. Volume monotonicity gives lambda^d >= |K_t|/|S| >= |K_t|/M(K_t) = 1+t+...+t^(d-1). It therefore does not inadvertently restrict the distance to maximum-simplex position. Its first-order lower coefficient is 1/d, and the stated t/(2d) bound is valid for 0<t<1.

## 4. Exponent ceiling and necessary constants

The invariant defect is asymptotic to c_d t^(d-1), while each of the three geometric errors used in the corollary is bounded below by a positive constant times t. Division by t excludes every exponent greater than 1/(d-1), even if a proposed universal estimate is only required for sufficiently small defects.

At the critical exponent, p=e_1 gives the every-maximum necessary constant (d+1)c_d^(-1/(d-1)); uniform p gives the best-maximum necessary constant (d+1)c_d^(-1/(d-1))/d. The unrestricted distance lower limit gives c_d^(-1/(d-1))/d. These are necessary lower bounds, not optimality claims. Since c_d<1, the every-maximum constant exceeds d+1, correctly excluding a dimension-independent constant in that formulation.

In d=3, cancellation yields e(K_t)=t^2(t^2+t+3)/[4(1+t+t^2)(2+t^2)] and c_3=3/8. Both displayed tetrahedral endpoint constants are correct.

## 5. Asymmetry and Rogers–Shephard calculation

For reflected containment, checking all facets gives (r+1)z_i>=1 and 1+rt <= (r+1)sum z_i <= r+t. These inequalities are necessary and sufficient. They force r>=d-t, and z_i=1/(d+1-t) attains that value because (1-t)(d-1-t)>=0. Thus s(K_t)=d-t exactly.

The description of the difference body by P<=1, N<=1 and |P-N|<=1-t follows by writing a=x_++w and b=x_-+w. In dimension three the untruncated difference body has volume 10/3. Each of its two removed caps has volume t/2+t^2+t^3/6, as obtained by integrating the three types of orthants. This gives the stated polynomial difference-body volume and normalized deficit. Its first-order coefficient 3/10, together with c_3=3/8, proves the asserted failures of the two linear defect bridges and the 1/2 ceiling for either proposed power bridge.

## 6. Checker review and completed replay

The checker uses rational arithmetic throughout and explicit exceptions rather than assert statements. Its Gaussian elimination, permutation determinant crosscheck, vertex-subset enumeration, barycentric linear solver, supporting-plane enumeration, projected polygon hull and facet triangulation were reviewed. Dropping a coordinate with nonzero facet-normal component is injective on the supporting plane. The difference body is full dimensional, centrally symmetric and contains zero in its interior, so summing absolute tetrahedron volumes over its boundary triangulation is legitimate.

Both normal and optimized Python modes passed and reproduced the received certificate and logs byte-for-byte. Totals: 1,080 horizontal minors, 300 lifted minors, 5,385 vertex-simplex subsets, 1,760 barycentric checks, 125 Leibniz crosschecks, and five rational 3D hull-volume checks with 70 facets and 160 triangles. The invariant/barycentric grid is d=2..9; full vertex-subset enumeration is d=2..6; the five t-values are 1/100, 1/10, 1/3, 1/2, 9/10.

These regressions do not independently certify the all-dimensional maximum-simplex equality case, an unrestricted Banach–Mazur optimization, asymptotic limits, or any universal stability theorem. Those claims were checked through their written arguments above.

## 7. Source and literature scope

Ten public source snapshots and two literal commit-reference files are recorded in sources/SOURCE_MANIFEST.json. The quantitative supplement's exponent and E convention agree with this note. The v4 and v5 scope descriptions do not alter the lower-end invariant used here.

The literature statements were checked against primary sources:

- [Böröczky, Rogers–Shephard stability](https://www.renyi.hu/~carlos/rogerstab.pdf), Theorems 1 and 3 and Example 19: the linear Rogers–Shephard result, the polar-projection power result, and simplex truncation as an existing obstruction method.
- [Ambrus–Böröczky, random simplices](https://arxiv.org/pdf/1005.5024), sampling definitions and Theorem 5: uniform interior sampling and planar simplex-maximizer stability.
- [Böröczky–Machado–Ramos](https://arxiv.org/html/2603.17726v3), Theorem 1.1: the Hausdorff exponent 1/(d-1) under a quantitative dispersion hypothesis for normalized measures, in dual-convex distance.
- [Brandenberg–González Merino–Grundbacher](https://arxiv.org/html/2607.27041v2), Theorem 1.1: dimension-independent linear-order simplex approximation in the asymmetry gap.

None of those theorem statements supplies the missing scalar-defect-to-measure-distance bridge for the present invariant. Their complete proofs were not re-audited. They are contextual references, not unacknowledged inputs to the exact truncation calculation.

## 8. Document and archive verification

The original archive contained all 19 supplied files with matching bytes and valid ZIP CRCs. All eight original manifest entries matched their byte sizes and SHA256 hashes. Its manifest intentionally covered only principal deliverables; the public-ready package extends coverage to the complete payload, with explicitly stated self-reference exclusions.

The original TeX rebuilt to eight pages with extracted text and all rendered page pixels identical to the supplied PDF. Publication edits are documented in EDITORIAL_CHANGES.md. All mathematical theorem/proof environments remain byte-identical. The final eight-page PDF was rebuilt, its full text re-extracted, and every page visually inspected. No clipping, overlapping formula, missing glyph, unresolved reference or TeX overflow warning was found.

The clean source archive uses the exact PACKAGE_FILES.txt whitelist, excluding itself. Both ordinary and optimized integrity checks, a clean-extraction exact replay, and a clean-extraction PDF/text rebuild are included in the completed verification record. Build products and private working material are excluded. Preparing this package performs no repository push or publication.
