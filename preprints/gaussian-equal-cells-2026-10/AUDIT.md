# Prepublication audit

## Outcome and actual scope

The expanded all-k argument has been checked against its stated hypotheses and published geometric dependency. No blocking mathematical gap was identified in this internal rederivation. This is AI-assisted internal review, not outside human peer review, a journal decision or a complete Lean certificate.

This release contains a signed, standalone seven-page version of the expanded PR #7 manuscript. The theorem, normalization, equality classification and fractional extension are retained. The source review and prior Lean provenance remain available without assigning an earlier review to newly changed bytes.

## Mathematical checks

1. The positive-covariance argument always lives in auxiliary dimension n=k−1. Milman–Neeman Theorem 1.1 is applied exactly at k=n+1 with strictly positive equal masses. The auxiliary winning cells are Borel polyhedra of finite Gaussian perimeter; arbitrary original measurable partitions are not assumed to have finite perimeter.
2. Total perimeter is half the sum of cell perimeters. Interface areas use the ambient Gaussian density, including counting Hausdorff measure for n=1. The inward flux sign gives B=LM and C=tr(LQ), with weights A_ij/ell_ij.
3. Centered prices attain their minimum. Gaussian differentiation in fixed invertible score coordinates gives a smooth objective and probabilities. The positive price Hessian L is invertible on 1-perp; strict convexity and the implicit function theorem give unique smooth balanced prices.
4. A covariance lift M(t)=M(I+tA)^(1/2), together with the vanishing price gradient, gives dC(Q)[D]=tr(LD)/2. The factor one half and the distinction from the interface-area Laplacian are preserved.
5. The regular fan gives C(Q*)=a_k/sqrt(k−1) and S*=C(Q*)sqrt((k−1)/2). The perimeter theorem and weighted Cauchy imply C tr(L)/(k−1) ≥ C(Q*)².
6. Along Q_t=Q*+t(Q−Q*), the differential inequality for h=C²−C(Q*)² is t h'≤h. Symmetry gives C'(0)=0. Thus h/t is nonincreasing from zero. Singular endpoints use continuity only; they do not assume bounded limiting prices or facet weights.
7. Equality at either an interior or singular endpoint forces all interior Cauchy inequalities to be equalities. Every edge weight is positive there, so all pair distances agree and the trace-one centered Gram matrix is Q*. This excludes equality below dimension k−1.
8. For actual moment scores, F≤C(MM^T) follows from the feasible equal-mass assignment for every price. Homogeneity gives F≤c_k sqrt(F), including the F=0 case. The pointwise nonnegative assignment gap gives the fractional equality classification. Regular flux verifies attainment.
9. The nonnegative improper deficit integral is obtained on compact subintervals and then by endpoint continuity and h(t)=O(t²) at zero; no numerical integration is a premise.

## Reference and engineering checks

The three primary arXiv version PDFs were freshly retrieved with TLS verification; their hashes match the prior source-review inventory. The published Milman–Neeman title, authors, volume, issue, pages and DOI were checked via Crossref. Heilman's 2014 journal DOI is `10.1214/ejp.v19-3083`. Original Conjecture 3, Problem 1.15 and Conjecture 1.16 were read directly. The neighboring positive-correlation and arbitrary-mass statements remain explicitly distinguished.

The publication PDF was freshly compiled three times. No unresolved citation/reference, missing character, overfull box or LaTeX warning remains; all fonts are embedded. All seven pages were rendered and visually inspected, including formulas, author block, page boundaries and bibliography. No clipping, overlap or broken citation was found. The original expanded research package passes its own 31-file integrity check and normal/optimized rational-control replay; those controls do not prove Gaussian analysis.

[Build audit](audit/BUILD_AUDIT.json) · [Primary source hashes and partial CI status](audit/REFERENCE_AND_CI_AUDIT.json). The existing review is preserved in the research package. The later source archive and Zenodo checks establish byte identity and accessibility, not a substitute mathematical proof.
