# Projection-volume geometry: products, joins, rigidity, equality and spectral amplification

**Latest: [version 5 — unique optimum in the balanced homogeneous simplex recursion](v5/README.md).** Read the [complete proof](v5/paper.md), [proof audit](v5/PROOF_AUDIT.md), [exact logarithm checker](v5/code/check_balanced.py), [recorded replay](v5/results/check_balanced.txt), [dependency manifest](v5/MANIFEST.json), and [focused prior-work comparison](../../comparisons/2026-10-07-balanced-recursion.md).

Version 5 proves an infinite-family spectral classification. For every integer arity \(t\ge2\) and simplex seed dimension \(p\ge1\), iterate
\[
K_{j+1}=(K_j^t)^{*t}.
\]
The asymptotic projection-volume root rate has a **unique** maximum at \((t,p)=(2,5)\). Every competitor is rigorously bounded below \(e^{131/125}<2.8534\), while the binary \(T_5\) orbit retains the certified \(2.8534<\Lambda<2.8535\) rate. The exact checker closes a 342-pair finite core plus both infinite parameter tails using rational logarithm intervals. This does not yet prove optimality over unequal product/join arities or arbitrary recursive trees.

[Version 4](v4/README.md) closes the higher-dimensional equality question left open in v3:
\[
a(K)=\frac12
\]
for a centrally symmetric convex body if and only if, up to an invertible linear map, \(K\) is a Cartesian product of centrally symmetric factors of dimensions one and two. It also proves a fixed-dimensional qualitative Banach--Mazur stability theorem for near equality.

[Version 3](v3/README.md) proves simplex equality for the cone invariant for **all convex bodies**, not just polytopes; a uniform qualitative affine stability statement at the lower endpoint; the sharp centrally symmetric bound \(a\le1/2\); a general random-law determinant comparison with complete lower-equality cases; and an explicit Cartesian-square operation strictly improving every finite-dimensional spectral value. First complete v3 disclosure: [43bb307](https://github.com/mxym/math/commit/43bb307c76ec83d09feb2fe3aa74b2a40e3d2bdc).

[Version 2](v2/README.md) contains the exact product/join calculus, the sharp recursive-class threshold in dimension fourteen and the certified \(2.8534<\Lambda<2.8535\) self-similar family. Its [spectral supplement](v2/ASYMPTOTIC_SPECTRAL_REDUCTION.md) identifies the join-closed asymptotic growth rate as \(e\sup\lambda\). Versions 3--5 do not determine the full recursive-class spectral supremum.

The historical version 1.1 record follows. Its optimum is restricted to products of simplices; the later versions enlarge the questions, not the scope of that old optimum.

**Read:** [PDF](v1.1/paper.pdf) · [complete LaTeX source](v1.1/build/main.tex) · [proof audit](v1.1/PROOF_AUDIT.md) · [exact certificate](v1.1/verification/exact_certificate.json) · [versioned release](https://github.com/mxym/math/releases/tag/density-simplex-20261007-v1.1)

**First public version:** v1.1, 2026-10-07. The version number records revision of a private draft, not an earlier public disclosure. First source commit: `e6c776cae39477baa4e1a03d59a1547417f1a68e`; compiled release snapshot: `e894ed8678052e45ecd9f1714b6a996cfea33cf3`.

**Attribution:** mxym (repository account), prepared with AI assistance. No institutional affiliation, independent referee review, or proof-assistant verification is asserted.

## Version 1.1 result and scope

The exact optimum in every dimension; a two-candidate balanced-partition formula; a sharp period-thirteen recurrence starting at dimension 100; uniqueness of every optimal dimension multiset; and sharp dimension-mass stability with additive constant 112. The optimal repeated block has dimension thirteen. These statements concern products of simplices and their affine images, not all convex bodies. No proof depends on a private transcript.

An [additional model-conducted review](../../reviews/2026-10-07-independent-model-review.md) found no confirmed correctness defect. The [supplementary rate comparison](../../comparisons/2026-10-07-simplex-product-rate-gap.md) quantifies an already stated restriction: known non-simplex blocks beat this exact simplex-product optimum exponentially. It includes a fully derived rational lower bound and an [exact checker](../../verification/2026-10-07-independent-review/check_nonsimplex_gap.py). These supplements are not human peer review or proof-assistant verification and do not alter the version 1.1 theorems.

## Version 1.1 build and replay

From `v1.1/`:

```sh
(cd build && pdflatex -interaction=nonstopmode -halt-on-error main.tex && pdflatex -interaction=nonstopmode -halt-on-error main.tex)
cp build/main.pdf paper.pdf
python3 verification/verify_exact.py --limit 300 --output verification/exact_certificate.json
```

LaTeX packages: amsmath, amsthm, lmodern, microtype, geometry, hyperref, booktabs and needspace. The standard-library Python verifier uses arbitrary-precision integers and Fraction, never floating-point inequalities or external solvers. The [recorded run](v1.1/verification/run.txt) checks seven strict rational comparisons, eighty finite no-tie cases, and every optimal dimension multiset by independent exhaustive dynamic programming through dimension 300. Explicit exceptions remain active under Python's optimization flag. Infinite-dimensional conclusions also require the analytic proof in the paper.

## Version 1.1 provenance and citation

The product identity, simplex value, and dimension-twenty example are credited to OpenAI, *A product counterexample to the simplex maximum for projection-body volume*, September 24, 2026, family 088, pinned snapshot `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, and rederived in the manuscript. The upstream paper already reports earlier unrestricted counterexamples in all dimensions at least nine. We claim neither the first disproof of Brannen's conjecture nor an unrestricted maximizer. Upstream rights and notices remain applicable; see the root NOTICE and retained Apache-2.0 license. A [post-publication comparison](../../comparisons/2026-10-07-density-simplex.md) records overlaps and limitations without asserting priority.

```bibtex
@misc{mxym2026simplexproducts,
  author = {mxym},
  title = {Exact projection-volume optimization over Cartesian products of simplices},
  year = {2026},
  note = {Research manuscript, version 1.1; AI-assisted; not peer reviewed},
  howpublished = {\url{https://github.com/mxym/math/tree/e894ed8678052e45ecd9f1714b6a996cfea33cf3/preprints/005-simplex-product-optimum}}
}
```

Public disclosure does not certify first discovery. Historical manifests should be checked at their fixed publication commit, because navigation files can subsequently evolve.

## Additive effective-rigidity supplement

The [complete supplement and evidence](../../notes/quantitative-projection-simplex-stability/README.md), [nine-page PDF](../../notes/quantitative-projection-simplex-stability/paper.pdf), and [source archive](../../notes/quantitative-projection-simplex-stability/source.zip) quantify the lower-end simplex-rigidity theorem with explicit dimension-dependent constants for every maximum-volume inscribed simplex. This is separate from v4’s symmetric upper-end equality class. The planar Banach–Mazur comparison credits the stronger existing linear bound. Versions 2–5 are preserved unchanged by this additive release. The [independent v4 review](../../reviews/2026-10-07-symmetric-projection-equality-review.md) found no substantive correction required.

## Additive symmetric upper-end stability supplement

The [complete upper-end supplement](../../notes/quantitative-symmetric-projection-stability/README.md), [11-page PDF](../../notes/quantitative-symmetric-projection-stability/paper.pdf), [Markdown proof](../../notes/quantitative-symmetric-projection-stability/paper.md), and [editable source archive](../../notes/quantitative-symmetric-projection-stability/source.zip) give an explicit dimension-dependent power modulus for v4's entire symmetric equality class. For every centrally symmetric full-dimensional body and d >= 3, D(K,E_d) - 1 <= d^15 (1/2 - a(K))^(1/(6d)). No smoothness or discreteness assumption is imposed. Corner-truncated cubes give distance at least t/(5d²) from the entire equality class with deficit of order t^d, excluding powers above 1/d and any positive dimension-independent power. The best exponent between 1/(6d) and 1/d remains open.

The [dependency map](../../notes/quantitative-symmetric-projection-stability/DEPENDENCIES.md) pins the v2--v4 inputs; this result neither imports the lower-end simplex modulus nor changes the v5 spectral theorem. The [two mathematical audit scopes](../../notes/quantitative-symmetric-projection-stability/AUDIT.md) and [portable exact-check instructions](../../notes/quantitative-symmetric-projection-stability/VERIFICATION.md) distinguish the written general theorem from finite regressions. No formal verification, external peer review or novelty certification is asserted.

## Additive mixed Bellman upper envelope

The [complete mixed Bellman supplement](../../notes/mixed-bellman-product-join/README.md), [11-page PDF](../../notes/mixed-bellman-product-join/paper.pdf), [English proof](../../notes/mixed-bellman-product-join/proof.md), and [editable source archive](../../notes/mixed-bellman-product-join/source.zip) prove Gamma_C <= exp(1049/1000) < 2.855. The class C permits finite products and joins from a point and affine isomorphisms on affine hulls. Rank-dropping affine maps are excluded. The mixed quadratic/quartic potential is certified on all 19,900 finite state rectangles, all 15,568 small-factor tail intervals and an overlapping analytic large-dimension region.

The theorem improves the actual public quadratic constant (11/85) log(189/128), not merely a rounded decimal. The mixed numerical direction was already public. The known lower endpoint 2.8534 remains inherited, and the complete recursive-class optimum is unresolved. The [precise dependency map](../../notes/mixed-bellman-product-join/DEPENDENCIES.md) and [separate independent checker and full audit](../../verification/2026-10-07-mixed-bellman-independent-audit/README.md) distinguish the new upper proof, inherited spectral passage and candidate-supplied component audit. This is not an upper theorem for all convex bodies.

## Additive lower-end truncation obstruction

The [simplex-truncation supplement](../../notes/simplex-truncation-stability/README.md), [eight-page PDF](../../notes/simplex-truncation-stability/proof.pdf), [TeX proof](../../notes/simplex-truncation-stability/proof.tex), and [editable source archive](../../notes/simplex-truncation-stability/source.zip) compute the projection-cone invariant and maximum inscribed simplices of a vertex-truncated simplex exactly. In every fixed dimension d >= 3, they exclude stability powers above 1/(d-1) for affine Banach–Mazur distance to the entire simplex class and for centroid containment with the best or every maximum simplex. The note gives exact asymmetry and a three-dimensional Rogers–Shephard deficit calculation.

This is a sharpness obstruction, not a universal endpoint upper estimate or a claim of the exact unrestricted Banach–Mazur distance of the examples. Combined with the previously released explicit modulus, it leaves an interval for the unknown optimal exponent. Its [mathematical audit](../../notes/simplex-truncation-stability/INDEPENDENT_AUDIT.md) and [source/verification record](../../notes/simplex-truncation-stability/VERIFICATION.md) are separate from the symmetric upper-end supplement and from any inverse-Minkowski positive extension. The [archival source map](../../verification/STATUS.md#byte-preserved-truncation-reference-copies) identifies the byte-preserved flattened reference copies and their pinned original public layout. Existing numbered versions remain unchanged.
