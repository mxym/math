# Vertex excess and the sharp exponent in simplex stability

Complete English manuscript candidate for the Entry 005 continuation, dated 8 October 2026.

## Main result

For integers d >= 3 and r >= 1, a full-dimensional convex d-polytope with at most d+1+r vertices satisfies

E(K,S) <= min{64(d+1)r, 16(d+1)^2} [3d^2(d+1)^3(d+2)]^(1/k) e(K)^(1/k),

where k = min(r,d-1), e is the original projection-body pyramid defect, and S is any prescribed maximum-volume inscribed simplex. The dilation uses that same S's original centroid. The sharp exponent is 1/k, with the exact truncation-and-pyramid limiting constant proved in Section 7.

The coefficient is not claimed optimal. The main theorem is for d >= 3; its r=1 sharpness family uses the explicitly computed m=2 core.

## Read and build

- `vertex_excess_sharp_exponent.pdf`: complete typeset paper
- `main.tex` and `sections/*.tex`: editable manuscript source
- `BUILD.md` and `build.sh`: reproducible TeX build instructions
- `SOURCE_MAP.md` and `INPUT_MANIFEST.json`: exact source correspondence and hashes
- `EDITORIAL_CHANGES.md`: changes from the frozen reviewed draft
- `audit/REFEREE_REPORT.md`: supplied independent traditional model review of the frozen mathematical argument
- `qa/PDF_QA.md`: page-by-page visual and build checks
- `verify_package.py`: exact source hashes and finite rational sanity checks

Run `./build.sh` and `python3 verify_package.py` from this directory. No network access, Lean, or upstream repository checkout is needed to build the paper. Standard TeX packages and Poppler are required; see `BUILD.md`.

## Proof coverage

The paper contains the cone/prismoid proof, ray collapse, facet counting, finite determinant assignment, raw projection-body and pyramid facet identities, finite actual-facet enclosure with all constants, both retention bounds for the originally prescribed maximum, all defect branches, the m=2 calculation, sharp truncation-and-pyramid family, and the maximum-over-all-directions geometric sharpness calculation. Classical mixed-volume facts, Minkowski's first inequality, Cauchy's projection formula, and the zonotope volume formula are credited as standard background.

## Verification and literature boundary

The frozen argument and sharpness family received a PASS in a separate analytic review by an independent model. This is not human professional peer review, journal acceptance, or a new Lean verification. The manuscript is an expanded exposition and has a separate source-fidelity check. Earlier compiled Lean main theorems do not certify the new cone/counting/facet-specialization/exponent result. Exact retained theorem names use the `Entry005` namespace and are listed in the paper and source map.

No first-discovery or priority claim is made. The focused literature comparison is not exhaustive. The package preserves historical source files byte-for-byte; any older “pending review” language in those frozen records describes their creation state. Current status is stated in this README, the manuscript, and the separately identified review.

## Publication scope

This is a local candidate package. No Git commit, push, external publication, or user attachment was made by its preparation step. `RELEASE_FILES.txt` identifies the necessary publication files. Build caches, temporary PDF renders, and scratch output are excluded. The parent publication writer should use that list or the accompanying release archive, and retain the audit boundary above.
