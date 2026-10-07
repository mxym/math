# Sharp Gaussian Brenier stability under logarithmic second moments

Version **v4**, prepared 7 October 2026. A focused 13-page continuation of manuscript 001.

- [Version 4 PDF](v4/manuscript.pdf), [editable source](v4/manuscript.tex), and [bibliography](v4/references.bib)
- [Source archive](v4/transport_latex_source_v4.zip)
- [Scope and build instructions](v4/README.txt), [build script](v4/build.sh), and [build information](v4/BUILD_INFO.txt)
- [Changes](v4/CHANGELOG.txt), [artifact checks](v4/QA.txt), and [file hashes](v4/SHA256SUMS)
- [Complete broader version 3 PDF](v3/manuscript.pdf) and [source](v3/manuscript.tex)
- Historical [v2 PDF](v2/paper.pdf), [v2 source](v2/manuscript.tex), [v1 PDF](v1/paper.pdf), and [v1 source](v1/manuscript.tex)
- [Verification scope](../../verification/STATUS.md)

## Focused v4 result and explicit public proof dependency

Version 4 proves the exact full-Gaussian logarithmic-second-moment exponent min(1/3, beta/(beta+1)) for beta>0 under the normalization stated in the paper. The transition beta=1/2 has no extra logarithmic loss. At beta=0 there is no uniform modulus in dimension at least two. The matching sharpness assertions require dimension at least two; in dimension one the map distance equals W2.

The positive logarithmic theorem also applies to the specified full-support strongly convex C1,1 source potentials with globally Lipschitz gradient, with explicit constants uniform in the stated fixed parameters. Sharpness is for that source class through its Gaussian member, not for every individual non-Gaussian source. Arbitrary hard-boundary sources are not covered by this logarithmic theorem.

The best Gaussian constant in the homogeneous finite-q one-third estimate has exact order (q−2)^(-1/6) as q decreases to two, in every fixed dimension at least two. The normalized one-dimensional best constant is exactly one.

The new proofs use the complete all-P2 potential theorem from [public v3, Theorem 1.1](https://github.com/mxym/math/blob/5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3/preprints/001-strongly-log-concave-brenier/v3/manuscript.pdf), with [its source](https://github.com/mxym/math/blob/5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3/preprints/001-strongly-log-concave-brenier/v3/manuscript.tex). Version 4 restates that input's exact hypotheses and conclusion as Theorem 2.1; it does not independently re-prove the earlier cell-calculus theorem. This is a public mathematical proof dependency, not a missing local typesetting input.

Version 3 remains the complete record of the broader earlier results: all-P2 potential estimates, compact log-concave sources, hard-boundary target-tail and finite-q estimates, curve lifting, conditional-cell inequalities, and finite-q one-third stability for the specified full-support source classes. Its files, and all v1/v2 files, remain unchanged. The focused v4 paper supplements rather than replaces those proofs.

## Build and status

Run sh build.sh inside v4 using the standard TeX packages listed in README.txt. All local typesetting inputs are supplied, and no installation or network access is performed by the script. Hashes identify the frozen files, not bit-for-bit rebuilds across different times or toolchains.

Research draft, not externally peer reviewed or formally verified. Inherited methods and the public v3 proof input are attributed. Qualitative uniform continuity from compactness is not claimed as new. The HAL comparison remains incomplete; no publication-priority claim is made. Cite the exact version and Git commit used.

## Earlier finite-moment context

The [focused finite-moment literature comparison](../../comparisons/2026-10-07-gaussian-finite-moments.md) concerns the v3 results. The [parallel-work reconciliation](../../comparisons/2026-10-07-modulus-tail-reconciliation.md) distinguishes those results from the separate 007 extensions. Their source-specific qualifications remain in force.
