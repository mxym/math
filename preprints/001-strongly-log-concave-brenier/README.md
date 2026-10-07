# Sharp Brenier stability under target moment bounds

Version **v3**, prepared 7 October 2026. Complete 30-page research proof draft.

- [Complete PDF](v3/manuscript.pdf)
- [Editable LaTeX](v3/manuscript.tex) and [bibliography](v3/references.bib)
- [Source bundle](v3/transport_latex_source_v3.zip)
- [Build instructions and scope](v3/README.txt), [build script](v3/build.sh), and [build information](v3/BUILD_INFO.txt)
- [Mathematical changes](v3/CHANGELOG.txt), [artifact checks](v3/QA.txt), and [file hashes](v3/SHA256SUMS)
- [Verification scope](../../verification/STATUS.md)
- [Finite-moment literature comparison](../../comparisons/2026-10-07-gaussian-finite-moments.md)
- Historical [v2 PDF](v2/paper.pdf), [v2 source](v2/manuscript.tex), [v1 PDF](v1/paper.pdf), and [v1 source](v1/manuscript.tex)
- [Pinned OpenAI source, family 374](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/article.pdf)

## Mathematical scope

Centered-potential estimates cover all finite-second-moment targets for the stated strongly log-concave and compact log-concave source classes. Curve lifting and conditional-cell exponential inequalities remain included.

For the full standard Gaussian, every fixed q>2 moment class has a one-third W2 map-stability exponent, sharp for each fixed Gaussian in dimension at least two. The same positive rate holds for full-support strongly convex C1,1 source potentials with a global gradient-Lipschitz bound. Constants are uniform for fixed dimension, convexity and gradient-Lipschitz parameters, and q. Sharpness for this broader source class follows through its Gaussian member; individual sharpness for every non-Gaussian source is not claimed. These translation estimates exclude hard boundaries.

The general source classes, including hard convex boundaries, have explicit target-tail bounds and a modulus under uniform integrability of second moments. For bounded q-th moments, q>2, the rate is (q−2)/(3q−2), with matching examples for a fixed cube-truncated Gaussian and uniform cube in dimension at least two. A second-moment bound alone gives no uniform map modulus, even on the exact unit-second-moment class for a fixed Gaussian or uniform cube in dimension at least two. In dimension one the map distance equals W2.

## Build and status

Run sh build.sh inside v3 using a standard TeX Live or MiKTeX installation with the packages listed in README.txt. All inputs are supplied; the script neither downloads nor installs dependencies. The supplied PDF hashes identify the frozen artifact, not a bit-for-bit reproducibility promise across toolchains or build times.

Research draft, not externally peer reviewed or formally verified. Inherited methods are attributed. Qualitative continuity from compactness is not claimed as new. Full-text comparison with Mérigot's HAL preprint remains incomplete, and publication priority is not certified. Cite the exact version and Git commit used. Earlier versions retain their original titles and bytes.
