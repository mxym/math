Sharp Brenier stability under target moment bounds
Research draft, version 3, 7 October 2026

Files
  manuscript.pdf    Complete rendered manuscript
  manuscript.tex    Editable LaTeX source
  references.bib    Editable BibTeX bibliography
  manuscript.bbl    Generated bibliography for convenient recompilation
  build.sh          Local build script
  BUILD_INFO.txt    Build environment and reproducibility notes
  CHANGELOG.txt     Mathematical changes from version 2
  QA.txt            Final rendering and compilation checks
  SHA256SUMS        SHA-256 file manifest

Build
  sh build.sh

The script uses latexmk when available, otherwise pdflatex and bibtex. A standard
TeX Live or MiKTeX installation with Latin Modern, AMS packages, microtype,
geometry, enumitem, xcolor, hyperref, cleveref, and fancyhdr is sufficient.
It does not access the network or install dependencies.

Mathematical scope
- Centered L2 potential stability for every finite-second-moment target, for
  strongly log-concave sources and compactly supported log-concave sources.
- Wasserstein absolutely continuous curve lifting and an action bound.
- Exponential transport inequalities for conditional Laguerre-cell laws.
- One-third map stability for targets in a common bounded set, including the
  sharp three-atom obstruction for the fixed standard Gaussian in d>=2.
- A coordinate-clipped interpolation inequality without globally bounded
  gradients, yielding explicit target-tail map bounds and a modulus under
  uniform integrability of the target second moments.
- The exponent (q-2)/(3q-2) for every q>2 under a bounded q-th moment, with matching
  two-atom sharpness for one fixed cube-truncated Gaussian and the uniform cube.
- For the full standard Gaussian, the sharp one-third exponent for every fixed
  q>2 moment class, via an unclipped minimum-weight interpolation.
- The same positive one-third rate for full-support kappa-strongly convex C1,1
  source potentials with globally Lambda-Lipschitz gradient. Its explicit
  constant is uniform for fixed d,kappa,Lambda,q. Sharpness is for the source
  class via its Gaussian member, not for every individual non-Gaussian source.
- Failure of every uniform map modulus under only a bounded second moment,
  already on the exact unit-second-moment class for a fixed standard Gaussian
  and a fixed uniform cube, in every fixed dimension d>=2.

All positive estimates hold in d>=1; the sharpness and endpoint obstructions
require d>=2. In d=1 the map distance equals W2. The full-support translation
results exclude hard convex boundaries. The general potential and tail results
allow those boundaries and nonsmooth convex source potentials.

Status and attribution
This is a research draft, not a formally verified or externally peer-reviewed
paper. Publication priority is not claimed. The inherited OpenAI framework is
attributed to a pinned revision. The introduction also identifies finite-moment
and interpolation precedents and does not claim novelty for qualitative uniform
continuity obtained by compactness. Full-text comparison with Merigot's HAL
preprint hal-05616391 remains unfinished; that limitation is not a premise of any
proof. The author field is intentionally blank.
