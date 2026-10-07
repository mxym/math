Research manuscript 001, version 5
Source regularity and sharp Brenier stability under target moment bounds
7 October 2026

This is a coherent continuation of manuscript 001, not a new numbered paper.
The editable manuscript.tex is complete and has a blank author field. The PDF
uses native LaTeX mathematics. This is an AI-assisted research draft, not an
externally peer-reviewed or proof-assistant-formalized result. No priority or
journal-tier claim is made.

Proof scope
- Arbitrary-density minimum-weight interpolation, including proper extended-
  valued convex functions and zero or disconnected density support.
- Sharp coefficient 7 in the universal mean weight bound; the exact W1,1
  first-order weight limit.
- Uniform little-o refinements for every fixed finite-q gradient-moment class
  and every fixed stretched-exponential gradient-moment class, for each fixed
  W1,1 density. The little-o factors do not imply improved exponents.
- A root-density Sobolev/generalized-Fisher sufficient condition for pure
  one-third interpolation. It strictly weakens raw translation-ratio control;
  exp(-exp(x^2)) supplies an explicit smooth strongly log-concave separation.
- Complete retained proofs of the Gaussian logarithmic-second-moment exponent
  min(1/3, beta/(beta+1)), the second-moment endpoint obstruction, the bounded
  Hessian source-class extension, and exact (q-2)^(-1/6) Gaussian critical
  constant order.
- A single smooth full-support strongly log-concave source, arbitrarily close
  to Gaussian in total variation and forward relative entropy, simultaneously
  exhibiting optimal finite-q exponents, the logarithmic-second-moment lower
  scale along a sequence, and sharp stretched-exponential logarithmic powers.

Endpoint and source qualifications
The finite-q and stretched-exponential lower sequences have ratios tending to
zero at their endpoint rates. They defeat every larger finite-q power or smaller
stretched-exponential logarithmic power, respectively. Only the logarithmic-
second-moment example has a positive limiting ratio at its stated scale. No
all-small-distance lower envelope is asserted. Transport obstructions require
d >= 2; atomless one-dimensional sources give the exact W2 map isometry.

Proof dependency
Transport estimates require a separate Lipschitz estimate for centered Brenier
potentials. The paper states the exact all-P2 theorem from manuscript 001 v3 and
uses it for strongly log-concave sources. BV or Sobolev density regularity alone
is not claimed to imply it. The public full proof is pinned at:
https://github.com/mxym/math/blob/5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3/preprints/001-strongly-log-concave-brenier/v3/manuscript.pdf

Relation to earlier versions and manuscripts 007 and 008
Public v1-v4 are preserved unchanged. Version 3 retains the broader compact
log-concave and hard-boundary results, while version 4 records the Gaussian
logarithmic and critical-constant theorems retained here. The present version
credits manuscript 007 v2 for the existing BV tail conclusions, smooth finite-q
and q=2 obstruction, and raw translation-ratio positive results. The logarithmic
second-moment and proximity conclusions also adapt that existing geometry; the
stronger scale choice proves the stretched-exponential logarithmic-power
obstruction. Manuscript 008 v1 also establishes bounded-overlap interpolation and the same
root-density/generalized-Fisher criterion; that shared result is counted once.
The exact weight mean/limit, strict Sobolev refinements, explicit separation
from raw ratios, and smooth stretched-exponential obstruction are developed
here. The boundary phase diagram of 008 is a separate result and is not used
as a proof input. Neither 007 nor 008 is used as an unproved input.

Build
Run ./build.sh with a standard LaTeX installation containing pdflatex, BibTeX,
Latin Modern, AMS packages, mathtools, microtype, hyperref, cleveref and fancyhdr.
The script uses latexmk if available; otherwise it runs pdflatex, bibtex and two
further pdflatex passes. The supplied .bbl also records the resolved bibliography.
No network download is needed once the TeX packages are installed. Compilation
metadata can vary between systems; mathematical/textual identity is the intended
reproducibility target, not a byte-identical PDF across TeX installations.

Files
manuscript.pdf                Rendered article
manuscript.tex                Complete editable LaTeX source
references.bib                Bibliographic source
manuscript.bbl                Resolved bibliography
build.sh                     Build script
CHANGELOG.txt                Mathematical changes from v4
BUILD_INFO.txt               Build configuration and reproducibility record
QA.txt                       Final verification record
transport_latex_source_v5.zip Editable source and supporting files
SHA256SUMS                   Matching release-file hashes
