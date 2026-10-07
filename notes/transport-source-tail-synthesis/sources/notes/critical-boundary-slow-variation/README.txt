Critical boundary stability with slowly varying density factors
Supplement to research manuscript 008
7 October 2026

This is a supplementary research note, not a new numbered paper. It extends
the critical multiscale construction in manuscript 008 to positive C2 slowly
varying factors L satisfying x(log L)' -> 0 and x^2(log L)'' -> 0 near zero.
The source potential is C2 on its support interior, with an optional C-infinity
extension when L is correspondingly smooth. It has a genuine support boundary;
no full support or smoothness across that boundary is claimed.

Main result
For p>2, s=p/(p-2), and the specified fixed d-dimensional source with d>=2,
first marginal proportional near zero to x^(s-1)L(x)exp(-x^2/2), and the smooth
infinitely vanishing transverse factors of manuscript 008, the optimal map
modulus on targets of pth moment at most one is determined for EVERY sufficiently
small Wasserstein distance. Put

  H(h) = 1 + integral from h to a of L(x)/x dx
  F(h) = h^(3/2) H(h)^(1/(2s))
  G(h) = h^(1/2) H(h)^(1/(2s))

Then Omega(w) is comparable above and below to G(F^(-1)(w)). The note supplies
the uniform estimates, complete global mass-matching formulas, moment budget,
and all-small-distance inversion argument. The finite atom count may grow
as w decreases.

Consequences and qualifications
- For L(x)=[log(e/x)]^gamma, the exact modulus has the logarithmic correction
  [log(1/w)]^((gamma+1)/(3s)) when gamma>-1, the necessary iterated-logarithmic
  correction [log log(1/w)]^(1/(3s)) at gamma=-1, and no correction when gamma<-1.
- Within this precise family, pure one-third stability is equivalent to
  integrability of L(x)/x at zero and to the global zero-extended root condition
  r^(1/s) in W^(1,s). This is not a criterion for all source densities.
- A proved example with L(x)=exp([log(1/x)]^alpha), 1/2<alpha<1, shows why the
  implicit inverse cannot generally be replaced by the naive argument w^(2/3).
- In dimension one an atomless source gives the exact W2 map isometry instead.

Proof inputs and attribution
The overlap interpolation and multiscale global convex-potential mechanism
are inherited from manuscript 008 v1, pinned at:
https://github.com/mxym/math/blob/9af06fa4cadaa80e176ed633a7176ed7f2e813db/preprints/008-density-overlap-phase/v1/main.tex

The transport upper bound uses the exact all-P2 centered-potential theorem in
manuscript 001 v3, stated explicitly in the note and pinned at:
https://github.com/mxym/math/blob/5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3/preprints/001-strongly-log-concave-brenier/v3/manuscript.tex

That earlier work develops the OpenAI family 374 framework; its pinned source
is cited in the bibliography. The lower construction does not use the potential
estimate. No unpublished proof note is used as a hidden input.

Current repository main was checked before drafting at revision
37a4d9ccfd4c4898d09b56d8fda46ea3fd903055. No additional slowly varying extension
was present among the intervening preprint changes. This is an overlap check,
not a novelty certification or exhaustive literature search.

Status
AI-assisted research draft. Blank author field. Not externally peer reviewed
or proof-assistant formalized. No priority or journal-tier claim. Existing
manuscript 008 version files are preserved unchanged.

Build
Run ./build.sh in a standard TeX installation containing pdflatex, Latin Modern,
AMS packages, mathtools, microtype, geometry, hyperref, cleveref and fancyhdr.
The bibliography is embedded in manuscript.tex; no BibTeX run or external .bib
file is needed. The script runs three pdflatex passes. See BUILD_INFO.txt and
QA.txt for the final verification record. PDF metadata may vary by platform;
source and textual reproducibility are provided rather than a claim of
byte-identical PDF output on every installation.
