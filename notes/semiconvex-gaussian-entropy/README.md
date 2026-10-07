# Semiconvex Gaussian entropy loss

A complete finite-observation proof of a sharp local entropy-loss comparison
under a lower curvature bound, with a conditional extension, optimal constants,
a finite unweighted counterexample, and an obstruction at the exact horizon.
The note refines the pinned OpenAI finite-observation lemma; its proof
architecture is attributed explicitly. No novelty or journal-level claim is made.

## Results and assumptions

For smooth strictly positive densities p,q on R^n, assume Hess(-log q)>=-kappa I,
kappa>=0, finite relative entropy H_0, finite initial relative-score energy I,
and E_p exp(c|Y|^2)<infinity for some c>0. Let H_r be the relative entropy after
common Gaussian convolution of variance r, and let
J(r)=E|E[grad log(p/q)(Y) | Y+sqrt(r)G]|^2.

For 0<z<1/kappa,

    2(H_0-H_z) <= integral_0^z J(r)/(1-kappa r)^2 dr
              <= (1-kappa z)^(-1) integral_0^z J(r) dr.

All z>0 are allowed when kappa=0. Both constants are sharp over the displayed
class. For kappa>0 no finite curvature-and-time-only scalar factor exists at
z>=1/kappa, already in dimension one with proper smooth quartic references.
The finite example p=N(0,1), q proportional to exp(x^2/2-x^4/256), z=1/2
violates the unweighted comparison by more than the exact rational
12863/49152. The conditional version keeps common curvature, jointly
measurable smooth conditional densities and first derivatives, independent
noise, and integrated finite entropy, score energy and exponential-square
moment with a common positive c.

J predicts the initial relative score. It need not equal smoothed relative
Fisher information. This bounds entropy loss; no general nonconvex logarithmic
Sobolev inequality is established. The hypotheses and strict horizon cannot
be silently removed.

## Read first

- paper.pdf: nine-page typeset note
- entropy.tex: complete editable proof
- SOURCE_MAP.md: attribution, exact source identity, dependencies and scope
- TECHNICAL_AUDIT.md: independent analytic audit and exact supporting evidence
- PROVENANCE.json and sources.json: verified public-source links, sizes and hashes

The independent analytic audit supports the main theorem, conditional version,
sharp constants, finite counterexample and threshold obstruction under the
stated hypotheses after one exact helper-domain correction.

## Exact correction

The original last clause of Lemma 3.1 allowed negative theta by stating only
2 theta<a. Its correct square-exponential domain is 0<=theta<a/2. Taking
a=1, pi=N(0,1/2), theta=-1 gives actual moment 1/sqrt(2), while the original
bound was 1/sqrt(3). Squared, this is the exact false comparison 1/2<=1/3.
Every downstream application already uses theta=min(c/16,a/4)>0, so the main
theorem and its hypotheses are unchanged.

The original and corrected mathematical TeX are preserved byte for byte under
originals/. square_exponential_domain.patch records the one-line correction.
public_editorial.patch records the remaining editorial changes. The verifier
checks that the public theorem, corollary, lemmas and all proofs equal those
in the audited corrected source. The original administrative delivery files
are represented by hashes only. The public manuscript omits an unrelated
frozen-file status sentence; the archival TeX and editorial patch retain it
for byte-accurate provenance.

## Reproduce the checks

Python 3.9+ and SymPy are needed. The original checker and correction checker
otherwise use the standard library. From this directory:

    python3 -B verify.py

This verifies the exact file whitelist, every manifest hash, preserved inputs,
deterministic archive bytes and saved outputs. It replays the unchanged
original checker, unchanged independent checker, and explicit negative-theta
regression normally and under python -O. The independent checker regenerates
the patch only in isolated temporary directories. The package stays unchanged.
No assertions are relied on for validation under optimization.

The original tests cover 192 Gaussian cubic predictions, 48 weighted-limit
derivatives, 36 adaptive finite minima, 48 precision kernels, four monotonicity
comparisons and the finite rational gap. The independent tests use symbolic
Gaussian moments and two three-copy adaptive models of 4096 states each.
Their discrete noise tests finite Hilbert-space algebra, not the Gaussian
entropy-cost lemma. The written proof and analytic audit supply the universal
and limiting arguments. These checks are not a complete Lean proof.

To rebuild the PDF outside the package, additionally install a standard
pdfTeX/LaTeX distribution with Latin Modern, microtype, AMS packages,
mathtools, booktabs and hyperref, plus Poppler:

    python3 -B verify.py --build --output-dir /tmp/semiconvex-entropy-build

The build runs three passes, checks nine pages and rejects final-pass warnings,
undefined references and overfull/underfull boxes. Shell escape stays disabled;
unused EPS conversion is disabled by a build-only wrapper. The date is fixed
for reproducibility. PDF byte identity is expected only with the same TeX
versions and fonts. If a minimal Debian-style TeX installation lacks formats
or font maps, the script builds those locally in the output directory without
changing the installed distribution.

## Public sources and archive

No copyrighted full paper is bundled. To download the four exact public pins
into a directory outside this package:

    python3 -B fetch_sources.py --destination /tmp/semiconvex-sources
    python3 -B fetch_sources.py --destination /tmp/semiconvex-sources --offline

The fetcher verifies TLS, SHA-256 and byte counts. This is optional; no network
request is needed to replay the checks. The audit already independently
retrieved and matched all four pins.

source.tar.gz contains the exact source whitelist, without paper.pdf or
release-level integrity records. To copy the verified archive elsewhere:

    python3 -B verify.py --archive /tmp/semiconvex-gaussian-entropy-source.tar.gz

The archive has sorted paths, fixed metadata and zero gzip timestamp.
SOURCE_MANIFEST.json hashes the source payload except itself. MANIFEST.json
hashes every release file except itself and SHA256SUMS; SHA256SUMS covers
MANIFEST.json and every other file except itself. PUBLICATION_WHITELIST.json
lists all permitted regular files. These integrity records are not signatures.

After any deliberate edit, mathematical and copy review must precede running
python3 -B tools/release_integrity.py to regenerate integrity records.
