# Source map and mathematical scope

## Exact source identity

The principal source is OpenAI, A dimension-free logarithmic Sobolev inequality
for subgaussian log-concave measures, 23 September 2026, in openai/math at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a.

[Pinned manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-dimension-free-logarithmic-Sobolev-inequality-for-subgaussian-log-concave-measures-September-23-2026/paper.pdf)

The independent audit downloaded all four public PDFs listed in sources.json
and matched their exact lengths and SHA-256 hashes. PROVENANCE.json contains
those same pins and the relevant audited-input hashes. No external paper is
bundled. Source availability and permission to redistribute a complete paper
are separate matters; this release uses links and hashes only.

## Theorem to dependency map

- Theorem 1.1: sharp local entropy-loss refinement of source Lemma 4.2,
  pages 22-25. At kappa=0 the entropy/score/exponential-square hypotheses and
  scalar comparison coincide with that finite-observation lemma. The proof's
  independent-copy construction, comparison of quadratic minima, and ordered
  limits are attributed to that source. This note shifts posterior curvature
  from b to a=b-kappa, producing the weight (1-kappa r)^(-2), its optimal scalar
  factor, and the finite horizon.
- Corollary 1.2: apply the established theorem label by label, then Tonelli.
  The common kappa, joint measurability, independent noise, and integrated
  entropy, score-energy and exponential-square assumptions remain explicit.
  The observation limits are completed before integration over labels.
- Lemma 3.1: anisotropic positive-curvature entropy inequality and finite-energy
  approximation, with source Lemma 2.1, pages 6-7, as the audited prerequisite.
  The proof is supplied in full. Bakry and Emery, Diffusions hypercontractives,
  Proposition 3, printed pages 187-188, and Corollary 2, printed page 199,
  give the classical curvature background.
- Lemma 3.2: averaged matching-means observation cost, proved directly.
  Its theta=min(c/16,a/4) is positive; its finite constant depends on N,a,p
  and need not be uniform in N. Mesh uniformity is the relevant property.
- Section 4: adaptive common likelihood, posterior curvature, finite Hilbert
  minimum, dual comparison, conditional copy independence and integrable
  score tails. No commutation of adaptive coordinate projections with
  conditional expectation is assumed.
- Three limits: mesh at fixed N,u, then N at fixed u, then u. Full Gaussian
  observation precision is b+i delta; curvature precision is a+i delta.
  Their distinction yields the weighted integral after change of variables.
- Scalar comparison: monotonicity of the initial-score prediction energy J
  and the opposite-monotonicity integral inequality. The optimal factor is
  (1-kappa z)^(-1), not the coarser pointwise maximum of the weight.
- Section 5: proper quartic reference densities. Explicit Gaussian cubic
  prediction, entropy-limit error estimates, weighted and scalar sharpness,
  finite unweighted counterexample with gap greater than 12863/49152, and
  divergence at and beyond z=1/kappa are all supplied in the note.

Chen and Eldan, Localization Schemes, arXiv:2203.04163v2, Sections 2.4.2 and
3.2.3, Equation (27), give Gaussian-quadratic likelihood and mean-difference
entropy-drift background. Eldan, Koehler and Zeitouni, A Spectral Condition for
Spectral Gap, arXiv:2007.08200v2, Lemma 2 and Section 2.0.1, treat smooth
approximations to orthogonal controls. Those continuous-time results do not
by themselves justify singular adaptive finite observations; this note proves
its finite-step facts directly.

## Exact correction and release edits

The original last clause of Lemma 3.1 imposed only 2 theta<a. The exact
mathematical correction is 0<=theta<a/2. With a=1, pi=N(0,1/2), theta=-1,
the old clause asserts 1/sqrt(2)<=1/sqrt(3), which is false: its squared sides
are exactly 1/2 and 1/3. Gaussian averaging uses sqrt(2 theta) and requires
theta>=0; theta=0 is immediate. Every application already uses the strictly
positive theta=min(c/16,a/4), with theta<=a/4<a/2 and 8 theta<=c/2.

originals/entropy.tex and originals/entropy.corrected.tex are unchanged frozen
copies. square_exponential_domain.patch is the exact one-line audit patch.
public_editorial.patch records the remaining release edits: abstract review
status, source-section title, verification/scope prose, and explicit disclosure
of the correction. The theorem, conditional statement, both lemmas and every
proof match the audited corrected TeX exactly. check_correction.py enforces
this claim rather than relying on a prose summary.

The original six-file submission's hashes are in ORIGINAL_INPUT_HASHES.json.
The original administrative README and verification files are represented by
hashes rather than bundled. The public manuscript omits an unrelated
frozen-file status sentence; the archival TeX and editorial patch retain it
for byte-accurate provenance. The audit narrative is a public editorial
derivative: only
administrative provenance and build-environment prose were replaced; the
mathematical analysis and exact source pins are retained.

## Verification boundaries

The original checker tests exact finite identities; the independent checker
uses different symbolic moments and two genuinely adaptive three-copy models
with 4096 states each. Normal and optimized Python outputs agree. The explicit
negative-theta control is kept as a regression check. These computations and
hashes support the written analytic audit; they do not prove the limiting or
infinite-dimensional assertions in Lean.

No novelty, priority, journal-level assessment, complete Lean proof, or external
peer-review claim is made. The result is local entropy loss, not a general
nonconvex logarithmic Sobolev inequality. No source tensor hierarchy,
covariance-freezing package, or source main-theorem claim is a dependency.
