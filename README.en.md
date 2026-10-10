# Mathematical research · mxym/math

[中文 README](README.md)

Mathematical research papers, formal proofs, Lean developments, and reproducible computational certificates.

**Yongxian Zhang**, School of Computer Science and Engineering, South China University of Technology.

Correspondence: [mxymmxym1@gmail.com](mailto:mxymmxym1@gmail.com) · ORCID: [0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536) · [author profile](AUTHOR.md)

Independent research with no external funding. AI is used for research assistance; each project states its proof sources, verification scope, and reproduction instructions.

[Preprints](#preprints) · [Claimed results](#claimed-results) · [Research directory](RESEARCH.md) · [Verification](#proof-and-reproduction)

## Preprints

The table lists the current version DOI for each published manuscript. Older immutable versions remain documented in [the Zenodo archive](releases/ZENODO_RECORDS.md) and the project provenance files.

| Preprint / research paper | Main result | Proof status | Current version DOI |
| --- | --- | --- | --- |
| [Qutrit–qudit APPT maximal purity](preprints/appt-qutrit-purity-2026-10/README.md) · [PDF](preprints/appt-qutrit-purity-2026-10/main.pdf) | Exact maximum purity for absolutely PPT states for every (n\ge3) | Main theorem fully formalized in Lean; the absolute separability corollary is written mathematics | [10.5281/zenodo.23269470](https://doi.org/10.5281/zenodo.23269470) |
| [Four equal Gaussian cells](preprints/gaussian-four-cell-global-2026-10/README.md) · [PDF](preprints/gaussian-four-cell-global-2026-10/paper.pdf) | Global sharp bound and equality classification for four equal Gaussian cells | Complete written proof; exact finite diagnostics and partial Lean | [10.5281/zenodo.23272806](https://doi.org/10.5281/zenodo.23272806) |
| [Erdős similarity: growing logarithmic gaps](preprints/erdos-similarity-growing-gaps-2026-10/README.md) · [PDF](preprints/erdos-similarity-growing-gaps-2026-10/paper.pdf) | Positive-measure affine non-universality for a class of growing-gap sequences | Complete written proof with exact finite diagnostics; the full Erdős conjecture remains open | [10.5281/zenodo.23272807](https://doi.org/10.5281/zenodo.23272807) |
| [Graph-state MMI forbidden-subgraph theorem](preprints/graph-state-mmi-forbidden-subgraph-2026-10/README.md) · [PDF](preprints/graph-state-mmi-forbidden-subgraph-2026-10/paper.pdf) | Proof of Fuentes–Keeler–Munizzi–Pollack Conjecture 1 and the claw-vertex-minor classification | Complete written proof and two independent exact checkers; not fully Lean formalized | [10.5281/zenodo.23272728](https://doi.org/10.5281/zenodo.23272728) |
| [All-graph strong Chollet inequality](preprints/all-graph-chollet-2026-10/README.md) · [PDF](preprints/all-graph-chollet-2026-10/paper.pdf) | Strong inequality for every finite simple unweighted graph and every principal submatrix | Complete fixed Lean development | [10.5281/zenodo.23252964](https://doi.org/10.5281/zenodo.23252964) |
| [Pure-state ECQC prime-dimensional classification](research/ecqc-pure-state-counterexamples/README.md) · [PDF](research/ecqc-pure-state-counterexamples/paper.pdf) | The pure-state assertion holds for prime dimension iff (p=2); all odd primes have full-rank counterexamples | Complete written proof and exact checkers; the qutrit witness is also Lean-verified | [10.5281/zenodo.23256948](https://doi.org/10.5281/zenodo.23256948) |
| [Gaussian equal-cell simplex first moments](preprints/gaussian-equal-cells-2026-10/README.md) · [PDF](preprints/gaussian-equal-cells-2026-10/paper.pdf) | Sharp upper bound and equality classification for all equal cell counts | Complete written proof; only part of the all-(k) argument is Lean formalized | [10.5281/zenodo.23250730](https://doi.org/10.5281/zenodo.23250730) |
| [Fixed-mass Gaussian regular-simplex counterexample](preprints/gaussian-fixed-mass-propeller-counterexample-2026-10/README.md) · [PDF](preprints/gaussian-fixed-mass-propeller-counterexample-2026-10/paper.pdf) | Strict non-regular improvement for every (0<p<1/4) in the stated four-cell mass family | Complete written counterexample; exact (\mathbb Q(\sqrt2)) diagnostics and partial Lean | [10.5281/zenodo.23272917](https://doi.org/10.5281/zenodo.23272917) |
| [All-integer Gaussian dimension order](preprints/gaussian-quadratic-dimension-all-k-2026-10/README.md) · [PDF](preprints/gaussian-quadratic-dimension-all-k-2026-10/paper.pdf) | Matching (\Theta((\log k)^2)) dimension order for all sufficiently large integer (k) | Complete written proof with Berry–Esseen input and exact replay | [10.5281/zenodo.23273190](https://doi.org/10.5281/zenodo.23273190) |
| [ECQC equality rigidity and stabilizer classification](research/ecqc-stabilizer-saturation/README.md) · [PDF](research/ecqc-stabilizer-saturation/paper.pdf) | Full-rank equality states and pure stabilizer states in odd prime dimensions | Complete written proof and exact replays; not fully Lean formalized | [10.5281/zenodo.23256934](https://doi.org/10.5281/zenodo.23256934) |
| [Sharp Gaussian dimension–accuracy tradeoffs](preprints/gaussian-sharp-dimension-rate-2026-10/README.md) · [PDF](preprints/gaussian-sharp-dimension-rate-2026-10/paper.pdf) | Explicit error-versus-(\log^2 k) dimension tradeoffs and spherical-cap refinements | Complete written proof and exact replay | [10.5281/zenodo.23273299](https://doi.org/10.5281/zenodo.23273299) |
| [Mutual-information continuity counterexample](preprints/mutual-information-continuity-2026-10/README.md) · [PDF](preprints/mutual-information-continuity-2026-10/paper.pdf) | A ternary counterexample at every sufficiently small positive distance | Classical counterexample fully Lean-verified; quantum embedding remains written mathematics | [10.5281/zenodo.23253944](https://doi.org/10.5281/zenodo.23253944) |
| [Gaussian spherical-cap dimension converse](preprints/gaussian-spherical-cap-converse-2026-10/README.md) · [PDF](preprints/gaussian-spherical-cap-converse-2026-10/paper.pdf) | An (\Omega((\log k)^2)) lower bound for additive (O(1/k)) approximation | Complete written proof and outward-rational replay | [10.5281/zenodo.23273187](https://doi.org/10.5281/zenodo.23273187) |
| [Arbitrary-mass Gaussian centroid envelope](preprints/gaussian-centroid-mass-envelope-2026-10/README.md) · [PDF](preprints/gaussian-centroid-mass-envelope-2026-10/paper.pdf) | (U(p)-2Q(p)\le M_d(p)\le U(p)) for every positive mass vector, with two-logarithmic consequences | Complete written proof and exact interval replay | [10.5281/zenodo.23273177](https://doi.org/10.5281/zenodo.23273177) |
| [Sharp cofactor spectral asymptotics](preprints/article-revisions-2026-10/sharp-cofactor-asymptotics/README.md) · [PDF](preprints/article-revisions-2026-10/sharp-cofactor-asymptotics/paper.pdf) | Large-order logarithmic asymptotics and rank-two endpoint statements | Theorem 1 fully Lean-verified; later ramp/endpoint claims remain written mathematics | [10.5281/zenodo.23255145](https://doi.org/10.5281/zenodo.23255145) |
| [Bapat (q)-permanent counterexamples](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/README.md) · [PDF](submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/paper.pdf) | Explicit complex rational counterexample and an existence theorem for real symmetric integer counterexamples | Both main results fully Lean-verified | [10.5281/zenodo.23252928](https://doi.org/10.5281/zenodo.23252928) |

The complete catalog, including smaller formalized results and research notes, is in [SOLVED_PROBLEMS.md](SOLVED_PROBLEMS.md) and [RESEARCH.md](RESEARCH.md).

## Claimed results

The repository records the precise scope of each claimed proof, counterexample, or classification. It does not make unverified claims of first priority or worldwide novelty. See [SOLVED_PROBLEMS.md](SOLVED_PROBLEMS.md) for the full list, including unresolved limits.

Examples include the Bapat (q)-permanent conjecture counterexamples, the Wakhare entropy-root counterexample, the cycle chromatic infinite-log-concavity classification, the Gaussian four-cell theorem, the graph-state forbidden-subgraph theorem, and the prime-dimensional pure-state ECQC classification.

## Proof and reproduction

Each project page contains its theorem statement, proof scope, external inputs, and reproduction commands. Central entry points are:

[Formalizations](formalizations/) · [Verification records](verification/) · [Research directory](RESEARCH.md) · [Integrated manuscripts](manuscripts/README.md)

“Complete Lean” applies only to the explicitly listed theorem. A finite certificate or successful build does not automatically certify an entire paper. Public manuscripts state their remaining assumptions and open parts.

## Citation, versions, and licensing

Use the current version DOI and the frozen source commit when citing a paper. Older immutable versions remain in [releases/ZENODO_RECORDS.md](releases/ZENODO_RECORDS.md) and in the project provenance files.

Public preprints and DOIs do not imply journal peer review, mathematical correctness certification, originality, or historical priority. Third-party material retains its stated license; original material without another license is reserved.

## Collective-unitary logarithmic-negativity rate

[The analytic preprint](research/collective-unitary-negativity-rate/README.md) determines the exact per-copy maximum logarithmic-negativity rate for every bipartite spectrum in every fixed pair of local dimensions. A fixed blockwise Bell output basis suffices. The proof uses the published matrix Bernstein theorem and includes exact ancillary checks with corrupted-source controls; it is not Lean-formalized or externally peer reviewed. This does not resolve the separate finite-copy APPT purity conjecture or APPT=AS.

## Global-unitary extraction capacity and exact exponents

[The analytic preprint](research/global-unitary-ppt-extraction/README.md) gives a common capacity and exact all-rate target-fidelity exponent for local product channels, LOCC and completely PPT channels, after collective global-unitary preprocessing on the original system. The matching construction is deterministic variable-dimension Bell packing. The prior entropy converse is credited; the paper proves spectral achievability and the common exponent. Exact ancillary CI and source-mutation tests passed. This is not Lean-formalized, externally peer reviewed, or a solution of ordinary fixed-input LOCC distillation.
