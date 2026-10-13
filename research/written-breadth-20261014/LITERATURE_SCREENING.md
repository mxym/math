# Written breadth: current literature and candidate audit

Review date: 14 October 2026, Asia/Shanghai. Reviewer: `/root/written_breadth`, an OpenAI AI assistant. This is internal research screening, without external peer review, Lean execution or a priority certificate. It follows Section 6 of the 13 October handoff. No new theorem is claimed in this record.

The old complex rank-at-most-three, order-seven candidate must be removed from fresh attack. A public 3 October proof package now supplies a full written argument. Its core analytic reductions were read, and its rational endpoint obligations were independently recomputed. The author-maintained Minc directory still reports the older gap; that directory is therefore insufficient evidence of current unsolved status. See the [original proof](https://huggingface.co/datasets/PureOne/QX-NEPHRIEL-Seventh-String/blob/1f564410cdfef22e99d73dacca6da1816b18de3b/PROOF.md) and the source-bound [recheck](RANK3_PRIOR_RESULT_RECHECK.json).

## Route decisions

| Direction inherited from the handoff | Current primary-source evidence | Decision and exact remaining boundary |
| --- | --- | --- |
| Strong Chollet for every weighted Laplacian / real symmetric PSD Z-matrix | Pant–Singh v2 gives bipartite support and matrix closure results, then structured **unweighted** graph families. Its cycle proof uses the normalized off-diagonal weight 1/2. The general graph question remains in its conclusion. | Remains unproved in our work. Arbitrary weighted odd cycles are a real extension of that particular cycle theorem; all weighted graphs and all PSD Z-matrices are outside our completed scope. Retain the x-squared edge-addition obstruction and stop repeating unrestricted numerical searches. |
| Full complex coefficient plane for four-row permanent–determinant pencils | The classical permanent-only endpoint is established. Targeted current searches did not locate a primary full-plane theorem matching the repository candidate. | The repository candidate remains unproved. The imaginary-axis norm and equality classification count as one direction. A PPT-relaxation gap and inaccurate DPS output are not actual-matrix counterexamples or proofs. Negative search evidence does not establish historical priority. |
| Kim–Roush odd-order doubly stochastic maximum | Lavi's current primary manuscript states and proves the maximum and classifies equality. | Remove from candidate list. Do not reproduce the maximum theorem as new. |
| Complex rank-at-most-three Chollet at order seven | The 3 October package gives the 24/25 bound for both factors separately of rank at most three. The main proof was read and 40 independent rational checks passed. | Remove from candidate list. This is another author's public result, not our new theorem. Rank four and unrestricted rank remain outside that statement. |
| ECQC / parity constructions | Iqbal's antecedent and the current Wang–Wang–Chen counterexample manuscript are public. The latter is v3 dated 25 September. | Preserve the repository's narrowly stated critical-rank pure-state classification. Do not present parity as invented here, or a mixed-state ECQC failure as our new disproof. |

Pant–Singh's current title is *Structural Classes for Chollet's Permanent Conjecture*, v2 posted 18 September 2026; the April v1 title alone understates its expanded scope. Theorem 3.1 covers a symmetric Z-matrix with bipartite support against an arbitrary Hermitian PSD second factor. Their Theorem 5.3 uses unweighted cycles, Theorem 5.4 extends to blocks that are bipartite or cycles, and Theorem 5.5 gives the weaker self-Chollet statement for unweighted complete graphs. These statements do not close the handoff's all-weighted-graph target. [Primary v2 manuscript](https://arxiv.org/html/2604.24192v2).

Lavi's August manuscript states the Kim–Roush value and equality up to simultaneous permutations of a half-weight triangle plus transposition blocks. The final proof assembly and equality argument were read; its intermediate charge estimates were not reaudited. This is enough to avoid choosing the already-public theorem as a fresh target. [Primary manuscript](https://arxiv.org/html/2608.08933v1).

The rank-three October argument controls the numerator by an interpolated Bregman row bound and the denominator by Gaussian/sphere and spectral-tilt bounds. At order seven, all admissible top eigenvalues reduce to three scalar endpoints. The independent exact checks give upper bounds approximately 0.954617923, 0.793755502 and 0.891681829, all below 24/25. The actual fractions and positive margins are in the recheck JSON. No error was identified in the read main proof. Its higher-order appendix and small-order external input were not rechecked, and the public package expressly disclaims external human peer review and Lean. [Original source at fixed commit](https://huggingface.co/datasets/PureOne/QX-NEPHRIEL-Seventh-String/blob/1f564410cdfef22e99d73dacca6da1816b18de3b/PROOF.md).

A newer rank-four primary preprint proves stated quantitative bounds for all orders at least ten and for **tight** rank-four correlation matrices at order nine. Its statements leave general rank-four orders seven, eight and nine outside that scope. The complete finite certificates were not audited here. This gives a narrower possible fallback candidate, without turning a rank-restricted problem into unrestricted Chollet or assigning an unsupported importance score. [Primary rank-four manuscript](https://arxiv.org/html/2609.37461v1).

The through-order-six paper is a public, non-peer-reviewed primary preprint. Its main statement and Cauchy–Schwarz transfer were read, but its full border induction was not reaudited. Do not target orders already covered by that public proof claim without first identifying a substantive issue. [Primary preprint](https://www.preprints.org/manuscript/202608.2196).

Wang–Wang–Chen's current version reports CQC counterexamples in every dimension at least three and an ECQC counterexample at dimension seven with an unbounded prime-dimensional overrun. This is a metadata/abstract status check; it does not reverify their quantum proof. [Current primary version](https://arxiv.org/abs/2608.03828v3).

## Bounded continuation

The broad weighted target remains mathematically valuable but the existing x-squared obstruction is unresolved. A further attempt must supply a new analytic inequality, an exact cross-monomial certificate that generalizes, or a valid structural reduction; another batch of numerical points is not progress toward the theorem. If no substantive proof step appears in 45–90 minutes, switch directions.

The full complex four-row problem remains a distinct candidate with actual-matrix statements. Its full plane and arbitrary-rank Chollet remain preferred over carving existing work into additional counted directions. General rank-four low orders are only a restricted fallback and must remain labeled as such. No number of new solutions or importance rating is inferred from this candidate audit.

The finite-tree paper's forthcoming independent written review takes priority over exploratory work. No other worktree will be edited; no publication, push, resubmission or Lean audit is performed by this subagent.

## Evidence files

[SOURCES.json](SOURCES.json) lists actual reading ranges, current versions, posting dates, access limitations and downloaded source hashes. Third-party full texts remain in local temporary storage and are not copied into this repository. The source binding is to the bytes actually fetched, not to a previous assistant's reading. Negative search results are bounded observations.

[RESEARCH_LOG.md](RESEARCH_LOG.md) records this continuation's actual completed work and unresolved targets.
