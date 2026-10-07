# Additional model review of manuscripts 004 and 005

Review date: 2026-10-07. Reviewed repository snapshot: [mxym/math at 65a1baa1307ec91bc53a96087641cc575690f285](https://github.com/mxym/math/tree/65a1baa1307ec91bc53a96087641cc575690f285).

## Conclusion and status

No confirmed mathematical correctness defect was identified in either version 1.1 manuscript after the proof checks and exact tests summarized below. No theorem erratum is recommended on this evidence. This is an additional model-conducted review, not independent human peer review, proof-assistant verification, or a guarantee of correctness. It does not determine priority.

The principal clarification concerns the scope of entry 005: its exact simplex-product exponential rate is already strictly below a rate available from known non-simplex blocks. This does not contradict the manuscript, which explicitly restricts its theorems. A [supplementary comparison with full derivation](../comparisons/2026-10-07-simplex-product-rate-gap.md) records that consequence.

The historical manuscript sources, PDFs and original verifiers are not modified by this supplement.

## Entry 004  Logarithmic density and similarity avoidance

[Reviewed source](https://github.com/mxym/math/blob/65a1baa1307ec91bc53a96087641cc575690f285/preprints/004-log-density-similarity/v1.1/build/main.tex).

The proof review covered the following dependencies:

- Upper Banach density supplies a sufficiently occupied large window together with uniform upper bounds on complementary windows. Subtraction gives simultaneous density flattening for all tested subwindows. Constants are chosen before the large-window parameter, in the order needed by the routing construction.
- The tree's local span bound charges an edge and its descendants, rather than unrelated sibling subtrees. Grid separation, periodic wraparound and the stability gap were checked.
- The exposure argument distinguishes independent current-edge selector bits from routing paths that may share entries. Conditioning on all selectors makes the required terminal entries distinct and gives the claimed failure probability.
- The scale representatives include boundary values and interval interiors. The exceptional-center repair covers every remaining center; it is not merely an almost-everywhere argument.
- Applying the normalized construction to scaled configurations preserves period one for the blockers. Tail indexing gives infinitely many distinct hits; reflection handles negative dilation; summable budgets give countable simultaneous avoidance.
- The squarefree application, the exclusions of the displayed direct geometric and sumset mechanisms, and the effective rational-certificate existence argument were checked.

The actual extension over the [pinned geometric-case source](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026) is the use of density flattening for irregular occupied logarithmic windows. The routing, local entropy and exceptional-center repair mechanisms are inherited and attributed. This criterion does not cover arbitrary zero-density logarithmic configurations, and no such extension is claimed.

### What the finite checker establishes

The original verifier checks the normalized covering and measure assertions for supplied finite rational point and interval lists. It does not verify that those points belong to a specified infinite configuration, establish positive logarithmic density, construct the complete countable blocker, or prove all-scale and infinite-hit conclusions.

The six published regressions were replayed. A separate exact oracle used intersections of boundary lines in the bounded parameter rectangle, direct periodic interval membership and an independent measure partition. All 1,000 deterministic seeded tests agreed: 564 covers and 436 failures. The tests included signed points, wrapping and overlapping intervals, empty and full-period blockers, and endpoint-heavy inputs. Every returned uncovered witness was checked against the original holes.

[Exact differential checker and results](../verification/2026-10-07-independent-review/README.md).

## Entry 005  Exact simplex product optimization

[Reviewed source](https://github.com/mxym/math/blob/65a1baa1307ec91bc53a96087641cc575690f285/preprints/005-simplex-product-optimum/v1.1/build/main.tex).

The proof review reconstructed the reduction and the quantifiers over all dimensions:

- Facet area-normal vectors give product multiplicativity and the simplex value. The zero-dimensional projection convention correctly includes interval factors.
- The logarithmic quotient derivative proves discrete concavity for all dimensions, with only the stated repeated increment at dimensions one and two.
- Two exact comparisons locate the unique root-optimal simplex block at dimension 13. The piecewise-linear perspective reduces every dimension to the two stated factor counts.
- Supporting lines remain upper bounds when their formal multiplicities are negative. The preferred residue branches become feasible in every dimension from 100 onward, and the exact dimension-99 obstruction proves sharpness.
- Strict balancing at eligible factor counts excludes the small-dimensional concavity degeneracy. Exactly 80 finite comparisons complete global uniqueness.
- The unique runner-up block is 14. Summing its per-dimension deficit proves dimension-mass stability, and eight 14-dimensional factors attain the additive constant 112.

The published exact certificate was reproduced byte-for-byte through dimension 300. A further run of the original verifier under Python's optimization flag passed through dimension 1000. A separate ascending-dimension dynamic program enumerated unordered partitions and counted all optimal multisets through dimension 300. It independently agreed with all seven rational inequalities, all 80 no-tie certificates, every optimum, and the complete checked recurrence-failure list.

These computations establish finite facts. The analytic concavity, supporting-line and geometric arguments are necessary for the all-dimensional conclusions; no finite test substitutes for them.

### The non-simplex comparison

[Feng–Hu–Liu–Xu, Theorem 1.3](https://archive.ymsc.tsinghua.edu.cn/pacm_download/743/12781--2026.8.26.pdf) already gives a 13-dimensional polytope Q with R_13(Q)>c_13. The supplementary derivation uses their construction to obtain the explicit lower bound R_13(Q)/c_13≥11774111/11760000. Its repeated-block base exceeds 2.810223952012, whereas the exact simplex-product base is 2.809964732559….

Multiplicativity makes the separation exponential, including all sufficiently large dimensions after adding bounded residual factors. This is a consequence of known non-simplex geometry, not a correction to entry 005 or a new unrestricted extremal theorem.

## Source integrity

The complete machine-readable [source manifest](../verification/2026-10-07-independent-review/source_manifest.json) records the reviewed paths, byte lengths and SHA-256 digests, as well as the pinned upstream source identities. Principal digests are:

- 004 main.tex: `2e3558848d7b022f85206ceefdafe3e75cd5c9307d70724bca5e1fc4c2dfdf38`
- 004 check_cover.py: `9595f9f2db8e4b25f62a7e6932a97d26652232de8f1611acd9a6dc648a16af01`
- 005 main.tex: `f709b04734073d0cf2d63eb958da68370d38a21a419301630b404279dc9428f0`
- 005 verify_exact.py: `cb224bbc33bbca0f09df6693030febebf1d4b1c0ce54d7a46631ef596cb41c18`
- 005 exact_certificate.json: `ca96820a672d2c514962dc774387e5b0a86127607477f81871d87ef98273d104`

The [replay instructions](../verification/2026-10-07-independent-review/README.md) distinguish tests of the historical verifiers from the self-contained arithmetic check for the supplementary comparison. None of these results is human peer review, a formalization of the infinite proofs, or a comprehensive literature-priority search.
