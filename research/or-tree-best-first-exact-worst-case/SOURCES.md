# Source and prior-art boundary

- Mohammad Etemad, Mohammad Mahmoody, and David Evans, *Optimizing Trees
  for Static Searchable Encryption*, IACR ePrint 2018/052
  ([paper](https://eprint.iacr.org/2018/052.pdf)). Section 3.1,
  Algorithm 1 (printed pp. 5–6) minimizes the probability of a true
  query on the merged label. Section 4.2 (pp. 13–14) already gives
  instances from small real data for which greedy is not exactly
  optimal. The “Open questions” paragraph in §5 (p. 16) discusses an
  empirical constant-factor expectation for real data and leaves a
  theoretical analysis of best-first and hybrid open; it does not assert
  an unrestricted worst-case constant. Appendix B.1, Lemmas B.2–B.3
  (p. 21) and Appendix B.2 Definition B.2 (p. 22) give the root-visit
  relation, SLC, and the optimal arbitrary-shape comparator. Theorems
  B.1–B.2 are for Algorithm 2, not Algorithm 1.
- [AICR c/0015](https://aicr.info/c/0015/), *A Constant-Factor Guarantee
  for Huffman-Style Search Tree Construction*. Its formal conjecture
  quantifies over arbitrary monotone-query distributions and over all
  tie-breakings, without a balancing restriction on either tree. The
  exact result here resolves that claim negatively, and also rules out
  an absolute bound for a best possible tie-break on every instance.
  It is not a claim about the heuristic on the source's datasets.
- Mainak Ghosh, Indranil Gupta, Shalmoli Gupta, and Nirman Kumar, *Fast
  Compaction Algorithms for NoSQL Databases*, IEEE ICDCS 2015,
  pp. 452–461, [DOI](https://doi.org/10.1109/ICDCS.2015.53),
  [author PDF](https://dprg.cs.uiuc.edu/data/files/2015/fastCompactionPaper.pdf).
  Its BINARYMERGING objective (§2 Eq. 2.1) adds the constant sum of
  leaf weights to the sum of internal union-cardinality weights.
  SmallestOutput (§4.3.3) is the same merge rule as best-first in the
  uniform single-keyword OR-tree case. Lemma 4.4 gives the logarithmic
  upper bound; the remark following Lemma 4.5 explicitly leaves a
  lower bound against the true optimum open. The proof here does not
  claim the logarithmic coverage result as new.
- Jarno N. Alanko, Ruben Becker, Davide Cenzato, Travis Gagie, Ben
  Kociumaka, and Nicola Prezza, *The Trie Measure, Revisited*, CPM
  2025 ([paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CPM.2025.19)).
  Section 2 explicitly connects its general prefix-free objective to the
  Ghosh et al. cardinality-union objective. It is a related coverage
  optimization formulation, not arbitrary monotone-query worst-case
  analysis of Algorithm 1.

Bounded literature check, 2026-11-27: read the source §3.1, §4.2,
§5 and Appendix B and searched exact-title/author follow-ups, AICR c/0015,
“crown graph” with “searchable encryption”/“best-first”, and
“SmallestOutput” with “BinaryMerging” and “approximation lower bound”.
The related 2015 paper, 2018 thesis and 2025 trie paper concern
cardinality/coverage. We did not find a prior threshold comparison or
the exact \(\lfloor n/2\rfloor\) and \((2\lfloor n/2\rfloor+1)/3\)
worst-case factors for arbitrary monotone-query weights. This is a
bounded search, not a priority guarantee.
