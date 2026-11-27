# Sources and exact scope

1. **[EME]** Mohammad Etemad, Mohammad Mahmoody and David Evans,
   *Optimizing Trees for Static Searchable Encryption*,
   [IACR ePrint 2018/052](https://eprint.iacr.org/2018/052),
   [full text](https://eprint.iacr.org/2018/052.pdf). Printed p. 6,
   §3, Algorithm 2 sets \(n=2^k\), uses all perfect matchings on
   each complete weighted layer, and sets the edge weight to the
   local cost of the OR parent. Definition B.2 and Theorem B.1
   (printed p. 22) compare the sum of internal local costs to
   the optimum over all, possibly unbalanced, OR trees and give
   the disjunctive \(O(\log n)\) guarantee. The paragraph
   continuing on printed p. 23 asks if it holds for a broader
   class; it does not assert it for every monotone formula.
   Section 4.1 (printed pp. 12–13) experiments with two- and
   three-keyword conjunctions without proving an approximation
   guarantee. Theorem B.2 (p. 23) instead compares with the best
   *balanced* tree for dense single-keyword workloads. The
   expected-visited identity is Lemma B.3 and Appendix B.1.
   Here we state explicitly that the root is counted when using
   that convention. Algorithm 1 is the separate best-first rule.
2. **[AICR]** [Level-Optimal Search Trees Beyond Disjunctive
   Queries, c/0016](https://aicr.info/c/0016/). The stated
   existential asks for one strictly larger workload class with
   the bound against the all-shapes optimum and for every tie.
   Theorem 1 here gives such a class. The platform distinguishes
   the conjecture from its maximal reading over all monotone
   queries; our linear examples refute the latter without
   contradicting the positive existential answer. Pair conjunctions
   already suffice for a tight-order and sharp-leading-coefficient
   restricted negative statement. None of this is the adjacent
   [best-first problem c/0015](https://aicr.info/c/0015/).
3. **[AGHP]** Noga Alon, Oded Goldreich, Johan Håstad and René
   Peralta, *Simple Constructions of Almost \(k\)-wise Independent
   Random Variables*, Random Structures & Algorithms 3(3),
   289–304 (1992), [author copy](https://www.cs.tau.ac.il/~nogaa/PDFS/kwise1.pdf).
   The powering small-bias construction used in §5 is their
   established ingredient; the trace pairing is an equivalent
   nondegenerate bilinear realization. The proof includes the
   root count and the application to this tree family. The
   exponential, exact column-list version does not require it.
4. **Related but different.** Mainak Ghosh, Indranil Gupta, Shalmoli
   Gupta and Nirman Kumar, *Fast Compaction Algorithms for NoSQL
   Databases*, ICDCS 2015, pp. 452–461, [DOI](https://doi.org/10.1109/ICDCS.2015.53),
   [full text](https://dprg.cs.uiuc.edu/data/files/2015/fastCompactionPaper.pdf).
   Its §2 Eq. (2.1) treats cardinality-union costs including leaves;
   §4.3.3 Lemma 4.4 is for a one-pair smallest-output merge, not
   the level-perfect matching. Theorem 1 above uses actual layer minimization to
   handle nonsubadditive exceptional costs; Theorem 2 is not
   a hardness or approximation bound for choosing an optimal
   tree by some other algorithm.

**Bounded literature check, 2026-11-27.** We checked the full
2018/052 ePrint and searched variations of its title with
“level-optimal”, “Theorem B.1”, “conjunctive”, “broader class”,
“minimum-weight matching”, “OR tree”, and subsequent work
through 2026. We found no matching result for this fixed-summary
class, the forced first-layer pair-conjunction examples, or
the limiting coefficient. Evidence of practical SSE conjunctive
query support does not analyze the same combinatorial cost.
No priority claim is made beyond this targeted check.
