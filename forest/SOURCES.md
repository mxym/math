# Sources and prior-art boundary

## Primary source

Piotr Marszalik, "The Price of Privacy: Randomness Complexity of Graph-Based Multi-Secret Sharing," arXiv:2610.10002 and Cryptology ePrint 2026/2395, October 2026.

Relevant parts:

- Section II, equations (1)-(3): exact graph-CMSS model and source-support objective.
- Proposition 1: deterministic support-one criterion on arbitrary graphs.
- Theorem 3 and Appendix A: signed-subgraph criterion for support at most two.
- Section V: randomness criteria on larger graphs are identified as a natural next step.

The forest construction in PROOF.md is a direct specialization of the signed-subgraph mechanism, written self-contained. The arbitrary-support terminal impossibility is separate from the one-bit theorem and uses only endpoint privacy, connected binary endpoint support, and correctness.

## Related scope

Earlier multi-secret-sharing work studies entropy or general access structures, but not this edge-view, individually private, pointwise binary-domain support objective. The search checked the cited Marszalik paper, its public companion description, and searches combining graph-CMSS, forest, tree, leaf, randomness support, and multi-secret sharing. No matching exact forest 1/2/infinity classification was located.

## Claims deliberately not made

- no new arbitrary-graph one-bit theorem;
- no result for Shannon entropy;
- no approximate or coalition privacy;
- no result for cyclic graphs beyond the separately proved cycle package;
- no implementation or deployed-scheme security claim.
