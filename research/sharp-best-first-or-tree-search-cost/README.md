# Sharp worst-case search cost for best-first OR trees

For n ≥ 2 labelled leaves and arbitrary monotone query distributions, put k = floor(n/2). The best-first tree of Etemad–Mahmoody–Evans has sharp worst-case approximation ratio

    (2k + 1)/3

for the expected number of visited nodes when the root is tested. For the internal sum of local costs used in the paper, the sharp ratio is k and the sharp additive gap is (k−1) times the root's satisfaction probability. The upper bounds hold for every tie-breaking rule. A family of two-query monotone DNFs approaches all three bounds for every tie-breaking rule and attains them for suitable ties in the deterministic-query limit.

For disjunctive workloads there is a separate O(log n) positive bound for best-first. For a sequence of inputs with four keywords per file and uniform single-keyword queries, every tie-breaking has ratio Omega(log n/log log n), so even that special case has no absolute constant approximation. These coverage bounds leave a loglog gap.

This settles the unrestricted worst-case formulation on AICR c/0015 as false, not a formal assertion of the original paper. The paper asks for a theoretical analysis and comments about its real-data experiments. These are mathematical statements about the traversal objective, not about the security of an encryption scheme or the behavior of deployed workloads.

See PROOF.md and SOURCES.md; run `./replay.sh` with Python 3.10+. The finite tests are not the proofs.
