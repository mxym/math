# Perfect additive randomized encodings over a fixed abelian group

We classify exactly which finite-domain Boolean functions have a perfectly correct and perfectly private additive randomized encoding over each fixed finite abelian group G, with independent private randomness:

- If |G| is even: exactly XORs of local Boolean functions, possibly complemented.
- If |G| is odd and exceeds one: exactly functions depending on at most one party.
- If |G| is one: exactly constants.

The algebraic step rules out two-party XOR over every odd-order finite abelian group, even with arbitrary real encoding probabilities. It uses the fact that convolution squares of nonzero complex group-algebra elements with disjoint supports cannot agree in odd order. We give two proofs, using cyclotomic reduction and principal minors of Fourier reflections.

Separately, at perfect correctness and positive simulator total variation error delta, any non-XOR-separable Boolean function requires log2|G| >= 2 log2(1/delta) - O(1). This unconditional converse has no deterministic-zero or flatness assumptions.

Scope: ordinary external-evaluator ARE, no shared setup or secret common coins. No robust ARE, no statement about a concrete deployment. Perfect OR impossibility is due to Ishai–Kushilevitz–Yerushalmi, not a novelty claim here. Their public statements and source access limits are distinguished in SOURCES.md.

Read PROOF.md and run `./replay.sh` (Python 3.10+). Checkers are exact finite spot checks, not the proofs.
