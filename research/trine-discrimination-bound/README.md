# The trine bound for three-state discrimination

Given three equally likely quantum states, how far can the sum of their pairwise trace distances exceed their optimal joint discrimination score? [Weiner’s Conjecture 6.3](https://arxiv.org/html/2609.17920v1#S6.SS5) predicts that no three states do better than the pure qubit trine. This draft gives a proof for arbitrary mixed states in finite dimension.

Here the joint score $S$ is **three times the optimal success probability**. With $T$ the sum of the three trace distances (each half the trace norm of a difference), the result is

$$
\max (T-S)=\frac{3\sqrt 3}{2}-2.
$$

Weiner already proved the qubit case, proved the pure-state case in any finite dimension, and gave both a trine attaining this value and mixed triples attaining it. What is shown here is the matching upper bound for arbitrary mixed triples. This does not classify all maximizers, describe the full quantum profile region, or address unequal priors.

## Proof and verification

The [proof](PROOF.md) uses an optimal dual operator for state discrimination to express the witness in terms of a chained Bell operator and the sum of three measurement marginals. A signed sum-of-squares inequality controls both at once. The certificate is exact: its Gram matrix is rational, and the polynomial identity is over $\mathbb{Q}(\sqrt 3)$.

Run from this directory with **Python 3.9+**; both checks use only the standard library. No solver, downloaded data, or floating-point test is required.

```sh
sha256sum -c SHA256SUMS
python3 -B -O verify.py
python3 -B -O independent.py
```

- [certificate.json](certificate.json): the finite Gram matrix and the 24 polynomial forms; encoding is specified in §4 of the proof.
- [verify.py](verify.py): checks the exact Schur pivots, expands the relabeled forms word by word, and checks they vanish on a trine realization.
- [independent.py](independent.py): tests leading principal minors with integer fraction-free elimination and separately expands the unaveraged polynomial before summing its six relabelings.
- [CHECKS.txt](CHECKS.txt): expected output. [SOURCES.md](SOURCES.md): primary sources, previous bounds, and limitations of the literature search.

**Status:** AI-assisted research and internal review, including a second implementation of the certificate check. This is not external peer review or proof-assistant formalization. No claim of worldwide priority.
