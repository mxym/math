# Shape of the most uncertain observations after four or more insertions

**Yongxian Zhang.** AI-assisted research note, independently checked within the AI workflow; not externally peer-reviewed. No worldwide priority claim.

Fix the number $k\ge4$ of insertions and let the binary received length $n$ grow. The inferred input has length $n-k$ and the prior on it is uniform. Maximizing conditional Shannon entropy no longer favors a fully alternating received word. Instead, **every maximizing word eventually consists of an explicit number of long alternating segments**, separated by isolated doubled bits.

The eventual number of segments is
\[
 b_k=\left\lceil\frac1{2^{2/(k-1)}-1}\right\rceil .
\]
It is 2 for four insertions, 3 for five, and 4 for six. Each segment length differs from $n/b_k$ by at most $O_k(\sqrt{n\log n})$. With $H_k^*(n)$ the maximum entropy in bits and $A_n$ an alternating word, the gain is
\[
 H_k^*(n)-H_k(A_n)=\frac{k}{n}\big[(k-1)\log_2 b_k-2(b_k-1)\big]+O_k(\log n/n^2).
\]

This asymptotic, proved analytically, applies for **each fixed** $k$; it does not determine exact optimal positions or a uniform threshold over varying $k$. The [exact witness at length 18](EXAMPLE.md) already beats alternation for four insertions. The source paper's named conjecture is at *three* insertions, so this is not a counterexample to that assertion.

- [Proof: a uniform upper bound and a matching construction](PROOF.md)
- [One-double specialization and finite witness](EXAMPLE.md)
- [Sources and research boundaries](SOURCES.md)
- [Independent internal review of the main theorem](OPTIMUM-REVIEW.md)

Replay the exact auxiliary tests with Python 3.10+ and no third-party packages:
```sh
python3 -B -O optimal_check.py
python3 -B -O optimum_check.py
python3 -B -O check.py
sha256sum -c SHA256SUMS
```
Outputs: [author checks](OPTIMAL-CHECKS.txt), [independent multi-anchor checks](OPTIMUM-CHECKS.txt) and [finite witness](CHECKS.txt). The proof does not extrapolate the checks.
