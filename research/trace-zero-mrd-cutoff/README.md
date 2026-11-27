# A cutoff for the trace-zero rank-metric binomial family

Let $H=\ker(\mathrm{Tr}_{\mathbb F_{q^m}/\mathbb F_q})$ and let $\delta$ have norm one. The family
$$
U_\delta=\{(x,x^q+\delta x^{q^{m-1}}):x\in H\}
$$
cannot be scattered for **any** prime power $q$ and $m\ge9$. The same holds at $q=2,m=8$. More precisely, a genus computation and the Hasse–Weil bound give a uniform count of pairs on $H$ with a prescribed nonzero Moore determinant. This rules out an unlimited extension degree in the specific family of Bartoli–Giannoni–Marino–Neri, arXiv:2603.27748v2, §5(ii). It does not assert nonexistence of MRD codes at these parameters.

We separately exclude pseudoregulus (monomial-graph) extensions for every $q$ and $m\ge6$. For $q=2$, where the Payne classification covers all maximum scattered subspaces, this suffices for full nonextendability in the remaining high-degree binary case. Exact finite checks in the binary family for $m\ge5$ leave six parameters at $m=5$ and one at $m=7$; all seven give scattered, nonextendable subspaces. The binary nonexistence ranges also follow from earlier work on the strong D-property of the Gold cube; see the source comparison.

- [Full proof and precise scope](PROOF.md)
- [Sources and overlap](SOURCES.md)
- [Deterministic replay output](RESULTS.txt)

Run `bash replay.sh` with Python 3. The two checkers use independent arithmetic and inspect the finite exceptions and matched counting identities. The general theorem uses Hasse–Weil and does not infer its conclusions from the sampled fields.

This is a finite-field and coding-theory theorem, not a claim about the security of a cryptographic protocol or implementation.
