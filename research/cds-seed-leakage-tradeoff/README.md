# A seed-leakage tradeoff for conditional disclosure of inner product

For two-party conditional disclosure of secrets (CDS), allow nonzero
correctness and privacy errors as in Hasegawa–Mataraarachchi
[arXiv:2609.24291v2](https://arxiv.org/html/2609.24291v2).
The participants have arbitrary private randomness and arbitrary-size
messages. The receiver knows the inputs, but not the shared seed.
We bound resources using how much each local message reveals **about
the seed**, not about the secret. Alice's seed leakage is evaluated
with a uniformly random secret bit.

- On any one-side restriction where the seed-to-local-message
  likelihood tail is bounded, the predicate has a low-rank sign
  representation. The restriction is imposed on only one sender.
- For \(n\)-bit inner product, bounded seed mutual information in even
  one sender's message, uniformly over that sender's inputs, forces
  \(\Omega(n)\) bits of shared randomness. This applies also to
  the Shannon entropy of a nonuniform, even countably supported seed.
  In particular, the bound holds if only one message has constant
  length; the other length is unrestricted.
- More generally, if the shared randomness has entropy \(O(n^\alpha)\)
  for fixed \(0\le\alpha<1\), then for every fixed
  \(0<\beta<1-\alpha\), each sender's message must reveal at least
  \((\gamma\beta/8)\log_2 n-O(1)\) seed bits on all but at most
  \(2^{O(n^{\alpha+\beta})}\) of that sender's \(2^n\) inputs,
  where \(\gamma=1-2\varepsilon-\delta>0\) is the correctness/privacy gap.

A one-bit Alice construction uses \(n+1\) shared bits, so the linear
order in the constant-leakage restricted model is attainable. We do
**not** give an unrestricted polynomial lower bound and do not settle
the full question in §5 of the cited work.

See [proof](PROOF.md), [sources](SOURCES.md) and [replay log](RESULTS.txt).
