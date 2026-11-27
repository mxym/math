# Sources, scope, and priority

* **[SCW] Pengcheng Su, Haibo Cheng, Ping Wang.** *Key-Space Complexity of
  Information-Theoretic Target-Distribution Semantic Security*,
  [IACR ePrint 2026/1899](https://eprint.iacr.org/2026/1899);
  [28-page full text](https://eprint.iacr.asia/2026/1899.pdf), accessed
  2026-11-27. Printed pp. 3–4 give the fixed-predicate model and independent
  uniform key with perfect correctness. Section 2, Lemmas 1–2, gives the
  empirical posterior for independent dummies and the gain formula.
  Theorems 1–2 and Corollary 1, printed pp. 10–12, give the universal upper
  bound 1/(2 sqrt(k)), a general lower bound, and the uniform-source
  order result, not the exact profile. Theorem 5 with Lemmas 4–5, printed
  pp. 18–19 and Appendix A, gives the zero-gain polytope and perfect-correct
  posterior realization, including the injection idea used here. Section 6
  discusses an approximate sparse-convex analogue and nonuniform keys as
  future directions. Our §4 gives a finite optimization formulation of the
  approximate posterior problem; it does not give the proposed general
  sharp explicit bounds or treat arbitrary key distributions. Correctness
  error delta>0 in our paper is a separately defined extension; [SCW] does
  not ask for that tradeoff in its main result.
* **Yuta Sakai.** *Generalizations of Fano's Inequality for Conditional
  Information Measures via Majorization Theory*,
  [Entropy 22(3), 288 (2020)](https://doi.org/10.3390/e22030288),
  [arXiv:1801.02876](https://arxiv.org/abs/1801.02876). Proposition 1,
  Section 2.2, equation (12), Theorem 4, and equation (235) in Section 6.4
  give the general list-Fano symmetric-functional bound and the same type-0
  vector in the uniform case. In particular the converse bound (3) follows
  from that theorem by taking phi=1/2-F_r, L=k, and error 1-s. The elementary
  averaging proof here is included for self-containment, not claimed as a new
  majorization theorem or a new two-level Fano extremizer. The specialization
  to fixed Boolean prediction, its exact uniform-key cipher realization, the
  finite hypergeometric evaluation and its consequences are the focus here.
* **MHR. Khouzani and Pasquale Malacaria.** *Relative Perfect Secrecy:
  Universally Optimal Strategies and Channel Design*, CSF 2016,
  [DOI](https://doi.org/10.1109/CSF.2016.12), and *Generalized Entropies and
  Metric-Invariant Optimal Countermeasures for Information Leakage Under
  Symmetric Constraints*,
  [IEEE TIT 65(2), 888–901 (2019)](https://doi.org/10.1109/TIT.2018.2883705),
  [arXiv:1811.09652](https://arxiv.org/abs/1811.09652). Theorem 1 and
  Algorithm 1 of the latter give optimum support-constrained channels for
  symmetric generalized entropies; their all-small case makes every
  posterior uniform on k labels, which includes the ideal posterior shape in
  our perfect-correct uniform case. This is earlier support-constrained
  channel optimization with the same symmetric convex mechanism. The
  cardinality-specific fixed-predicate gain evaluation and correctness-error
  tradeoff are different questions.
* **Su–Cheng–Wang.** *The Information-Theoretic Limits of Hiding Among
  Decoys in the Shuffle Model*,
  [IACR ePrint 2026/667, revised 2026-11-01](https://eprint.iacr.org/2026/667).
  The primary abstract reports a reduction from perfectly correct
  uniform-key ciphers to message-dependent decoy mechanisms and results for
  symmetric channel statistics, mutual information, message recovery,
  TV information, and posterior variance. Thus neither message-dependent
  decoys as a primitive nor the generic preimage-channel perspective is
  new here. The publicly accessible abstract does not state the
  all-fixed-predicate hypergeometric profile or the decoding-error extension;
  the full PDF of this closely related report was not available in this search.
* **Joseph Jaeger, Thomas Ristenpart, Qiang Tang.** *Honey Encryption Beyond
  Message Recovery Security*,
  [EUROCRYPT 2016](https://doi.org/10.1007/978-3-662-49890-3_29),
  [IACR ePrint 2016/174](https://eprint.iacr.org/2016/174), introduces the
  target-distribution semantic-security notion. **Xinze Li, Qiang Tang,
  Zhenfeng Zhang.** *Fooling an Unbounded Adversary with a Short Key,
  Repeatedly: The Honey Encryption Perspective*,
  [ITC 2021](https://doi.org/10.4230/LIPIcs.ITC.2021.23), Definition 1 is a
  primary reference for the same one-ciphertext predicate-guessing game;
  that paper also studies constructions and multiple messages. Our bounds do
  not transfer to its key-reuse setting.

Checks for exact duplicates used combinations of the TDSS title and
"all predicates", "hypergeometric", "without replacement", "uniform key",
"list decoding" and the works above. No prior statement of the exact
fixed-predicate finite formula was identified in the sources we could read.
This is not a priority claim for symmetric-functional list bounds,
posterior sparsity, empirical posteriors, or the generic convex formulation.
