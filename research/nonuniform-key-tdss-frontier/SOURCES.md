# Primary sources and scope

* Pengcheng Su, Haibo Cheng, Ping Wang, *Key-Space Complexity of
  Information-Theoretic Target-Distribution Semantic Security*,
  [ePrint 2026/1899](https://eprint.iacr.org/2026/1899),
  [readable PDF](https://eprint.iacr.asia/2026/1899.pdf),
  [version record](https://opencryptology.org/2026/1899), verified
  Nov. 12, 2026. Section 2 defines the fixed-target, one-ciphertext
  prediction game; Lemma 2 gives its Bayes expression. Lemma 5 uses
  uniform keys and sparse Bayes-plausible message posterior realizability.
  Corollary 1 gives the order for uniform priors and uniform keys;
  Theorem 5 gives the zero-gain sparse convex characterization. Section 6,
  p. 24 independently asks for an approximate sparse-convex analogue and
  explicitly identifies relaxation of uniform keys as an open direction.
  Here the key law is prescribed and independent of the message. The
  closed-form result addresses that second direction for a uniform
  target and all fixed Boolean predicates, not the entire direction for
  arbitrary message priors.
* The repository's earlier
  [Exact uniform-prior target-distribution semantic security](https://github.com/mxym/math/tree/83b31da02282f9f4500c5ac98afc8c740f4162c4/research/exact-uniform-tdss-tradeoff)
  already proves the exact uniform-key case, its average-error extension,
  and in §4 a finite sparse/top-mass LP for arbitrary finite message priors
  and predicates with **uniform** keys. None of those results is claimed
  again. Its neighboring balanced-partition extractor result studies
  uniform averaging in a different public-seed TV objective, not this
  private-key prediction game.
* Haijie Su, Haibo Cheng, Ping Wang, *Distribution-Aware Encryption with
  Optimal Recovery and Semantic Security*,
  [ePrint 2026/2192](https://eprint.iacr.org/2026/2192),
  [Nov. 12, 2026 fixed PDF](https://opencryptology.org/2026/2192/versions/20261112T135311Z.pdf).
  Theorem 4 simultaneously handles arbitrary finite joint sources, exact
  message-recovery optimum and upper bounds for key recovery and TDSS;
  it does not assert exact per-source TDSS. Appendix B.4 Eq. (59)–(60)
  already uses the decryption-vector normal form for MRS and KRS, which
  our §4 explicitly reuses with a TDSS objective. Appendix D.3 describes
  the family of injections and Appendix F.4 Eq. (83) explicitly analyzes
  uniform subsets without replacement with uniform keys through a
  variance certificate. Appendix F.3 Theorem 7 already recovers the
  lower square-root scale and sparse leading constant. We claim neither
  the normal form, nor the no-replacement uniform construction, nor the
  asymptotic order as new.
* Ferdinando Cicalese, Luisa Gargano, Ugo Vaccaro, *Bounds on the Entropy
  of a Function of a Random Variable and their Applications*,
  [arXiv:1712.07906](https://arxiv.org/html/1712.07906),
  [IEEE TIT DOI](https://doi.org/10.1109/TIT.2018.2883705).
  Their Eq. (3) defines \(R_m(p)\), and Lemmas 2–4 include both
  aggregation majorization and least shorter majorant. The same vector
  is in Sason [arXiv:1812.03324](https://arxiv.org/html/1812.03324),
  Eq. (30) / Lemma 5 for the Rényi relaxation. These sources do not
  make this vector the distribution of a deterministic aggregation in
  general; they bound such aggregations. Our theorem uses a
  key-conditioned randomized decomposition, not a deterministic
  partition of the key probabilities. The new connection claimed here
  is the exact attainable cipher posterior profile plus its TDSS
  optimality for arbitrary prescribed key laws.
* Joseph Jaeger, Thomas Ristenpart, Qiang Tang, *Honey Encryption Beyond
  Message Recovery Security*, [ePrint 2016/174](https://eprint.iacr.org/2016/174.pdf),
  §5 and Remark 5.6 introduce and bound the TDSS objective in the honey
  encryption setting; Xinze Li, Qiang Tang, Zhenfeng Zhang,
  [ITC 2021](https://doi.org/10.4230/LIPIcs.ITC.2021.23), studies
  unconditional selected-distribution protection and repeated encryption.
  Neither the random-oracle nor the repeated-ciphertext guarantees are
  asserted in this note. Cheng et al. [ePrint 2026/646](https://hbcheng.net/publication/optimal-low-entropy-encryption/)
  optimize key confidentiality and message-recovery success, not the
  fixed-predicate minimax profile. Biondi–Given-Wilson–Legay,
  [Apollonian cell encoders](https://doi.org/10.1109/TrustCom/BigDataSE.2018.00069),
  assumes uniform keys for its universal equivocation result. There is
  also related perfect-secrecy literature: Ho–Chan–Grant–Uduwerelle
  [arXiv:1207.1860](https://arxiv.org/abs/1207.1860) already proves the same
  maximum-key-mass necessity for Shannon secrecy (Theorem 1 / Eq. (3));
  we do not claim novelty for the even-message zero endpoint in isolation.

A bounded search on 2026-11-28 examined the latest ePrint records above,
exact title/identifier searches, TDSS with nonuniform keys, without
replacement, and majorization, and mathematically related posterior
aggregation/entropy results. The repository's unified ref at
83b31da02282f9f4500c5ac98afc8c740f4162c4 was screened; the actual
uniform-key predecessor was compared theorem by theorem. No
matching exact arbitrary-key-law TDSS result was located in the
sources searched. This is not an absolute priority claim.
