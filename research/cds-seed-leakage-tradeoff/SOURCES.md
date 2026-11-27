# Original question and proof scope

- Atsuya Hasegawa and Ranitha Mataraarachchi, *New lower bounds for CDS
  and f-routing*, [arXiv:2609.24291v2](https://arxiv.org/html/2609.24291v2).
  Definition 2.4 is the one-secret-sender model and fixes the full
  \(\ell_1\) privacy normalization. Lemma 3.1 gives the transcript
  distance gap, and Lemmas 3.3–3.4 give posterior representations.
  Theorem 3.6 bounds deterministic SMP complexity in terms of the
  shared seed support, yielding logarithmic shared randomness
  lower bounds for inner product. Section 5 asks for
  a polynomial shared randomness lower bound for classical
  inner-product CDS with both errors constant and no restrictions
  on communication and private randomness. Corollary 4.5 gives
  stronger bounds under one-sided perfect conditions. Here both errors
  can be nonzero, but the linear bound needs one-side low seed leakage;
  the necessary leakage consequence applies to every protocol with
  a stated sublinear entropy budget. Neither settles the unrestricted
  polynomial question. The old posterior identities are ingredients,
  not new results.
- Benny Applebaum and Prashant Nalini Vasudevan,
  [ePrint 2018/1169](https://eprint.iacr.org/2018/1169),
  and Akinori Kawachi and Maki Yoshida,
  [ePrint 2021/1037](https://eprint.iacr.org/2021/1037),
  prove relations to communication complexity and older randomness
  lower bounds. In particular, communication-based versus pure
  preshared-resource lower bounds must be distinguished when
  private coins and communication are unrestricted.
- Uma Girish, Alex May, Leo Orshansky and Chris Waddell,
  [arXiv:2505.02939v4](https://arxiv.org/html/2505.02939v4),
  [Quantum 10, 2049 (2026)](https://doi.org/10.22331/q-2026-04-01-2049),
  give adjacent classical/quantum CDS results with other
  resources/complexity measures. Ch. 14 of the [Alex May's non-local quantum
  computation survey](https://arxiv.org/abs/2605.02840) and
  Hasegawa–Mataraarachchi §1.5 discuss quantum routing; this
  proof is only about classical CDS. In particular, [Bogner's robust
  routing bound](https://arxiv.org/abs/2608.05775v3) is logarithmic and
  concerns a quantum resource.
- R. Paturi and J. Simon, *Probabilistic communication complexity*,
  JCSS 33 (1986), 106–123, gives the standard link from sign rank to
  unbounded-error communication; J. Forster, [JCSS 65 (2002), 612–625](https://doi.org/10.1016/S0022-0000(02)00019-3)
  gives the spectral sign-rank bound applied to inner product in the
  source. The quantitative count here is proved directly from a
  bounded factorization and the Hadamard norm, not from Forster's
  change-of-basis theorem. Hasegawa–Mataraarachchi's §4 uses sign rank,
  but only obtains the stronger resource bounds when one error is zero;
  the present likelihood hypothesis is different.
- The Chebyshev calculation, elementary Hadamard norm, KL tail
  argument and perfect binary linear example are standard elementary
  ingredients. The new claim is their combination with transcript
  likelihood clipping to separate the robust CDS predicate
  at low rank and quantify both senders' required seed leakage.
  Searches through 2026-11-27 for CDS with
  “seed leakage,” “posterior,” “sign rank,” “mutual information,”
  “inner product” and “shared randomness” did not find the same
  bounded-leakage tradeoff. This check is not a priority guarantee.
