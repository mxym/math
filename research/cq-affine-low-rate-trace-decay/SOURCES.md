# Primary sources and scope

- Bartosz Regula and Hao-Chung Cheng,
  [*Sharp one-shot bounds and optimal exponents of universal randomness
  extraction*, arXiv:2611.33270v1](https://arxiv.org/html/2611.33270v1).
  Equations (22)–(25) define the independence classes and trace
  distance, and Theorem 11 with Equation (7) gives the exponent for
  four-wise-exact collision families. Section IV.5, Lemma 16,
  Equation (144), and the final paragraphs distinguish this from the
  faster decay that can occur with ordinary universality, using
  scalar balanced bins for sources without side information.
  The authors explicitly leave a same-form achievability question
  with side information. The present low-rate analysis concerns
  a specified strong-three affine ensemble and does not solve the
  general side-information problem or claim that bin balancing
  carries over. For the uniform binary pure-state subclass we
  evaluate the natural analogue of the expression in (144) with
  sandwiched conditional entropy, including the distinction between
  the finite-order and infinite-order optimizers.
- Hao-Chung Cheng, Li Gao, Shi-Bing Li and Hongsen Qiu,
  [*Exponential Analysis for Trace-Distance Errors in Quantum
  Information Theory*, arXiv:2611.34468v1](https://arxiv.org/html/2611.34468v1).
  Theorem 24 gives the i.i.d. trace-distance exponent for
  independent random binning. Section V.E, Eq. (54) and the
  discussion around it, gives a different exponent for
  strongly two-wise affine-field-projection hashes on a flat
  input with trivial side information. That source is not a
  noncommuting cq source, and the complete uniform binary
  matrix ensemble used here is not their affine-field-projection
  law (except in the one-bit binary case).
- Alessio Meneghetti, Massimiliano Sala, and Alessandro Tomasi,
  [*A weight-distribution bound for entropy extractors using
  linear binary codes*, arXiv:1405.2820](https://arxiv.org/pdf/1405.2820).
  Theorem 3, Eq. (4), is the classical weight-distribution
  upper bound for total variation after a fixed binary linear
  map on an i.i.d. Bernoulli source. The scalar Fourier-style
  upper estimate is not new. It does not give the matching
  expected lower bound and prefactor with cq side information.
- Serge Fehr and Christian Schaffner,
  [*Randomness Extraction via Delta-Biased Masking in the
  Presence of a Quantum Attacker*, arXiv:0706.2606](https://arxiv.org/pdf/0706.2606).
  Theorem 3.2 and §4.1–4.3 develop matrix-valued Fourier tools
  for cq sources with random additive masking and weighted
  squared-norm bounds. Operator Fourier analysis of cq sources
  is not new. The new step here is to compare the expected
  sum of trace-norm coefficients to a matching single-frequency
  contribution in the uniform affine-matrix ensemble.
- Roy Kasher and Julia Kempe,
  [*Two-Source Extractors Secure Against Quantum Adversaries*,
  Theory of Computing 8 (2012), 461–486](https://theoryofcomputing.org/articles/v008a021/v008a021.pdf).
  The binary cq parity trace-norm identity is already Claim 2.7
  and Equation (2.1); the operator Fourier decomposition is used
  in the proof of their Lemma 2.6. We do not claim those ingredients
  or the elementary Fourier triangle inequality as new.
- Masahito Hayashi,
  [*Large deviation analysis for quantum security via smoothing
  of Rényi entropy of order 2*, arXiv:1202.0322v6](https://arxiv.org/html/1202.0322v6),
  §VIII-B and Appendix E-A. The probability law and phase-state
  source in our comparison are the source of his Lemma 39, the
  uniform kernel of dimension \(\lceil n(1-R)\rceil\).
  The equality in Lemma 39 is HTML Eq. (151), or Eq. (150) on
  printed p. 28 of the [v6 PDF](https://arxiv.org/pdf/1202.0322v6).
  Lemma 40's displayed definition gives his \(d'_1\) normalization.
  The following inequality is HTML Eq. (152) / PDF Eq. (151)
  and is not itself claimed false. The associated IEEE
  publication DOI is [10.1109/TIT.2014.2337884](https://doi.org/10.1109/TIT.2014.2337884);
  its final typeset full text was not separately verified here.
- Vladimir Klebanov, Alexander Weigl and Jörg Weisbarth,
  [*Sound Probabilistic #SAT with Projection*,
  arXiv:1610.08167](https://arxiv.org/abs/1610.08167),
  Construction 2.2 and Theorem 2.3
  ([authors' PDF](https://formal.kastel.kit.edu/~klebanov/pubs/qapl2016.pdf)),
  give the classical strong-three affine family, citing Gomes,
  Sabharwal and Selman (AAAI 2006). The affine law and its
  strong-three property are prior art, not contributions of
  this note.
- Shun Watanabe,
  [*Expurgation Exponent of Leaked Information in Privacy
  Amplification for Binary Sources*, arXiv:1208.3017](https://arxiv.org/pdf/1208.3017),
  studies binary erasure and binary symmetric classical side
  information, mutual-information leakage, and the use of
  suitable or expurgated linear codes. Madhura Pathegama and
  Alexander Barg, [*Smoothing of Binary Codes, Uniform
  Distributions, and Applications*, arXiv:2308.11009](https://arxiv.org/abs/2308.11009),
  and [*Rényi divergence guarantees for hashing with linear
  codes*, arXiv:2405.04406](https://arxiv.org/abs/2405.04406),
  study classical noise smoothing and linear hashing under
  other norms or Rényi divergence. These are close classical
  precedents for using code spectra, not the cq trace-distance
  mean or exact prefactor studied here.
- Ke Li, Yongsheng Yao and Masahito Hayashi,
  [*Tight Exponential Analysis for Smoothing the Max-Relative
  Entropy and for Quantum Privacy Amplification*,
  arXiv:2111.01075](https://arxiv.org/pdf/2111.01075), §IV and
  especially §IV-B, distinguish the low-rate regime for
  purified-distance and relative-entropy security. Joseph
  M. Renes, [*Tight Lower Bound on the Error Exponent of
  Classical-Quantum Channels*, arXiv:2407.11118](https://arxiv.org/html/2407.11118),
  section “Improved bounds for compression and privacy
  amplification,” gives duality-based converse bounds
  for surjective linear extractors with purified distance.
  Neither addresses this exact trace-distance average over
  all binary matrices.
- Robert König, Renato Renner and Christian Schaffner,
  [*The operational meaning of min- and max-entropy*,
  arXiv:0807.1338](https://arxiv.org/abs/0807.1338), Theorem 1
  gives conditional min-entropy as optimal guessing probability.
  Salman Beigi, [*Sandwiched Rényi Divergence Satisfies
  Data Processing Inequality*, arXiv:1306.5920](https://arxiv.org/abs/1306.5920),
  and Rupert L. Frank and Elliott H. Lieb,
  [*Monotonicity of a relative Rényi entropy*,
  arXiv:1306.5358](https://arxiv.org/abs/1306.5358), give the
  data-processing and trace-power convexity facts used in the
  comparison and the binary pure-state calculation.

A bounded prior-art check on 27 Nov 2026 UTC included the primary
sources above and searches combining “low-rate”, “privacy
amplification”, “random linear”, “random affine”, “trace distance”,
“Fourier weight distribution”, “quantum side information”, and
“relative/annealed prefactor”. No matching theorem for the exact
mean or its prefactor for an arbitrary finite i.i.d. cq source at
the stated Fourier threshold was located. Absolute priority is not
claimed; no prior artifact or third-party data is redistributed.
