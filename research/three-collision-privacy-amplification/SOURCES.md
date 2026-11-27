# Primary sources and scope

- **Questions and definitions:** Bartosz Regula and Hao-Chung Cheng,
  [Sharp one-shot bounds and optimal exponents of universal randomness
  extraction, arXiv:2611.33270v1](https://arxiv.org/html/2611.33270v1),
  Eqs. (22)--(25), Theorem 11, Lemma 12 and §IV.5. The source
  differentiates collision upper bounds, exact \(k^*\) collision
  equality, and strong \(k\)-wise independence. It gives the exact
  \(4^*\) asymptotic exponent and a constant-factor lower bound on
  trace distance, and asks in §IV.5 for the weakest conditions for
  such a converse. Lemma 12 uses an independent random bin to turn
  collision moments into centered Bernoulli moments. Our use of this
  trick for the first three moments follows that reasoning; the scalar
  lower bound uses a separate one-sided argument. We resolve the
  collision-order comparison (strong three fails; exact four suffices)
  and the restricted classical-side-information exponent, not the full
  question of weakest general structural conditions.

- **Parallel recent exponents:** Hao-Chung Cheng, Li Gao, Shi-Bing Li and
  Hongsen Qiu, [Exponential Analysis for Trace-Distance Errors in Quantum
  Information Theory, arXiv:2611.34468v1](https://arxiv.org/html/2611.34468v1),
  §V, in particular §V-E. They establish the independent-binning
  reliability exponent and general two-universal strong converse
  exponent. §V-E constructs the field-affine exact-two example
  \(\pi_m(ax+b)\) on a uniform field source, with a rare \(a=0\) error,
  as well as the zero-error, non-exact-two \(a\ne0\) subfamily.
  This construction and its distance are cited as existing. The
  present random-matrix affine family is different: its evaluations
  are strongly three-wise independent, and on a binary affine source
  its deviation is governed by rank deficiency of a uniform rectangular
  binary matrix. The scalar lower bounds compare optimal errors over
  the entire exact collision classes, not just those two ensembles.

- **Related affine hashing:** Jack Doerner and Lawrence Roy,
  [Tighter Bounds for the Oblivious Bit-Fixing Inner Product Extractor on
  Biased Seeds, ITC 2026](https://drops.dagstuhl.de/storage/00lipics/lipics-vol385-itc2026/html/LIPIcs.ITC.2026.1/LIPIcs.ITC.2026.1.html),
  Lemma 28 and §4, use a related inner-product hash with triple collision
  bounds in a biased-seed oblivious-bit-fixing setting. Binary affine
  hash independence, rank-counting and the dyadic affine source examples
  are standard ingredients; no novelty is claimed for them.

- **Known erasure connection:** Shun Watanabe, [Expurgation Exponent of
  Leaked Information in Privacy Amplification for Binary Sources,
  arXiv:1208.3017](https://arxiv.org/pdf/1208.3017), §III, Lemma 3,
  Theorem 4 and Remark 6, relate rank of the unknown columns for
  binary linear privacy amplification to decoding on a complementary
  erasure channel. In particular his Eq. (7) already displays the
  erasure random-coding exponent equal to the expression in our example.
  Their leakage quantity and expurgated-code comparison are distinct
  from the present optimum of average trace-distance error constrained
  to exact three-collision ensembles. See also Joseph M. Renes,
  [On privacy amplification, lossy compression, and their duality to
  channel coding, arXiv:1708.05685](https://arxiv.org/abs/1708.05685),
  for the broader connection. Chin Hei Chan, Fang-Wei Fu and
  Maosheng Xiong, [Decoding error probability of random parity-check
  matrix ensemble over the erasure channel, arXiv:2108.09989v2](https://arxiv.org/html/2108.09989v2),
  Theorems 1.1 and 1.2, give the corresponding rectangular rank
  expressions and exponential rates in the coding setting. There is no claim that the
  erasure exponent or rank method is new, or that the constrained
  exponent is the best achievable by unrestricted privacy amplification.

The closest matched prior claims are those just explained. Searches for
three-wise/exact-three trace-distance converses, the random-bin moment
lower bound, and affine-conditioned exact three-collision exponents
did not locate the matched scalar/converse statements. This is a
bounded literature check, not a claim of priority over every equivalent
formulation.
