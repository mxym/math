# Primary sources and scope

- Masahito Hayashi, *Large deviation analysis for quantum
  security via smoothing of Rényi entropy of order 2*,
  [arXiv:1202.0322v6, HTML](https://arxiv.org/html/1202.0322v6),
  [same-version PDF](https://arxiv.org/pdf/1202.0322v6).
  Appendix E-A, Lemma 39, is the same binary phase-pure
  source problem and positive-rate uniform quotient sequence; HTML Eq. (151)
  is PDF Eq. (150). Its following inequality, HTML Eq. (152),
  compares another quantity and is not the equality evaluated
  here. The v6 material immediately before Lemma 40 already
  gives the decomposition of the conditional density operator
  into rank-one phase-coset blocks. Lemma 40 and Appendix E-C
  through E-E already use coset masses and types, and Lemma 43
  uses random-subspace incidence. Those structures and the
  classical random-coding formula are not new here. The
  comparison replaces the square-root-of-decoding-error
  estimates by matching two-sided pair-occupancy estimates
  for the trace norm. It yields twice Lemma 39's displayed
  exponent for \(0<R<1-H(\lambda)\). The literal
  zero-rate choice \(R=0\) gives an empty output in Lemma 39,
  not the positive-length zero-rate sequences treated by
  the new theorem. The IEEE
  typeset publication was not separately checked; no claim
  is made about that version.
- Robert G. Gallager, *A Simple Derivation of the Coding Theorem
  and Some Applications*, IEEE Transactions on Information
  Theory 11(1), 3–18 (1965),
  [DOI 10.1109/TIT.1965.1053730](https://doi.org/10.1109/TIT.1965.1053730),
  [primary PDF](https://web.mit.edu/6.441/www/reading/IT-V11-N1.pdf).
  This is the classical channel-coding random-coding exponent,
  not a novelty of the present calculation. See also Yuval
  Domb, Ram Zamir, and Meir Feder,
  *The Random Coding Bound Is Tight for the Average Linear
  Code or Lattice*, [arXiv:1307.5524](https://arxiv.org/abs/1307.5524)
  for the classical average linear-code problem.
- Joseph M. Renes, *On privacy amplification, lossy compression,
  and their duality to channel coding*,
  [arXiv:1708.05685](https://arxiv.org/abs/1708.05685);
  *Achievable error exponents of data compression with quantum
  side information and communication over symmetric
  classical-quantum channels*,
  [arXiv:2207.08899](https://arxiv.org/html/2207.08899), §2.2,
  Eq. (14), and §4. These works give a different exact
  correspondence based on fidelity (or squared purified
  distance) to an optimized ideal side marginal. The
  [2024 coding paper](https://arxiv.org/abs/2407.11118) is
  also about coding exponents. None is used as an identity
  for trace distance to the fixed **true** side marginal.
- Toyohiro Tsurumaru and Masahito Hayashi,
  *Dual universality of hash functions and its applications to
  quantum cryptography*,
  [arXiv:1101.0064](https://arxiv.org/abs/1101.0064):
  dual-universal hash families and phase-error-correction
  reductions. Toyohiro Tsurumaru,
  *Leftover hashing from quantum error correction:
  Unifying the two approaches to the security proof of
  quantum key distribution*,
  [arXiv:1809.05479](https://arxiv.org/abs/1809.05479):
  established phase-error/leftover hashing correspondence.
  Those reductions do not by themselves give the two-sided
  annealed true-marginal trace exponent stated here.
- Hao-Chung Cheng, Li Gao, Shi-Bing Li, and Hongsen Qiu,
  *Exponential Analysis for Trace-Distance Errors in Quantum
  Information Theory*,
  [arXiv:2611.34468v1](https://arxiv.org/html/2611.34468v1),
  Theorems 19 and 24, §V-E. Their exact reliability formula
  is for independent output assignments in the initial
  privacy-amplification map; their strong-converse result
  applies more broadly. Our auxiliary quotient occupancy
  bins are in the phase domain; they do not make the original
  affine hash an independent-random-binning ensemble.
- Bartosz Regula and Hao-Chung Cheng, *Sharp one-shot bounds
  and optimal exponents of universal randomness extraction*,
  [arXiv:2611.33270v1](https://arxiv.org/html/2611.33270v1),
  §IV following Eq. (147), discusses extending a classical
  high-Rényi-order bound to quantum side information. The
  phase-pure and readable-flag model here is a special
  quantum model; it does not resolve that discussion for
  general sources or all universal families.

A bounded duplicate check on 27 November 2026 used the arXiv
ID/title and combinations of “phase-error”, “binary pure”,
“true marginal”, “trace distance”, “random linear quotient”,
“Gallager”, and “Lemma 39”. It located the close primary works
above, but no matching exact theorem for the specified
ensemble and fixed-marginal distance. This is not a claim
of absolute priority. The finite phase-block and occupancy
estimates are independent of any prior coding bound.
