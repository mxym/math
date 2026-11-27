# Primary sources, mapping, and limits

## Target and scope

Mark M. Wilde, *Convex splitting by binary quantum hypothesis testing*,
[arXiv:2611.25496v1](https://arxiv.org/html/2611.25496v1), 19 November 2026.

* Section 7.2 identifies an extra half-logarithmic term in the noncommuting
  covering achievability and separately raises a matching covering
  converse. This note addresses restricted input/output classes. It does
  **not** solve the fully quantum or general mixed-output problem.
* Equations (2.2)--(2.7) define the independent, planted, and arbitrary
  placement mixtures and their two weight parameters. For c-q inputs the
  ordinary product-table mixture is exactly the conditional empirical
  average in (1). Our pairwise variant retains the actual classical table
  rather than identifying it with a product of table marginals.
* Appendix D, Theorem D.1, already gives the bounded-bit formula and
  $O(n^{-1/2})$ window for the classical independent experiment.
  Appendix D.1 / (D.23) uses it for simultaneously diagonal Eve. These
  statements are not claimed as new. Appendix E / (E.4)--(E.9) handles
  **packing** for pure Bob; the threshold displacement conditional on
  a word and the tail-tilt estimate from (D.12) come from that argument.
  The present proof shows the conditional tail estimate for completeness,
  and uses it in a different normalized Gram **covering converse**.
* Theorem 4.2, (4.23)--(4.37), identifies the two secrecy comparisons,
  adds the decoding error, and selects a fixed table for private
  communication. Theorem 5.1 and Corollary 5.2, especially (5.11),
  (5.14)--(5.16), and (5.25)--(5.28), implement the corresponding
  one-way public-table source protocol and compressed pairwise tables.
  Theorem 6.1 and (6.6)--(6.10) give the exact placement of the logarithmic
  losses. We replace the Eve bound only. We do not change the classical
  communication model, Bob's packing theorem or the coding error metric.

## Closest other primary results

* Hao-Chung Cheng, Li Gao, Shi-Bing Li, and Hongsen Qiu,
  [*Exponential Analysis for Trace-Distance Errors in Quantum Information
  Theory*, arXiv:2611.34468v1](https://arxiv.org/html/2611.34468v1).
  Definition 11 and Remark 13 explicitly identify independent c-q
  soft covering with the ordinary c-q convex-split distance. Theorems
  12 and 16 are tight **exponent** results away from the threshold; they
  are not bounded-third-order expansions in the Gaussian window.
  The elementary identification of the two distances is credited here.
* Yu-Chen Shen, Li Gao, and Hao-Chung Cheng, [*Optimal Second-Order Rates
  for Quantum Soft Covering and Privacy Amplification*,
  arXiv:2202.11590](https://arxiv.org/html/2202.11590), IEEE Transactions
  on Information Theory 70(7), 5077–5091 (2024). Theorem 13 and
  Proposition 14 give a one-shot testing characterization and exact
  Gaussian terms with an $O(\log n)$ remainder for c-q soft covering.
  Their Gaussian expression is the one refined here for particular ensembles.
* Hao-Chung Cheng and Li Gao, [*Error Exponent and Strong Converse for
  Quantum Soft Covering*](https://arxiv.org/abs/2202.10995), IEEE
  Transactions on Information Theory 70(5), 3499–3511 (2024).
  Pairwise-independent one-shot estimates and i.i.d./constant-composition
  exponent and strong-converse bounds do not
  give a bounded-order fixed-error remainder.
* Anurag Anshu, Rahul Jain, and Naqueeb Ahmad Warsi, [arXiv:1702.01940]
  (https://arxiv.org/abs/1702.01940), use pairwise-independent positions
  for convex splitting and position-based decoding. Pairwise sampling
  itself is not new; the new use here is the explicit second-moment
  spectral-row bound and control of the distinct-site Gram overlaps.
* Hao-Chung Cheng, Li Gao, Christoph Hirche, Hao-Wei Huang, and
  Po-Chieh Liu, [*Sharp estimates of quantum covering problems via a
  novel trace inequality*, arXiv:2507.07961](https://arxiv.org/abs/2507.07961),
  improve **relative-entropy** covering estimates. Those criteria and
  statements do not establish (3) in normalized trace distance.

A targeted comparison (2026-11-27) of these papers and searches for
third-order pure-state c-q soft covering, spectrum-based sample covariance,
and logarithm-free convex splitting did not locate either the
flat-conditional spectral-row estimate (6) or the compatible-compression
tail matching (3). It is a comparison of specific statements, not a
claim that every spectral or Gram technique is new. The note does not
claim a general relative-entropy, purified-distance, quantum-input, or
optimized-codebook result.
