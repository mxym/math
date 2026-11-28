# Sources and scope

- Piotr Marszalik, *The Price of Privacy: Randomness Complexity of
  Graph-Based Multi-Secret Sharing*, [arXiv:2610.10002v1](https://arxiv.org/html/2610.10002v1),
  [ePrint 2026/2395 Nov. 11 fixed PDF](https://opencryptology.org/2026/2395/versions/20261111T233940Z.pdf).
  Section II Eqs. (1)–(3) define the arbitrary positive dealer
  weights, individually private views, perfect correctness and
  log-support cost. Section V lists randomness criteria on larger
  graphs as a next direction. Proposition 1, Theorem 3, Lemma 9
  and Appendix A give the deterministic/one-bit/edge-marginal
  results used in our Section 2. Appendix C-A Proposition 12 gives
  the three-state weight reduction; Appendix C-B Theorem 13 gives
  a general finite normal form. Appendix D applies a local
  three-state argument to a particular complete-graph domain.
  Theorem 5 already exhibits uniform ternary masked sums around
  a four-cycle in its five-point domain; Proposition 6 uses two
  masked paths in the complete graph. No first use of these
  mechanisms is asserted.
- The earlier repository
  [cycle classification](https://github.com/mxym/math/tree/81d7c7547efa879c28ca5b93efd0c999664c1b7b/research/cycle-multi-secret-support)
  determines \(m_{C_n}(D)\) for every \(n\ge4\) and binary domain.
  The new assertion is the entire connected unicyclic family,
  including triangles with attached vertices. Its residual
  three-state classification changes from a single signed
  congruence to an ordered affine-group criterion (1); Section 5
  shows this change is necessary. The cycle result is not claimed
  again, and Section 4 reuses its four-state construction.
- H. K. P. Anilkumar, A. Rajesh, V. Narayanan, M. M. Prabhakaran,
  V. M. Prabhakaran, *Randomness Requirements for Three-Secret
  Sharing*, [arXiv:2304.14934](https://arxiv.org/html/2304.14934),
  [ISIT DOI](https://doi.org/10.1109/ISIT54713.2023.10206455).
  Their binary \(K_3\) classification is separate; our theorem
  excludes the unattached triangle. D. Data, V. M. Prabhakaran,
  M. M. Prabhakaran, [IEEE TIT 2016](https://doi.org/10.1109/TIT.2016.2568207)
  gives the more general correlated multi-secret sharing framework.
- The [author's code and logs](https://github.com/pjmarszalik/price-of-privacy-code)
  cover the \(K_4\) exact computations and longer-version statistical
  privacy analysis; they are not used in the proof or included here.
  The standard graph-access-structure model in which vertex
  participants share a single secret and each edge authorizes
  reconstruction is not this edge-share, vertex-secret model.

Search scope, 2026-11-28: the short source and fixed longer PDF,
its companion, follow-up title/identifier searches, related
cycle/unicyclic/cactus correlated multi-secret-sharing support
criteria and the repository's unified research tree at
`e9424ed2cf3ea1556034b5368fd7c509ac0611d7`.
We did not locate this connected unicyclic classification in
those sources. Only one-vertex perfect privacy is claimed, and
the result is not for arbitrary graphs or Shannon-entropy cost.
