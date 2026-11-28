# Primary sources, model and novelty boundaries

* Piotr Marszalik, *The Price of Privacy: Randomness Complexity of
  Graph-Based Multi-Secret Sharing*, [arXiv:2610.10002v1](https://arxiv.org/html/2610.10002v1),
  Oct. 7, 2026; [ePrint 2026/2395](https://opencryptology.org/2026/2395),
  [Nov. 11 fixed PDF](https://opencryptology.org/2026/2395/versions/20261111T233940Z.pdf). Its §II Eqs. (1)–(3) specify the exact
  graph-CMSS model and support-size objective used here. Section III
  Proposition 1, Lemma 9 (in App. A), and Theorem 3 give deterministic
  and one-bit criteria on all graphs; we reproduce their cycle
  specialization, not new general criteria. Its §IV Theorem 7 classifies
  the **complete** graph on four vertices. Its Appendix C-A
  Proposition 12 proves the exact three-state weight reduction, which
  is also used and reproved here. Appendix D's local-star arguments
  address a particular complete-graph obstruction, including separate
  uniform and half-heavy cases. Section §V names randomness criteria
  on larger graphs as a next direction. For cycles of every length
  \(n\ge4\), the present note gives a full support-size criterion:
  the new ingredients are the degree-two itemized marginal analysis,
  the forced \(A_3\) relation in the three-state residual case,
  and the universal two-bit construction with disjoint truncated edges.
  Theorem 5 / Eq. (19) already constructs a uniform \(\mathbb Z_3\)
  masked sum for a specific five-point domain on the four-cycle
  (constant diagonals in \(K_4\)). Our sufficiency extends that same
  mechanism to all signed slices and lengths; we do not claim it as a
  new seed-sharing method. The universal construction extends the
  independent masked paths of Proposition 6 from two edge-disjoint
  paths in \(K_4\) to two overlapping paths in a cycle, with separate
  mask components on their shared edges.
* [Author's code and logs](https://github.com/pjmarszalik/price-of-privacy-code)
  report exact computations for \(K_4\) and \(K_3\), and a statistical
  privacy extension to the longer version. They are not used as
  certificate inputs to this package. The short source explicitly
  distinguishes the graph-CMSS question from a lower bound for general
  interactive private computation. We neither infer such a bound
  nor claim any result about statistical privacy.
* H. K. P. Anilkumar, A. Rajesh, V. Narayanan, M. M. Prabhakaran,
  V. M. Prabhakaran, *Randomness Requirements for Three-Secret Sharing*,
  [arXiv:2304.14934](https://arxiv.org/html/2304.14934),
  [ISIT DOI](https://doi.org/10.1109/ISIT54713.2023.10206455).
  Their §II and §IV/Table I give the prior \(K_3=C_3\) model and
  exact binary classification; that graph is not included here.
* D. Data, V. M. Prabhakaran, M. M. Prabhakaran,
  *Communication and Randomness Lower Bounds for Secure Computation*,
  [IEEE TIT DOI](https://doi.org/10.1109/TIT.2016.2568207), motivates
  the more general correlated multi-secret sharing framework. B. Masucci,
  *Sharing multiple secrets: Models, schemes and analysis*,
  [DCC DOI](https://doi.org/10.1007/s10623-005-2761-1), and
  C. Blundo and B. Masucci, *Randomness in multi-secret sharing schemes*,
  [J.UCS DOI](https://doi.org/10.3217/jucs-005-07-0367), are historical
  multi-secret frameworks, not the exact cyclic support classification.

A bounded search on 2026-11-28 queried the source title and identifier,
follow-up references, cycle graph/cyclic secrecy with correlated
multi-secret sharing, three-state and signed mod-3 conditions, and
graph-access-structure randomness. The repository's unified ref at
e6d7b87c3a6cc16fdaa708bce99171e06fce327b was also screened. No matching
complete \(C_n\), \(n\ge4\) classification was located in the
inspected sources. This is not an absolute priority claim. The proof
targets the pointwise, individually private model and does not solve
the larger-graph question for general graphs.
