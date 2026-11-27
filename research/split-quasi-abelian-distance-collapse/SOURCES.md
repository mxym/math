# Source mapping and novelty boundary

- Maxime Bombar, Geoffroy Couteau, Alain Couvreur and Clément Ducros,
  *Correlated Pseudorandomness from the Hardness of Quasi-Abelian Decoding*,
  [ePrint 2023/845](https://eprint.iacr.org/2023/845.pdf) /
  [arXiv:2306.03488](https://arxiv.org/abs/2306.03488). Printed p. 9,
  “Security Against Linear Tests,” conjectures that the Gaborit–Zémor
  distance result extends to arbitrary abelian groups. The same page
  explicitly considers the split algebra over the ternary field with
  an elementary abelian 2-group for its Fourier arithmetic. Printed
  pp. 19–20, Theorem 20 and the two paragraphs following it, separate
  Fan–Lin's fixed-group result from their own growing-group conjecture,
  where \(k,\ell\) are constant, and explicitly suggest systematic form
  to avoid a full-rank issue. The authors do not print a fully quantified
  statement of the growing-group extension.
- [AICR c/0105](https://aicr.info/c/0105/) formalizes the distance claim:
  fix \(q\), \(1\le k<\ell\), and a positive \(\delta<1-1/q\) with
  \(k/\ell<1-h_q(\delta)\); for **any** abelian group family
  \(|G|\to\infty\), the probability of
  \(d_{\min}>\delta\ell|G|\) in the random systematic ensemble should
  tend to one. For each fixed \(q>2\), there is a prime \(p\mid q-1\)
  and a family \(G=C_p^d\) on which the probability instead equals
  zero for all sufficiently large \(d\), by our uniform deterministic
  distance bound. Thus no particular interpretation of their uniform
  generator sampler is needed. We do not claim a result for \(q=2\)
  or a classification for all abelian groups.
- Zhe Li, Hongqing Liu, Chaoping Xing, Yizhou Yao and Chen Yuan,
  *More Efficient SNARKs via Quasi-Abelian Codes: Faster, Smaller, and
  Field-Agnostic*, ePrint 2026/939
  ([manuscript](https://opencryptology.org/2026/939.pdf)).
  Printed p. 5, Theorem 1.1 and the ensuing paragraph, explicitly leave
  open the fixed-index/fixed-field asymptotic question in their
  \(\mathbb F_q[C_2^d]\) family (with odd prime fields in their theorem).
  Their finite-parameter distance estimate assumes a positive gap after
  subtracting a term growing with \(d/\log_2 q\); see also §3.2. Their
  §2.1 and §4.1 already describe the split group-algebra isomorphism and
  Walsh transform, which are not new here. Our estimate is an upper
  bound in a regime where that finite lower bound ceases to apply, not
  a contradiction to their finite results. We do not claim tight
  probabilities or dependence for every joint field/index scaling.
- Yun Fan and Liren Lin, *Thresholds of Random Quasi-Abelian Codes*,
  [arXiv:1306.5377v2](https://arxiv.org/abs/1306.5377v2), Theorem 2.1:
  fixed coindex \(|G|\), increasing index \(\ell\). Philippe Gaborit
  and Gilles Zémor, *Asymptotic Improvement of the Gilbert–Varshamov
  Bound for Linear Codes*,
  [arXiv:0708.4164](https://arxiv.org/abs/0708.4164), give the distinct
  successful binary double-circulant families. Neither prior theorem
  is contradicted by fixed index and growing elementary-abelian rank.
- Martino Borello, Cem Güneri, Elif Saçıkara and Patrick Solé,
  *The Concatenated Structure of Quasi-Abelian Codes*,
  [arXiv:1807.01246v2](https://arxiv.org/abs/1807.01246v2), credits
  Somphong Jitman and San Ling for the constituent decomposition.
  This is earlier background for the product in our §2. Their positive
  existence results do not claim fixed index with growing elementary
  rank. Our dense-cube counting uses standard repeated Cauchy–Schwarz,
  proved directly in §3. The contribution is the quantitative
  distance obstruction from applying the signed-cube support
  identity to a dense set of identical constituent vectors.
- Anonymous, *Small-support subcodes and distance collapse in modular
  group-algebra codes*, version 2.1-candidate (2026),
  [DOI 10.5281/zenodo.23046770](https://doi.org/10.5281/zenodo.23046770);
  [scope statement](https://www.evidencepress.org/releases/modular-code-obstructions/).
  That unrefereed work describes distance collapse with an elementary
  \(p\)-quotient in **characteristic \(p\)** and nonzero augmentation
  image, and gives earlier scalar binary modular credit to Pascale
  Charpin. In contrast \(p\mid(q-1)\) here, so the elementary family
  is split and coprime to the characteristic; the all-submodules bound
  does not use augmentation. We make no originality claim about its
  modular regime or the first failure of an all-groups formulation.
- Newer applied follow-ups looked at during the bounded search include
  Jia et al., *Quasar*, [ePrint 2026/1839](https://opencryptology.org/2026/1839),
  which refers to Li et al.'s concrete distance as an ingredient, and
  Li et al. [ePrint 2026/1940](https://opencryptology.org/2026/1940),
  which uses fast arithmetic over split extension fields and again
  cites the concrete bound. The present result does not evaluate
  those constructions. The separate 2025 scheme-specific literature
  is not the source of any of these abstract code-distance statements.

Bounded literature check on 2026-11-27: the primary papers above were
checked at the cited statement or abstract, and title/keyword searches
combined “quasi-abelian” with “asymptotically bad,” “semisimple,”
“elementary abelian,” “split group,” “monochromatic affine subspace,”
“Fourier support” and “minimum distance.” Apart from the explicitly
distinct modular and growing-index results, no matching published
fixed-index quantitative bound for the split elementary groups
was located. This limited search is not a guarantee of priority.
