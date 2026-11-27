# Sources and attribution

* **[W] Christopher Williamson,** *Secret Sharing at the Shannon Ceiling*,
  [arXiv:2608.17047v1](https://arxiv.org/abs/2608.17047v1),
  [full text](https://arxiv.org/pdf/2608.17047v1). Section 3 equations (4)–(5)
  define the cyclic matching-selector access structure. Theorem 2 and
  Corollary 3 prove the unrestricted lower bounds, using Shannon
  inequalities as developed in Lemma 1 and Sections 4–6. The present
  exact constrained optimum, pointwise atom bound, and excess-entropy
  tradeoff concern minimum or nearly minimum helper entropy and general
  edge-disjoint matchings. The main result is not represented as the
  solution of a conjecture the original paper formally states.
* **Josh Benaloh and Jerry Leichter,** *Generalized Secret Sharing and
  Monotone Functions*, CRYPTO 1988, LNCS 403, 27–35 (1990),
  [DOI](https://doi.org/10.1007/0-387-34799-2_3),
  [paper](https://www.cs.cornell.edu/courses/cs754/2001fa/bena88.pdf).
  The original monotone-formula secret sharing construction duplicates
  the secret for OR and uses an additive split for AND. Our attainable
  construction on Williamson's formula is this standard construction,
  not a new sharing primitive. The contribution is the converse under
  the helper-size constraint and its pointwise and quantitative versions.
* **Siu-Wai Ho, Terence H. Chan, Alex Grant, Chinthani Uduwerelle,**
  *Error Free Perfect Secrecy Systems*,
  [arXiv:1207.1860](https://arxiv.org/abs/1207.1860). Theorem 1's
  error-free secrecy model with key independent of the source gives the
  key-atom bound and key entropy at least log of the source support
  size, independent of the prior. The pair (X-side tuple, one helper)
  gives that setting here. The elementary disjoint-fiber proof is
  included; no priority claimed for the one-helper atom or entropy bound.
* **Mitsugu Iwamoto and Junji Shikata,** *Secret Sharing Schemes Based on Min-Entropies*,
  [arXiv:1401.5896](https://arxiv.org/abs/1401.5896). General share
  min-entropy bounds and definitions are prior; the explicit pointwise
  D^(-r) bound here is for the different matching-selector constraint.

A focused duplicate search (2026-11-27) combined Williamson's title or
“matching-selector” with “helper entropy”, “exact bound”, “dealer randomness”,
“edge-disjoint”, and mirroring searches in the repository's research tree.
It found the general monotone-formula upper bound and standard support-size and
min-entropy facts above, but no matching conditional lower bound. This is
not an exhaustive priority claim.
