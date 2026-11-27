# Sources and exact scope

- Asker Friis Bach, Isabel Moreno Babuglia and Jonatan Bohr Brask,
  [*On the Failure Probability of Quantum Leftover Hashing with Bad
  Seeds*, arXiv:2611.03484v1](https://arxiv.org/html/2611.03484v1).
  Definition III.3 defines the collision functional, and
  Lemma III.16, equation (57), already gives its expected
  one-block hash bound. Equation (6) is the unsmoothed
  raw-conditional min-entropy condition. Equation (7), generalized in Theorem V.2, gives a
  reused-seed tail with quadratic dependence on the number of blocks.
  Definition III.5, equation (38), minimizes over a replacement
  side marginal. The fixed-side definition here upper bounds that
  distance and supplies the usual strong trace-distance comparison.
  Proposition IV.13 and equation (129) give (CI)+(MS);
  Proposition IV.15 proves the bound with coefficient \(k\)
  under stronger product and stationarity assumptions. Their
  §I.3.2 raises the hypothesis question. We give a weaker
  sufficient unsmoothed hypothesis and a stronger rate; we do not
  claim to have characterized all possible sufficient hypotheses.
- Kai-Min Chung and Salil Vadhan, [*Tight Bounds for Hashing Block
  Sources*, arXiv:0806.1948](https://arxiv.org/pdf/0806.1948),
  Theorem 3.8 and its Hellinger proof already give the classical
  common-seed error scale \(\sqrt{MT/K}\) when per-block
  conditional collision probabilities are at most \(1/K\).
  This is a classical prior result, not a new conclusion of our
  note. Its Hellinger control also implies a same-order classical
  fixed-seed second moment: squared Hellinger distance averages
  over the public seed, and squared TV is at most twice that
  distance. Their lower-bound sections establish the importance
  of the block-count loss; our classical binary example is
  illustrative. See also Kai-Min Chung, Michael Mitzenmacher and
  Salil Vadhan, [*Why Simple Hash Functions Work: Exploiting the
  Entropy in a Data Stream*, Theory of Computing 9 (2013), 897–945](https://theoryofcomputing.org/articles/v009a030/),
  Theorem 4.10 and its Hellinger proof.
- Daniela Frauchiger, Renato Renner and Matthias Troyer,
  [*True randomness from realistic quantum devices*,
  arXiv:1311.4547v1](https://arxiv.org/html/1311.4547v1#A1),
  Appendix A, equations (17)–(23), treats shared-seed blockwise
  hashing via a trace/total-variation hybrid. It explicitly mentions
  extension to quantum side information. It is prior art for reuse,
  the conditional-entropy approach, and first-moment hybrid bounds,
  not the relative-entropy squared-distance bound proved here.
- Marco Tomamichel, Christian Schaffner, Adam Smith and Renato Renner,
  [*Leftover Hashing Against Quantum Side Information*,
  arXiv:1002.2436](https://arxiv.org/abs/1002.2436), in particular the
  local collision-estimate and weighted trace norm approach.
  The arithmetic inequalities in Sections 2 and 4 of our proof
  are standard one-block ingredients; no novelty there is claimed.
- Robert König, Renato Renner and Christian Schaffner,
  [*The operational meaning of min- and max-entropy*,
  arXiv:0807.1338](https://arxiv.org/abs/0807.1338), Theorem 1,
  identifies CQ min-entropy with optimal guessing probability.
  For the standard interpretation of the true-marginal collision
  functional as pretty-good guessing, see Mario Berta,
  Patrick J. Coles and Stephanie Wehner,
  [*Entanglement-assisted guessing of complementary measurement
  outcomes*, Phys. Rev. A 90, 062127 (2014)](https://doi.org/10.1103/PhysRevA.90.062127),
  equations (A10)–(A12).
  Neither of these one-block facts is new; we give the short
  operator proof of the needed inequality independently.
- Masahito Hayashi, [*Precise evaluation of leaked information
  with universal₂ privacy amplification in the presence of
  quantum attacker*, arXiv:1202.0601v3](https://arxiv.org/html/1202.0601v3)
  Section 2, equations
  (7), (10), (13), and (15), and the privacy-amplification bounds
  in Section 3, already relate one-block secrecy at the real
  side marginal to modified quantum mutual information
  (relative entropy), conditional Rényi entropy, and Pinsker's
  inequality. We do not claim the one-block relative-entropy
  approach as new. Our bound applies its blockwise entropy-chain
  version to a reused seed and correlated CQ input.
- Martin Müller-Lennert, Frédéric Dupuis, Oleg Szehr, Serge Fehr
  and Marco Tomamichel, [*On quantum Rényi entropies: a new
  generalization and some properties*, arXiv:1306.3142v4](https://arxiv.org/abs/1306.3142),
  gives monotonicity in the order and the order-one limit for the
  sandwiched divergence. See also Salman Beigi,
  [*Sandwiched Rényi Divergence Satisfies Data Processing
  Inequality*, arXiv:1306.5920](https://arxiv.org/abs/1306.5920).
  The proof invokes standard Umegaki data processing and the
  corresponding von Neumann conditional-entropy properties.
- Patrick Hayden, Richard Jozsa, Dénes Petz and Andreas Winter,
  [*Structure of states which satisfy strong subadditivity of
  quantum entropy with equality*, arXiv:quant-ph/0304007v2](https://arxiv.org/pdf/quant-ph/0304007),
  equation (11), Theorem 6 and their account of Petz equality
  supply the two-endpoint Markov decomposition and recovery used
  in §6. The extra equality of the two cq marginals is crucial
  for the conditional-i.i.d. conclusion in that section.
- Bartosz Regula and Hao-Chung Cheng,
  [*Sharp one-shot bounds and optimal exponents of universal
  randomness extraction*, arXiv:2611.33270v1](https://arxiv.org/html/2611.33270v1),
  concerns one-shot and i.i.d. rate/exponent bounds for universal
  extraction and does not treat the same seed applied blockwise
  to a general correlated input.

A bounded public search checked the cited current versions,
earlier blockwise analysis, and the exact source identifier and
title together with “seed reuse”, “relative entropy”, “Pinsker”,
“blockwise hashing”, “collision”, and “quantum side information”.
No matching prior statement was located for the finite-dimensional
noncommuting CQ extension: true-marginal relative entropy and
linear-\(k\) squared-distance tail for one reused almost-two-universal
seed and arbitrarily dependent CQ blocks controlled by their raw-past
conditional collision terms. The classical scaling and one-block
relative-entropy method already have the antecedents given above.
This is an abstract positive security result under explicit input
and seed hypotheses, not an implementation claim.
