# Literal classical-model and scope review

The fixed source is a single proof module, `src/Counterexample.lean`, with SHA-256 `1726a70d840a8af78ccde0fb0801273a5e9acc424b258684fce21c07d6c9419d`. This review is separate from the kernel audit and is not an external human peer-review certificate.

1. `P` is the actual diagonal 3 × 3 table with masses `(1-e)/2`, `(1-e)/2`, `e`. `Q` has the same first two diagonal masses, off-diagonal masses `e/2` at `(0,1)` and `(1,0)`, and zero final row/column.
2. `IsProbability` is the conjunction of pointwise nonnegativity and the double finite sum being exactly one. The family theorem proves this predicate for both actual tables.
3. `marginalA` and `marginalB` are the actual row and column sums. Their proved values are `[(1-e)/2,(1-e)/2,e]` and `[1/2,1/2,0]`. The independently compiled literal check uses coordinate two to verify that both cross-state marginals differ when `e > 0`.
4. `eta x = -x * Real.log x` and finite sums of `eta` give Shannon entropy with zero contributions at zero probability. `mutualInformation` is marginal-A entropy plus marginal-B entropy minus the joint entropy, not an assumed formula.
5. `totalVariation` is half the double sum of absolute entry differences. Its value on the actual tables is proved to be `e`.
6. The family theorem has only the explicit real-parameter hypotheses `0 < e` and `e <= 1/16`. It returns both probability predicates, exact distance, and strict violation of `h(e) + e log 8`.
7. The universal-negation theorem quantifies over actual arbitrary joint tables with their probability predicates. Its exact-distance witnesses also contradict a purported bound with distance at most `e`.
8. The arbitrarily-close theorem quantifies over every real `r > 0` and returns valid joint tables and a positive distance smaller than `r`. It is not merely a claim about one rational witness.
9. The target is the general different-marginals proposal in arXiv:2408.15226v2 Eq. (106), v1 Eq. (54). Its dimension term is `log(min(3^2,3^2)-1) = log 8`. The primary discussion distinguishes the fixed-one-marginal application from the more general proposal. The present witnesses do not address the fixed-one-marginal version.
10. The quantum diagonal embedding and the paper's Section 5 necessary-leading-coefficient discussion remain written arguments. This package supplies no formal general quantum spectral-function library and makes no claim that these additional arguments have been closed in Lean.

The independently compiled `verification/LiteralSemantics.lean` checks the literal family and arbitrarily-close signatures and both changing marginals, using the freshly built source module. Its stdout records the actual theorem signatures and only the three standard axioms. Full proof-source ownership and dependencies are separately covered by the empty-kernel trust-zero replay.
