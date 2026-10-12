# Proof and verification scope

`paper.md` is a full written deduction from two explicitly attributed
inputs. Sivashankar arXiv:2606.24878v2 supplies the degree-three lemma,
whose full proof is reproduced in our notation with attribution in the
appendix; his Section 4 also supplies the degree-five peeling and
linearization/matching/star framework. Kahn's published small-codegree
edge-colouring theorem, stated in Kang--Kelly--Kühn--Methuku--Osthus,
Theorem 3.1, is the second input. Its exact hypotheses were checked in
the primary manuscript; this theorem is not re-proved or formalized here.
The source URL and downloaded PDF hash are recorded in `results/source.txt`.

The new step retains W=x3/2+x4 in the linearization budget, giving
e >= binom(q,2)-qr/2-3W. A larger W saves cover vertices through the
part partition; a smaller W preserves more linear four-blocks. Combining
these alternatives yields the exact transition factorization at q=5r/3.
The old 13/4 package remains unchanged as the complete elementary result.

Self-review checked incidence multiplicities, original simplicity versus
initial repeated auxiliary blocks, strict decrease of pair excess,
nonnegative versus possibly negative lower bounds, distinct defining
vertices for retained blocks, the precise linear-star union, pairing
ceilings, the large-degree colouring hypotheses, the small-degree
alternative, empty residuals, r>=2 bounds and every additive error.
No assumption that Ryser's conjecture holds is used.

The exact checker validates sparse-polynomial identities with a damaged
factor negative control; it independently constructs and deletes auxiliary
blocks and computes exact covers on exhaustive small families, duplicate
blocks, an F2 cube-plane family and a linear truncated F4 projective plane.
It also repeats the finite elementary diagnostics. These checks are
diagnostics, not finite substitutes for the general proof. No floating
point, solver assumption or unverified certificate is used.

Eight Lean exports check retained-block algebra, matching/star multiplication,
the residual coupling, error scaling, transition factorization, its lower
bound, transfer of additive errors and the final cover inequality. The
printed axioms are limited to propext, Classical.choice and Quot.sound.
The finite combinatorics, the local coloured-graph classification and Input K
are not Lean-formalized. No formal axiom asserting an unproved conjecture
is introduced; the partial file only checks scalar implications.

`verify.py --lean` checks the 17-file frozen payload, ordinary and optimized
exact diagnostics, kernel replay and exact axiom-output agreement. The PDF
is generated from the Markdown proof. Package hashes prove integrity,
not mathematical validity. No external mathematician or human peer review
has been involved. The separate explicitly requested Luna literature
comparison does not review the mathematical proof or establish priority.
