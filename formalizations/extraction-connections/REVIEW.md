# Independent internal review of the universal connections

Reviewer: the probability subagent, independent of the root author's four
universal connection modules. Read-only inspection on 2026-10-16; it did not edit
or compile the reviewed source. This is an internal AI review, not external
human peer review or a novelty certification. Kernel evidence is separate.

The first inspection found a substantive statement-strength issue: existential
choice of a general PPT channel did not retain the local Kraus witnesses used
inside its existence proof. The root author added `IsProductLocal`, proved it
for actual product-local channels, strengthened the finite existence statements,
and chose the universal family from the strengthened proposition. The reviewer
confirmed that complete local witnesses now occur before every unknown input,
including the blocklength-zero default branch.

The reviewer checked that lower and upper bounds use the same `tensorInput`,
the spectral reindexing directions agree, the finite budget is the actual
`m^k*n^k/K^2`, integer floor losses are retained, and the Gaussian cutoff is
`-2*z`. The positive smoothing diverges but vanishes after division by `sqrt k`.
No positive-blocklength identity is used at zero; the limiting argument is
eventually at positive blocklength. No other substantive flaw was found.

The reviewer requested these limitations be retained:

- Limits are pointwise for each fixed density and fixed `m,n`, not uniform in
  changing inputs or dimensions.
- Gaussian statements require positive varentropy and both local caps. These
  hypotheses cannot be discarded at the capacity/local-cap boundary.
- The entropy strong converse alone is not the complete local-cap converse.
- `bipartitePowerCoordinates` is a fixed dimension-preserving bijection. A literal
  standard copywise regrouping representation requires an additional fixed
  permutation bridge; no efficient gate bound follows from its existence.
- Sharp pure minimax and mixed Gaussian existence theorems do not by themselves
  show that one family simultaneously realizes both claims.
