import ChromaticCyclesAllN.GeneralCycleChromatic

/-!
# Formalized infinite log-concavity classification of chromatic cycle polynomials

Theorems are in `ChromaticCycleAll`:

* `cycleGraph_chromatic_polynomial_classification`: the actual cycle graph has
  `(X - 1)^n + (-1)^n * (X - 1)` as its chromatic polynomial (all q-coloring
  counts are proved), and the absolute coefficient sequence is infinitely
  log-concave precisely for 3 <= n <= 11.
* `every_actual_cycle_n_ge_17_fails`: all n >= 17 fail already on the third
  log-concavity iterate at coefficient index two.

All preceding modules are needed to construct these theorems.
-/
