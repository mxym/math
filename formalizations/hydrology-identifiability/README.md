# Exact identifiability and equifinality in a two-storage rainfall–runoff model

This package formalizes the exact algebraic core of the accompanying hydrology note.
It proves both sides of a useful model-design statement:

* the output of the two-storage linear model satisfies a scalar second-order
  equation whose coefficients depend on `(a,b,c)` only through
  `S = a+b+c` and `P = ac`; and
* under constant rainfall and zero initial storage, the first three output
  derivatives recover `a`, `b`, and `c` exactly.

The package also verifies a physical equifinality example: `(2,2,2)` and
`(1,1,4)` have the same `(S,P)` and the same equilibrium discharge for every
rainfall level, while their storage partitions differ for nonzero rainfall.

The formalization is intentionally explicit about its scope. It does not claim
that arbitrary rainfall–runoff models are identifiable, and it does not encode
ODE existence or numerical observations. The theorem is a symbolic, exact
result about trajectories (represented by their pointwise jets) satisfying the
model equations. This makes the proof reproducible with rational arithmetic and
separates structural non-identifiability from numerical conditioning.

## Reproduce

With Lean 4.34.1 and the pinned Mathlib revision:

```bash
lake exe cache get
lake build
```

The Python checker in `checks/exact.py` independently checks the same rational
identities and deliberate failure controls.
