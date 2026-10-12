# Independent exact ancillary checks and manuscript binding

Successful CI run **38030907207**, checked source
**abf483af25b252f8ddaee91c8612c9e678cd8ac4**. The workflow response, job records,
and literal test reports/logs are retained here. The uploaded proof, LaTeX,
PDF and manifest were byte-compared with the publication tree before retention.
All twelve pinned root proof/manuscript/tool files matched.

This is **not Lean verification or external peer review of the analytic theorem**.
The dimension-uniform proof is in `PROOF.md`; these checks support particular
algebraic and finite quantum identities. The final proof is deterministic and
does not invoke the companion's random-projector/concentration argument.

The exact checker covers six full rational Choi matrices and their partial-
transpose conjugates; eight local-channel systems and 25 embedded Bell inputs;
110,640 integer packing cases, including the d=1 and nondivisible cases;
three symbolic escort identities and 3,750 exact hinge checks. The inherited
type routine checks 710 type bounds, 154 independent type cardinalities and
1,296 mode comparisons. No floating-point optimizer is used.

The actual checker passes normally and with Python assertions disabled.
Seven deliberately changed source programs are rejected with the specified
mathematical diagnostic: incorrect antisymmetric denominator, omitted input
partial transpose, missing target-dimension square, missing leftover Kraus
weight, wrong minimum Bell dimension, incorrect squared-fidelity convention,
and wrong escort sign. An unrelated exception or timeout does not count as
successful rejection. The source-corruption checks themselves run with -O.

Earlier branch commits describe a cPPT-only draft. The checked source above
is the strengthened proof of the common LO/LOCC/cPPT capacity and exponent.
Earlier draft success records are not substituted for this final source check.
