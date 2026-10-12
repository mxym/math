# Independent audit — 7 October 2026

The 68 exported finite/scalar theorems passed a clean project rebuild using Lean
4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`), Lake
`5.0.0-src+5045d00` and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The build reported 2,321 Lake jobs;
retained dependency artifacts contribute to that count. All project and curated
upstream proof modules were recompiled.

All 68 full signatures and literal axiom audits passed. Their axiom union is
`propext`, `Classical.choice`, `Quot.sound`; no custom/sorry/native-proof axiom
appears. An independent compiler inventory found 158 declarations, including
136 theorem declarations and 22 definitions. The difference from 68 is generated
and private helpers. Direct traversal of checked types and stored bodies visited
24,789 constants, with no missing or reachable unsafe/partial proof dependency.
Generated partial runtime implementations are excluded as traversal roots; any
unsafe dependency reached from a safe proof root is still rejected.

The normed/cofactor results derive balance from a zero-sum relation and supplied
unit norms on active vectors; they do not assume the balance inequality. Semantic
controls include nonzero normalized examples, inactive vectors without unit
norms, strictness, singular cofactors, and exact counterexamples to removing the
relation or weakening normalization. The normalized dimension-zero cofactor
hypotheses are infeasible; positive-dimensional examples are nonvacuous.

Reporting guards check reviewed dependency revisions/origins and source
cleanliness, remain active under Python optimization, include protected theorem
declarations, reject proof escapes, and require fresh Lean signature/axiom output
before generating coverage. A compiler inventory supplements the lexical source
inventory. `scripts/check_controls.py` provides reproducible negative reporting
and semantic controls. All 32 negative controls and 7 positive checks passed;
their commands, exit codes and expected diagnostics are in
`logs/controls-summary.json`. Nonzero exits in individual negative-control logs
are the intended rejection results.

The verified scope is finite Rademacher mathematics, its coefficient-defect and
normed-relation extensions, determinant identities, weighted finite Jensen/defect
mechanisms, elementary scalar inequalities, explicit scalar recurrences and
curated finite/scalar upstream reuse. The complete theorem map gives assumptions
and application gaps. Constructing a convex-body Minkowski norm and boundary-unit
normalization, measure integration, exposed-point rigidity, geometric
classification/stability, the coefficient-distance bound and global optimality
remain outside scope.

The trust boundary includes the official Lean compiler/standard library and
official pinned third-party `.olean` cache. This is a clean project rebuild,
without a full dependency/compiler-from-source rebuild or an external kernel
checker. Axiom/body traversal is a dependency audit, not a re-typecheck of every
imported cached proof. The build log's local path was normalized for distribution;
all theorem signature and axiom output remains verbatim.
