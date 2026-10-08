# C17: complete Lean verification added, 2026-10-08

The [complete C17 formalization and evidence](../../formalizations/chromatic-infinite-logconcavity-counterexample/README.md)
now connects the genuine cycle graph, all-q proper-coloring counts, the unique
chromatic polynomial, its actual absolute coefficients, and the exact negative
third log-concavity iterate. This yields a formal counterexample to the universal
infinite-log-concavity conjecture under endpoint-retaining zero extension.

The recorded Lean 4.34.1 run freshly compiled three source modules, audited all
98 owned declarations and their 10,964-node closure, replayed that closure from
an empty trust-zero kernel, and passed the invalid-proof rejection control.
A separate [independent audit](../../formalizations/chromatic-infinite-logconcavity-counterexample/audit/AUDIT_REPORT.md)
found no mathematical gap and independently checked the static evidence and exact
C17 arithmetic. That auditor did not run Lean.

This addition preserves the existing proof, certificates, checksums, manifest,
and earlier release. It does not extend the Lean claim to C12, the infinite
family, the complete cycle classification, or endpoint-deleting variants.
Use the [current public manifest](../../formalizations/chromatic-infinite-logconcavity-counterexample/CURRENT_PUBLIC_MANIFEST.json)
and its [checksums](../../formalizations/chromatic-infinite-logconcavity-counterexample/SHA256SUMS)
for the new formalization package; the old note manifest still describes the
unchanged earlier mathematical snapshot.
