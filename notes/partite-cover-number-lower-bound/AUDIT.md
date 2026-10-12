# Verification and dependency scope

The complete proof is `paper.md`. Theorem 2 is independent of external
theorems: incidence counts, pairwise intersection, within-part disjointness,
averaging, pairing and a completed square suffice. Theorem 1 additionally
uses Sivashankar, arXiv:2606.24878v2, Lemma 2 and its maximum-degree-four
consequence in Section 4. Degree-five peeling also follows that source's
framework. The new ingredient is the partite residual estimate and its
combination with these inherited estimates. The degree-three lemma's full attributed proof is
restated in the appendix and was inspected against the source. No Kahn
edge-colouring theorem or OpenAI/math theorem enters either result.

Self-review covered empty residuals, negative intermediate lower bounds,
arbitrary part widths, degree changes during peeling, maximal versus maximum
matchings, the degree-four deletion argument, witness distinctness, the
coloured-graph cases, integrality of the contradiction parameter, and the
two cases at q=2r. The written factorization includes all additive constants.

`checks/check_exact.py` uses integer/rational arithmetic. Polynomial identities
are checked by coefficient dictionaries, with an intentionally damaged
identity required to fail. Diagnostic scalar samples and finite hypergraphs
do not stand in for the general proof. Exact cover searches enumerate vertex
subsets, including the empty cover; no external solver or floating point
is used. Explicit `require` calls remain active with Python optimization.

The nine Lean exports check incidence slack, residual interpolation,
peeling algebra, the completed square, the independent bound, threshold
factorization, the strengthened bound, and both degree-three scalar
contradictions. None uses an unproved placeholder or native evaluation.
This is partial algebra formalization. The combinatorial statements and
their reduction to the scalar hypotheses remain written proofs.

`verify.py --lean` checks the frozen payload hashes, reruns normal and
optimized exact checks, kernel-checks the Lean source and compares its
printed dependencies against the recorded output. Package integrity is
not a mathematical proof. The PDF is a presentation of `paper.md`.

Literature checking was performed by an explicitly requested separate
Luna agent and is limited to the sources stated in the comparison report.
It is independent of the proof construction but does not validate the
proof or establish priority. No external mathematician has reviewed this
note. The asymptotic improvement and its dependencies are stated precisely;
no claim of solving the unrestricted Ryser or Erdős--Lovász problem is made.
