# Full independent Lean verification, 2026-10-08

The [complete Lean source and verification evidence](../../formalizations/cyclotomic-prime-factor-counterexample/README.md)
now supplements the mathematical counterexample to Billey–Swanson Conjecture 48.
The 11 author Lean files are byte-identical to the source checkpoint at
`616877a1f3ac57ddc23737901581e666b0aabdd1`. That historical checkpoint's pending
status remains part of its original record; this is the subsequent verification
report, not a rewrite of history.

The designated independent verification operator compiled eight mathematical
modules and three author audit modules fresh, audited all 112 owned declarations
(73 named plus 39 generated/private), and replayed their 29,737-node closure in
an initially empty trust-level-zero Lean kernel. The malformed-proof negative
control was rejected. Only `propext`, `Classical.choice`, and `Quot.sound` occur
as closure axioms.

The four formal roots cover the actual cyclotomic product, all-natural-index
unimodality, universal prime-index nondivisibility, the full negation of
Conjecture 48, the centered polynomial identity, and the nonzero-denominator-
cleared q-integer certificate. The latter does not claim a separate formal
rational-function division theorem.

A separate static reviewer checked mathematical meaning, exact bytes, manifests,
closure edges, axiom sets and exact coefficient arithmetic. That reviewer did
not run Lean. The operator used `leanctl.py`; the author's `verify.sh` was not
run end to end. The publication checks likewise do not claim a new Lean run.

The public delivery includes all exact source/log bytes and losslessly encoded
complete graphs. It omits 22 rebuildable compiler outputs and projects two
configuration copies to remove administrative fields. Every original file has
an explicit [mapping](../../formalizations/cyclotomic-prime-factor-counterexample/PUBLICATION_MAPPING.json).
The original execution manifests are retained separately from the
[current complete public inventory](../../formalizations/cyclotomic-prime-factor-counterexample/CURRENT_PUBLIC_MANIFEST.json).
Run `python3 check_public.py` in that directory for the default static check;
`reproduce_lean.py` prepares and runs a fresh execution with existing pinned
Lean/dependency assets.

No worldwide-priority or external-human-peer-review claim is made. No existing
tag or release is changed, and no GitHub CI pass is asserted for this evidence.
