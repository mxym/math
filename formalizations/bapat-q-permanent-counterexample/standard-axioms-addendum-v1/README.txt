Separate axiom-signature hardening addendum, version 1.

This adds an explicit signature check to the recorded Bapat verification.
It does not identify a defect in the frozen mathematical proof or replay.
Neither original archive, original checker, original logs nor Bapat source
was rewritten. No Bapat mathematical module was recompiled for this addendum.
The successful addendum imported BapatN200Counterexample from the exact frozen
fresh-run build, with that directory first in LEAN_PATH.

Actual loaded propext, Classical.choice and Quot.sound were exported with pp.all,
complete raw expressions, universe parameters, axiom kind and safety flags.
Expected expressions are constructed independently from the pinned Lean source
signatures. Source git-blob hashes match the fixed commit; see upstream-signatures.

Comparison: normalize only binder names and universe-parameter names (by their
parameter-list indices), then use Expr.equal. Unlike ordinary BEq Expr, this
preserves binder visibility. No type unfolding, definitional equality, unresolved
metavariables or trusted types supplied by the inspected declarations are used.
All three complete expected expressions are in sources/StandardAxiomGuard.lean.

Actual checks: the three loaded Bapat signatures PASS. Thirteen mutations are
rejected: False type, extra universe, unsafe flag and wrong declaration kind for
each axiom, plus an implicit-to-explicit binder change for propext. The separate
small smoke replay has 3 owned declarations / 14 closure declarations, from an
empty trust-zero kernel. The original invalid-proof kernel negative control
also PASSed. This is not another replay of the full 22371-declaration closure.

OwnedAudit.standard-axioms-v1.template.lean is a NEW checker version, with the
guard embedded and called before replay. The original template remains untouched.
It can replace the template in a NEW verifier installation/copy for future runs;
never silently substitute it into a frozen historical evidence directory.

Reproduce with Python3 and the existing exact toolchain/dependency artifacts:
  sha256sum --check SHA256SUMS
  python3 run_supplement.py --environment-json /local/environment.json --bapat-build /restored/full/fresh-verification/build --output /new/addendum-output
The output directory must not exist. Adapt only local root paths in a COPY of
 environment.example.json. The runner performs no downloads, installation,
dependency rebuilds, credential operations or GitHub writes.

Public logs/metadata have mechanical path substitutions listed in FILE_MAP.json;
their original and transformed hashes are both recorded. Mathematical source,
expected/actual raw type expressions and new checker bytes are unchanged.
Rebuildable supplement .olean files are omitted with original hashes.

Original checker SHA256: 8e3abe80fce80e182c5876d81a87a0508f2aa7721ba5638d93b562c673a2234b
