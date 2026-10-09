# All-dimension theorem: compiled and independently replayed

The original run **37956727424** had overall status **failure**, and its original
`RUN.json` is retained without edits. The failure came after all **879 local
modules**, the default Lake build, all original positive/negative controls,
and the **155,787-declaration / 58-root trust-zero replay** had succeeded.
It was confined to `CompletionFormulaControls.lean`: ordinary simplification did
not normalize the rational expression for n=3. The neighboring n=8 and n=9 tests
compiled. The actual final `appt_purity_maximum_formula` theorem was already among
the successfully replayed roots.

`PROOF_STATUS.json` certifies only those successful sub-results; it does not
rename the entire failed run as successful. `literal-evidence.tar.gz` retains
all original module logs/records and complete root/closure/axiom inventories.
The standalone log files are verbatim copies. Every module source hash and
build-log hash was compared with the publication tree before this checkpoint.
All mathematical `APPT/*.lean` sources are unchanged from the checked commit.

A subsequent run must pass the corrected endpoint controls and independently
reject a corrupted proof of the same final theorem before release validation
is complete. No full-formalization Release is created by this checkpoint.

The build combines independently compiled source-bound components, rather than
claiming that every module was freshly compiled on one runner. The uniform
component provenance is explicit in `UNIFORM_CACHE_PROVENANCE.json`; its proof
closure is nonetheless included in the new trust-zero replay.
