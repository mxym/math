# Publication-only checks

The portable static checker and preparation helper were exercised on 2026-10-08.
See `audit/publication-tests-result.json` for the recorded successful controls.
Run `python3 -B test_publication.py` to repeat them using temporary copies.

These tests execute the complete 75-file projection inventory, historical-manifest bindings,
portable declaration/closure/axiom/source/command consistency audit, and independent
exact C17 reconstruction. Negative controls reject a changed source, unexpected
file, duplicate manifest path, truncated closure, optimized Python, existing output directory,
output inside the snapshot, missing toolchain, and audit output inside the snapshot.

The preparation test uses a synthetic executable only to detect accidental
execution. It is never invoked. The test checks that all pins, modules, roots,
source hashes, and verifier bytes are retained, that paths with spaces work,
that no archived owned binary is copied, and that the public snapshot remains
byte-identical. This is not a Lean compile, semantic audit, or new kernel run.
