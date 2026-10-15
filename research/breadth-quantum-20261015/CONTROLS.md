# Reproduction boundaries

All outputs must use fresh absolute paths. Existing evidence is preserved.
The portable exact programs require Python and SymPy; the recorded run used
Python3.10.12 and SymPy1.9. The finite numerical environment additionally used
NumPy1.21.5 and SciPy1.8.0. No Lean verification is claimed.

From this directory, replace /ABS/NEW_*.json with unused output paths:

```
python controls/exact_route_controls.py --output /ABS/NEW_exact.json
python controls/all_copy_route_controls.py --output /ABS/NEW_allcopy.json
python controls/certify_structured_polys.py --input STRUCTURED_MEMORY3.json --output /ABS/NEW_interval.json
python controls/orthogonal_two_copy_control.py --output /ABS/NEW_orthogonal.json
python controls/signature_completion_control.py --output /ABS/NEW_completion.json
```

EXACT_REPRODUCTION_CHECKS.json records fresh author reruns of the first three
from prefix source, with every non-timestamp output field compared exactly.
The last two sources are byte-identical copies of the just-executed exact
controls. None is an independent review or full N0 proof.

Other exploratory scripts preserve their actual execution sources, including
private workspace paths and pure-function dependencies. They are not a
path-independent turnkey reproduction package. Do not blindly run their
top-level blocks against existing evidence. Initial scripts with failure
labels intentionally preserve rejected implementations or output mistakes.

ARTIFACT_MANIFEST.json binds the current prefix files except itself. The
private preservation bundle also keeps original program failures, numerical
arrays and privately cached primary sources; third-party full text is not
added to the public research prefix. No raw numerical minimum is a certified
global lower bound.
