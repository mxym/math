# Clean archive build

Date: 8 October 2026.

A release-file-only archive was extracted into a fresh temporary directory, outside the manuscript's original build tree.

Results:
- Every packaged SHA256SUMS entry passed before building.
- `verify_package.py` passed before and after the clean build.
- `./build.sh` succeeded using only the extracted TeX/package files and installed TeX dependencies.
- Final clean TeX log had no overfull/underfull boxes, undefined references, or warnings.
- The clean PDF has 17 pages.
- `pdftotext -layout` output is byte-identical to the visually inspected release PDF's text.

The prepared release PDF hash is `1897d4059800e2a7612d65f816c0eb274d844375aebcf1f551144eec56c4fc05`.
The separate clean-build PDF hash is `2e0554dbc0bf1ad133bfbacc823b4b608b457cc5b04a139620c926d37ea1f906`; timestamps account for permitted binary variation. The release retains the original visually inspected PDF.

Only this build receipt was added after the clean build. The mathematical TeX, source snapshots, and reader PDF were not modified. This is build reproducibility evidence, not mathematical proof certification or Lean validation.
