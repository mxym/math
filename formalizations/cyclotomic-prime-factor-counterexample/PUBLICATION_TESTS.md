# Public-copy validation performed on 2026-10-08

The publication preparer ran these checks against the public staging copy:

- `python3 check_public.py`: PASS for complete public inventory/hashes and the
  portable static evidence audit, including reconstructed full dependency graphs.
- `sha256sum -c SHA256SUMS`: PASS for every current public checksum entry.
- `unpack_evidence.py` into a temporary external directory: both output files
  matched the original full graph files byte for byte.
- `reproduce_lean.py` without `--run`: prepared an isolated temporary workspace.
  Every retained environment field and verification parameter matched the
  supplied profile, except the explicitly relocated operational paths. Copied
  checker/control bytes matched the originals. No toolchain was executed.
- Refusal tests: existing output directories and an unpack destination inside
  this evidence snapshot were rejected without overwriting files.
- Python source syntax was parsed successfully.

These are public-copy, unpacking and wrapper-preparation checks. The publication
preparer did not install Lean, compile the proofs or execute kernel replay. The
recorded Lean run belongs to the independent verification operator named by role
in the README and original execution assessment. `--run` in the new portability
wrapper was not exercised in this publication workspace, and the author's
`verify.sh` was not run end to end by the recorded operator.

Hashes of omitted compiled binaries were checked against historical manifests
and the publication mapping only; this public-copy check does not claim to have
retrieved those omitted binary bytes from GitHub.
