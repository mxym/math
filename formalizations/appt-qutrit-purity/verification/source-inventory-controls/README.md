# Source-inventory positive and failure controls

This is a test of `scripts/source_manifest.py`, not a substitute for Lean kernel
verification. It creates a temporary fixture, never changes the real proof tree,
and checks two positive cases (original and restored) and six intentional errors:
changed mathematical source, changed replay support, missing mathematical source,
an additional unlisted source, a changed toolchain pin, and an altered checksum.
Each invalid case must exit with code 1 and the exact inventory-mismatch diagnostic;
a timeout or unrelated error does not count as successful rejection.

From the package directory:

```sh
python3 verification/source-inventory-controls/check.py
```

`RUN.json` contains literal outputs and the checked inventory-program hash.
The temporary-directory location is selected by the system or `TMPDIR`.
These tests do not add hypotheses or dependencies to any mathematical theorem.
