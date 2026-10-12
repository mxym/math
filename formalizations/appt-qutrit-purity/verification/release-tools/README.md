# Source-locked release export

`package.py` exports deterministic gzip/tar archives from an explicit Git commit.
It refuses to export a complete release unless the final runner and its GitHub
workflow both report success, every required build/control/replay stage passed,
and the exact pinned source inventory equals the Git-stored publication sources.
It then reopens the source archive and verifies all pinned file hashes.

This is a packaging gate, not an alternative to Lean proof verification.
`negative-control.json` records rejection of the real earlier failed workflow
37956727424 without creating any archive. The successful release manifest records
the separately verified source commit, publication commit, toolchain, proof scope,
axioms, build/replay counts, and source/evidence asset hashes.

```sh
python3 verification/release-tools/package.py --repo /path/to/math \
  --commit <fixed-publication-commit> --evidence /path/to/successful-evidence \
  --output /path/to/release-assets
```

The evidence directory must contain the original `RUN.json`, the successful
`workflow-run.json`, and the retained literal logs. GitHub Release publication is
separate; this script does not create or modify tags, releases, or remote assets.
