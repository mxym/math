# Literal verification evidence

`kernel-r2` is a completed fresh Lake build, separate 26-module source build,
206-root audit, 53,415-declaration empty-kernel trust-zero replay, and three
rejected source mutations. Only propext, Classical.choice and Quot.sound occur.
The precise toolchain binary hash, dependency source checks and all source and
object hashes are in verification.json. The compressed closure list expands
to the literal replay output; SHA256SUMS binds the retained evidence files.

SOURCE_BLOBS.used.json preserves that run's exact manifest. The subsequent
addition of fetch_cache.sh to the manifest does not change any Lean source,
verifier, audit root, toolchain or dependency. A second clean run is being
recorded separately; no old development log is presented as that run.

The Windows/WSL run is a source-isolated kernel check on the authorized device,
not an independent human review. The GitHub Actions workflow is configured for
an independent hosted runner; no successful hosted run is claimed here until
its actual result has been retrieved and recorded.
