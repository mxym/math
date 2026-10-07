CONDITIONAL CONSERVED QUADRATIC FLUCTUATIONS
7 October 2026; corrected public version 1

Read manuscript.pdf for the full 18-page statement and proofs. This is a
conditional analytic theorem for the three-dimensional excluded-product
hard-sphere gas with smooth compactly supported initial data. It assumes the
operational history package H1-H6 and the existing exactly centered Schwartz
functional input F, both identified at fixed public source commits.

Proved conclusions are true-flow weak process convergence and first-moment
transfer for the conserved thirteen-dimensional quadratic family, together
with pasted prelimit covariance convergence. The intrinsic per-particle
moment corollary is a weak-limit statement. True prelimit covariance remains
open under the stated probability coupling. No full phase-space mean theorem,
generic polynomial functional CLT, or complete Lean proof is claimed.

The full proof is in manuscript.tex and sections/. Symbolic checks verify
selected identities and normalizations; they are not proof-assistant proofs.
The audit/ directory contains model-assisted mathematical reviews. Its
historical report is a documented public derivative. All seven original audit
objects were retained unchanged, but raw historical audit/checker/patch files
are not bundled. Their content hashes are in provenance/original-object-pins.json.
EDITORIAL_CHANGES.md identifies the notation correction and metadata edits.

OFFLINE REPLAY FROM THIS DIRECTORY
  python3 checks/verify_package.py
  python3 -O checks/verify_package.py
  python3 checks/strict_check.py
  python3 -O checks/strict_check.py
  python3 checks/optimization_regression.py --output ../regression-replay.json
  python3 build.py --verify-repeat

Put any optional replay output outside this directory, or remove it before
exact-inventory verification. A convenient external destination is ../regression-replay.json.
Python checks require Python 3 and SymPy. The audited toolchain used Python
3.12.14, SymPy 1.14.0, pdfTeX 1.40.26 (TeX Live 2025/dev/Debian), and Poppler.
The PDF requires the standard packages declared in manuscript.tex. The build
changes no system files, enables no shell escape, and installs no dependency.
If the system format/font-map cache is absent, a temporary local format loads
english hyphen.tex and the standard Latin Modern and AMS font maps.
Two independent three-pass builds must match byte-for-byte in this toolchain.
No byte identity across different TeX/font distributions is promised.

PINNED INPUTS
sources/ contains exactly the 32 files from the audited verification inventory,
with original commit/repository-relative layout. All byte counts, SHA-256,
Git-blob SHA-1 and literal labels are checked offline. This is the audited
verification cache, not the complete independent F/V/U build distributions.
Their exact public locations and the 82-entry source-label map are in provenance/.
Equality with the newer comparison commit is a preserved historical manifest
assertion, not a new network validation.
Optional fresh download uses ordinary verified HTTPS:
  python3 checks/strict_check.py --fetch-sources ../new-source-cache

RELEASE INVENTORY
PUBLIC_FILES.json is the explicit publication whitelist. package-manifest.json
hashes every whitelisted file and is self-excluded to avoid a circular hash.
The checker rejects extra files, duplicate rows, unsafe paths and symlinks.
Only Python bytecode/cache files are ignored. Generate delivery outputs outside
this directory:
  python3 package.py ../delivery
The deterministic tar.gz contains the full source, PDF, audits, source cache
and evidence under notes/conserved-quadratic-fluctuations/. The readable patch
contains every UTF-8 file; apply it in an empty directory with git apply, then
run build.py --verify-repeat to reconstruct the binary PDF. Archive and patch
replay results and output hashes are recorded separately with the release.
