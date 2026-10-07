# Source overlap and target tails in quantitative Brenier stability

A derived synthesis note for entries 001, 007 and 008. The complete proof identifies global density-root Sobolev regularity with the linear-overlap interpolation condition for **1 < s < infinity**, including a coordinatewise finite-liminf criterion and an exact strong rooted-Ls first-order limit.

## Read the result

- [Proof PDF](synthesis.pdf) and [editable TeX source](synthesis.tex)
- [Exact statement, assumptions and attribution](REVIEW.md)
- [Full independent proof reconstruction](audit/CORE_PROOF_REVIEW.md), including zero sets, subsequences, boundary jumps and both excluded endpoints
- [Independent audit verdict](audit/B_REVIEW.md) and [imported-result review](audit/IMPORT_REVIEW.md)
- [Dependency map and reading order](DEPENDENCY_MAP.md)
- [57 byte-exact source copies and pinned public URLs](DEPENDENCIES.json)
- [Changes since the reviewed source](RELEASE_DELTA.md)

The independent audit is model-based. No external human peer review, proof-assistant verification, literature-novelty or priority certification is claimed. The existing root-to-overlap sufficient direction, broader density-level L1 limit and derived rearrangement envelope retain their prior attribution and are not counted as new results.

The source copies are a frozen dependency subset, not a complete repository checkout. Historical relative links retain their original repository meaning; use the public URLs in DEPENDENCIES.json to read them in full context.

This is an exact characterization of the interpolation method, not a classification of all sources with stable transport maps. Transport applications still require source and target second moments, the proper-convex/L2 domain hypotheses, and the separate centered-potential estimate (P). Root regularity alone does not establish (P).

## Verify and reproduce

Run from this directory:

    python3 verification/verify_integrity.py
    python3 -O verification/verify_integrity.py
    python3 verification/test_integrity.py --package .
    python3 verification/package_release.py .
    python3 -O verification/package_release.py .
    python3 verification/run_checks.py /path/to/check-results
    bash verification/build_pdf.sh /path/to/pdf-build

Choose output directories outside this package; the integrity check rejects added files. Python 3 and its standard library suffice for integrity and the exact historical checks. The independent numerical diagnostics additionally use SciPy; the tested version is in verification/requirements.txt. The PDF build uses pdfLaTeX, standard AMS/Latin Modern/microtype/geometry/hyperref packages and Poppler. It disables shell escape, uses an isolated temporary directory and fixes SOURCE_DATE_EPOCH. Build logs are local diagnostics and are not part of the release.

Finite exact tests and numerical diagnostics are regression controls, not proofs of the infinite-dimensional theorem or an infinite lower construction. The analytic proof and its reconstruction carry the mathematical argument.

[MANIFEST.json](MANIFEST.json) records every release file except itself and SHA256SUMS. [SHA256SUMS](SHA256SUMS) additionally authenticates MANIFEST.json. The verifier checks the exact file inventory, sizes, hashes, safe paths, source Git-blob identities, protected mathematics and archive contents, with explicit checks that remain active under Python -O. Hashes establish integrity relative to a trusted manifest; they are not digital signatures or mathematical certification. Use verification tools from a trusted copy when checking an untrusted package. The required inventory includes every release entry point and all 57 source paths, so deleting an expected file cannot be legitimized merely by dropping its manifest entry.

The [deterministic source archive](source/transport-source-tail-synthesis-source.tar.gz) contains the complete text sources, audits, source copies and runnable checks, plus SOURCE_MANIFEST.json. It excludes the compiled PDF and outer release manifests. Its member inventory and hashes are in [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json). The source archive alone omits the PDF and outer manifests, so the full-release integrity commands above apply to this complete package; the extracted source still supports PDF rebuilding and regression replay. [BUILD_INFO.json](BUILD_INFO.json) records the tested build and page review.

## Verified packaging and intentional maintenance

The public package_release.py command validates the existing manifests, checksum list, complete required inventory, dependency identities, protected mathematics and source archive before reconstructing the archive in memory. It makes no package changes. Add --output /outside/package/new-source.tar.gz only to write an already verified source archive to a new external file. It never repairs or reseals an invalid release, and rejection leaves the package unchanged.

Intentional maintainer regeneration is a separate operation: verification/regenerate_manifests.py ROOT --acknowledge-no-authenticity. It requires the full fixed inventory and protected mathematical/source checks, but deliberately replaces ledgers for reviewed source edits. It does not authenticate those edits or establish that a prior release was intact. Public verification and packaging never call it. A regenerated release needs a new trusted digest and independent review before distribution.

## Rights

No personal author is assigned. No additional license for newly authored material is granted by this package. Inherited OpenAI material retains its existing Apache-2.0 terms. See [rights and attribution](provenance/RIGHTS_AND_ATTRIBUTION.md), the preserved [upstream notice](provenance/UPSTREAM_NOTICE.md) and [upstream license](provenance/openai_math_LICENSE.txt).
