# Immutable publication record: equal-mass Gaussian simplex theorem

Public release:
https://github.com/mxym/math/releases/tag/gaussian-balanced-simplex-all-k-v1

Published: **8 October 2026, 11:11:44 UTC** (GitHub server metadata).
Locked tag commit: `ebfd90558439afca21babeb7b77c8d8837ea745f`.

The live API reported `draft: false` and `immutable: true`. The tag points
directly to that exact commit. GitHub CLI 2.102.0 verified the generated
signed release attestation; its statement binds
`pkg:github/mxym/math@gaussian-balanced-simplex-all-k-v1` to that commit.
The verified timestamp authority reports 11:11:45 UTC.
The complete verification bundle and result are in
`attestation-verification.json`; `PUBLICATION.json` records the binding
and the public PDF digest.

The frozen commit includes the complete six-page proof, editable sources,
partial Lean proofs, all replay logs, two internal model reviews,
literature comparisons and all-file checksum manifest. Its actual Git
archive was independently extracted and passed package verification and
a fresh eight-root, 18,013-declaration empty-kernel Lean replay. The
second replay's record is `frozen-archive-lean.json`.

There are **no separately uploaded attachments**. The managed connection
accepted Git/API operations but returned HTTP 401 at `uploads.github.com`.
The release therefore uses the locked tag, the source archives GitHub
generates for that tag, and fixed-commit links to the complete package.
The PDF was downloaded through the public tag and its SHA-256 checked:
`f50e07e08e1c9a676b7c5511dcb5a88c4dd18c8b867dcbf5169f62b24bf08872`.

For current independent verification using a recent GitHub CLI:

```sh
gh api repos/mxym/math/releases/tags/gaussian-balanced-simplex-all-k-v1
gh api repos/mxym/math/git/ref/tags/gaussian-balanced-simplex-all-k-v1
gh release verify gaussian-balanced-simplex-all-k-v1 --repo mxym/math --format json
```

The immutable release is a disclosure record, not a mathematical priority
determination. The complete Gaussian analytic theorem is a written proof
using the published Milman–Neeman perimeter theorem; only its eight
algebra/abstract-real-analysis exports are Lean-checked. The internal
reviews are not external human peer review. No award-level assessment or
worldwide first-proof claim is made.
