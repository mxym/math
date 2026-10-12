# Quadratic-dimensional simplex stability: final-copy audit

Date: 7 October 2026. Verdict: **PASS. No required fixes.**

This independent analytic model review covers the exact publication copy of `notes/quadratic-dimensional-simplex-stability/`, including all three proof files, imported arguments, source pins, public-copy fidelity, archive integrity, and finite-check replay. Neither this release nor the companion polynomial-dimensional release was modified by the review.

## Exact release identity

- Public payload: 40 files; 680,548 bytes in total.
- Strict manifest: 37 payload files, excluding `MANIFEST.json`, `SHA256SUMS`, and `source.zip`.
- `source.zip`: 342,836 bytes; 39 entries; SHA-256 `d79b07df28ad259f6f02c396335a69a9a3bff98b0a98dfd17d89e5199d4b980d`.
- `MANIFEST.json`: SHA-256 `f84d3d1989c39333159f99d8fa22a7e2e58385f6bc4911f13d4e815bc867e486`.
- `SHA256SUMS`: SHA-256 `ea714e1b27b27d264740149db32fd052c443a73303536e626bba634f56b78115`.
- Transport ZIP: 689,448 bytes; SHA-256 `1b9f50f00fbc529fd4b47f96be91cc3e1184dc67869e7698943fec2182661a19`.

The supplied final handoff agrees with these independently measured bytes. The verdict applies to this exact release, not to later self-consistent edits.

## Mathematical findings

For every integer $d\ge3$, every full-dimensional convex body $K\subset\mathbb R^d$, and every prescribed maximum-volume inscribed simplex $S$, with its own original centroid, the proof establishes

$$E(K,S)\le G_d e(K)^{1/(d-1)},\qquad
G_d=16(d+1)^2[3d^2(d+1)^3(d+2)]^{1/(d-1)}\le4096d^2.$$

The coefficient is asymptotic to $16d^2$. The deficit uses the original projection-body/pyramid invariant; it is not replaced by a polar-projection invariant. The actual simplex-truncation source retains the sharp exponent $1/(d-1)$.

The review checked the complete proof chain: maximum-simplex existence and replacement maximality; centering at the prescribed simplex; the norm $h_{K-K}$ and dual gauge; the actual cone-law pushforward and first absolute determinant moments; the exact first-moment defect ratio $D/B=(d+1)e/[1+(d+1)e]$; integrated anchor selection, including singular tuples; intrinsic dispersion; multiplicative barycentric weight correction; Minkowski conversion with the unnormalized relative projection denominator; exact affine caps; determinant comparison; column matching; and the maximality bootstrap for every prescribed maximum.

The local estimate $8(d+1)\delta^{1/(d-1)}$ includes its gate $\delta^{1/(d-1)}\le1/[16(d+1)]$. The global quadratic bridge, zero-deficit case, endpoint $e=1/H$ with $H=3d^2(d+1)^3(d+2)$, strict anchor gates, and large-deficit universal bound all pass. Translation back retains the original centroid. No mathematical repair or changed hypothesis is required.

## Fidelity and dependency findings

The frozen mathematical basis has 35 archive members, 119,723 bytes, and SHA-256 `e4692f094731baa994ae10a2d81bc0b50334ed65bb5e5f676c3e48d5b21fe978`. Every member agrees with the supplied frozen directory.

All 36 ordered editorial operations in seven derivatives replay exactly. All 64 line-segment records match the original and public bytes. The 18 unchanged-file records, 13 public source pins, and 11 original-to-public audit source mappings pass. The mathematical code of the quadratic checker is unchanged; the other four regression scripts are byte-identical. The three proof files and the full original audit retain their mathematical content.

All six historical proof, provenance, and license files carrying public commit URLs were independently fetched at those exact commits and matched byte-for-byte. The actual polynomial-dimensional companion payload was compared directly: shared mathematical arguments agree; the imported polynomial and weighted-anchor files differ only in contextual wording and relocated links. The square-pyramid lower bound and four historical mathematical sources are byte-identical between the releases.

All 41 checked new-proof and release Markdown links resolve. Two contextual links retained inside the byte-identical historical v3 manuscript refer to its original repository neighbors; this is explicitly disclosed in `SOURCE_GUIDE.md` and does not leave an unbundled dependency in the new proof. The cone-law import is correctly identified as Section 4 of the v3 manuscript and Section 3 of the imported polynomial refinement.

No undisclosed private locator was found in the publication payload. The checker's explicit prohibited-pattern test data is not a private source locator. The attribution notice and applicable upstream license remain unchanged. The review does not certify novelty or priority, assign a new blanket license, or claim an optimal dimension order.

## Reproduction and adversarial evidence

Independent inventory, checksum enumeration, archive-member byte comparisons, CRC checks, safe member paths, and deterministic archive reconstruction all pass. The supplied packager also reproduces the exact source ZIP.

All five regression scripts reproduce their recorded outputs in five complete replay configurations:

1. Normal runner.
2. `-O` runner.
3. `-O` runner with `PYTHONOPTIMIZE=2`.
4. Clean source-ZIP extraction, normal runner with `--extracted`.
5. Clean extraction, `-O` runner with `--extracted`.

The runner uses isolated, unoptimized checker subprocesses, preserving assertion-based checks even when the parent is optimized. The exact quadratic evidence records nine actual convex bodies, 696 projection directions, 36 vertex-set maximum simplices, 400 rational relative-deficit comparisons, and the matching endpoints. These finite checks supplement the analytic proof; they do not prove its universal quantifiers.

Thirty hostile controls were each rejected under normal Python and `-O`, for 60 successful rejection tests. Nineteen controls changed a proof, pinned import, audit, or checker and then successfully regenerated the manifest, checksums, and ZIP with the legitimate packager. All 19 were still rejected. Thus changing these files cannot pass by merely regenerating the manifest. Other controls cover missing/duplicate/reordered inventories, missing/duplicate checksums, unlisted files, symlinks, a deleted proof, and a malicious archive inventory.

To reproduce the ordinary release checks from its directory:

```sh
python check_package.py
python -O check_package.py
python verify.py
python -O verify.py
PYTHONOPTIMIZE=2 python -O verify.py
```

For a clean source-ZIP extraction, add `--extracted` to either checker or runner. Hashes establish byte identity against a trusted copy; they do not authenticate authorship or protect against an attacker replacing the checker and all trust records together.

## Scope limits

This is a complete readable Markdown release; no new PDF is required for completeness. The separate at-most-$d+2$-vertex construction, Euclidean-radius construction, old anisotropic work, and open-route material are not covered by this verdict. The retained square-pyramid example supplies the previously established asymptotically linear lower obstruction. A uniform linear upper bound and the optimal dimension order remain unproved here.

This is independent analytic model review with finite computational regression evidence. It is not human peer review, Lean or other proof-assistant verification, a novelty certification, or proof by finite testing. No publication or repository write was performed by this audit.

The accompanying evidence and inventory are newly authored publication summaries using release-relative identifiers; they are not locator-normalized copies of execution logs. The release's existing source/public mapping and sanitization ledger remain unchanged and were verified in full.
