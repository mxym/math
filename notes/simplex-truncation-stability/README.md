# Exact exponent obstruction for lower-end simplex stability

Additive research supplement to entry 005, 7 October 2026. AI-assisted mathematical research; no peer-review, proof-assistant, priority, or optimal-universal-bound claim is made.

## Main conclusion

For every fixed dimension d >= 3, a stability estimate in a power of the projection-cone defect e(K) = a(K) - 1/(d+1) cannot have exponent greater than 1/(d-1). This applies both to affine Banach–Mazur distance from the class of all simplices and to centroid containment using either the best or every maximum-volume inscribed simplex.

The example is K_t = {x_i >= 0, t <= sum x_i <= 1}, 0 < t < 1. Its invariant is calculated exactly, and all its maximum simplices are classified, including those with a nonvertex bottom-face apex. The necessary endpoint constant for the every-maximum-simplex estimate is at least

(d+1) ((d+1)^2 / (d(d-1)))^(1/(d-1)).

The note also proves the exact Minkowski asymmetry d-t and a dimension-three Rogers–Shephard deficit calculation. These calculations identify obstructions to direct linear bridges between the corresponding deficits.

## Scope

The universal upper estimate at exponent 1/(d-1), the exact unrestricted Banach–Mazur distance for this family, and optimal universal constants are not proved. The previously released quantitative supplement supplies the separate lower bound 1/[d(d^2+2d+2)] on admissible powers. Combining it with this obstruction gives an interval for the unknown best exponent; it does not close that interval.

The all-dimensional conclusions rest on the written proof. Finite exact calculations are regression tests, not a proof of the infinite family. Truncation as a sharpness method is established prior work and is cited explicitly.

## Contents

- [proof.pdf](proof.pdf): eight-page mathematical note
- [proof.tex](proof.tex): editable English source
- [proof.txt](proof.txt): text extracted from the PDF with layout retained
- [INDEPENDENT_AUDIT.md](INDEPENDENT_AUDIT.md): independent mathematical and implementation review, with scope limits
- [VERIFICATION.md](VERIFICATION.md): completed checks and reproducibility details
- [EDITORIAL_CHANGES.md](EDITORIAL_CHANGES.md): complete publication-edit diff; mathematical environments were preserved verbatim
- [check_exact.py](check_exact.py), [exact_certificate.json](exact_certificate.json), and the two exact-run logs: unchanged received checker and reproduced outputs
- [sources/SOURCE_MANIFEST.json](sources/SOURCE_MANIFEST.json): exact upstream paths, commits, byte sizes, and SHA256 hashes for archived dependency snapshots
- [NOTICE.md](NOTICE.md): attribution and retained upstream notices
- [PACKAGE_FILES.txt](PACKAGE_FILES.txt): exact package whitelist, including the source archive
- [MANIFEST.json](MANIFEST.json): byte hashes of all package payload files, except the manifest and archive to avoid self-reference
- [source.zip](source.zip): clean source-and-results archive; excludes itself and all build/cache files

## Reproduce

Requirements: Python 3 with its standard library; a TeX Live installation with pdfLaTeX, geometry, AMS packages/fonts, booktabs, xurl and hyperref; and Poppler pdftotext. The tested toolchain is recorded in VERIFICATION.md. No network access is needed.

From this directory:

```sh
sh replay.sh
sh build.sh
python3 check_package.py
python3 -O check_package.py
```

The checker is replayed in build/replay because it writes its certificate next to its own file. The two Python modes must produce identical certificates and logs, including the archived copies. Expected totals: 1,380 facet minors, 5,385 vertex-simplex subsets, 1,760 barycentric checks, 125 independent Leibniz determinant crosschecks, and five exact 3D difference-body volumes reconstructed from 70 facets and 160 triangles.

The PDF build fixes timestamps and suppresses the path-dependent PDF trailer identifier. A writable local TeX fallback is included for an installed but unconfigured Debian TeX tree; it installs nothing. Identical PDF bytes are expected with the tested toolchain, while other TeX/Poppler versions may change rendering or extraction. Such byte changes do not by themselves contradict the mathematics.

To intentionally regenerate the package after reviewed edits, run `python3 make_package.py`, then rerun `python3 check_package.py`. This refreshes the manifest and deterministic archive from the fixed whitelist. It does not publish anything. After extracting source.zip, run `python3 check_package.py --extracted` before rebuilding; the archive deliberately does not contain a second copy of itself.

## Pinned sources

The entry005 v3–v5 snapshots use commit [31e3d8a37e4a3051a7f5a2535be1c75642e15bcc](https://github.com/mxym/math/tree/31e3d8a37e4a3051a7f5a2535be1c75642e15bcc/preprints/005-simplex-product-optimum). The quantitative supplement uses commit [6785c1c830f8e19e2eb07b0bb89f4d475a8b154a](https://github.com/mxym/math/tree/6785c1c830f8e19e2eb07b0bb89f4d475a8b154a/notes/quantitative-projection-simplex-stability). Their contents were also checked unchanged at public repository commit 3360e7191cf564a46d09edcbfbd107c9178bd98f. The v2 derivation and upstream notices are additionally included at that checked commit. External literature is cited in the note; copies of those third-party papers are not redistributed here.
