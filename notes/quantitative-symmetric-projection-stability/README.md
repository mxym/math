# Effective stability at the symmetric projection-cone endpoint

This research supplement gives a complete English proof for centrally symmetric,
full-dimensional convex bodies, with no regularity or discreteness hypothesis:

\[
D(K,\mathcal E_d)-1
\le d^{15}\bigl(\tfrac12-a(K)\bigr)^{1/(6d)},\qquad d\ge3.
\]

Here `E_d` is the entire class of affine Cartesian products of symmetric
one- and two-dimensional factors. The article also computes a corner-truncated
cube family with deficit of order `t^d` and distance at least `t/(5d^2)` from
that entire class. Consequently a universal fixed-dimensional power above
`1/d`, and any positive dimension-independent power, are impossible.
The optimal exponent between `1/(6d)` and `1/d` remains open.

## Contents

- `paper.pdf`: typeset article in the complete bundle; `paper.tex` and
  `paper.md`: complete editable English sources in both archives.
- `DEPENDENCIES.md` and `DEPENDENCIES.json`: exact pinned entry005 v2–v4
  statements, byte hashes, provenance, and the classical inputs.
- `LITERATURE.md`: primary-source comparison with explicit full-text limits.
- `AUDIT.md`: scope of the two passed independent model mathematical audits.
- `VERIFICATION.md`, `code/`, and `results/`: exact regression sources,
  portable replay instructions, and recorded output.
- `BUILD.md` and `PDF_QA.md`: clean rebuild and all-page visual inspection.
- `MANIFEST.json` (complete bundle) or `SOURCE_MANIFEST.json` (source archive):
  sizes and SHA-256 hashes of the shipped files.

The upper-end theorem does not import the lower-end simplex modulus or the
v5 spectral recursion. Inherited repository manuscripts are linked and hashed,
rather than redistributed. No publication, external peer review, formal
verification, or novelty determination is asserted.

The archive tree is additive under
`notes/quantitative-symmetric-projection-stability/`. It contains no changes to
the numbered entry005 versions or repository catalogue files.

## Rebuild the article

The Markdown-to-LaTeX build requires Pandoc and a standard TeX Live installation
with pdfLaTeX, AMS packages, `mathtools`, `mathrsfs`, `lmodern`, `microtype`,
`xurl`, `fancyhdr`, and `needspace`. From the extracted package, run:

```sh
sh build.sh
```

This regenerates `paper.tex` and `paper.pdf`; intermediate files go to
`build/typeset/`. The shipped LaTeX source can also be compiled directly with
pdfLaTeX twice in a separate directory. The recorded deterministic build and
tool versions are in `BUILD.md`.

## Replay the exact checks

Python 3.10 or newer and its standard library suffice. No repository checkout,
network access, or third-party Python package is required:

```sh
python3 code/verify.py --output-dir build/verification
```

The three exact scripts run ordinarily and with `python -O`, and their outputs
must agree byte for byte. New output is separate from the shipped reference
reports. `VERIFICATION.md` documents optional inherited-check replay with an
explicit external checkout pinned to commit
`6785c1c830f8e19e2eb07b0bb89f4d475a8b154a`, and the preflight and packaging
regressions. These finite checks supplement the written proof; they do not
formally certify the general theorem.
