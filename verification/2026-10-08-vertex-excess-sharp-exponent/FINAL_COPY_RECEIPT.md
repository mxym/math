# Final-copy receipt: vertex-excess exponent manuscript

Date: 8 October 2026.

## Disposition

**PASS. No blocking transcription, mathematical expansion, formula-conversion, or verification-status error found.** The expanded English manuscript faithfully presents the theorem and sharpness argument covered by the preceding traditional review. No correction is required for the reviewed copy within this limited final-copy scope.

This receipt is a final-copy/source-fidelity check, not a repeated full theorem audit, professional peer review, new Lean validation, or priority determination. It relies on the scope of the original independent traditional report, whose unchanged SHA-256 is `d638e1ebf4505f480d99c08c21a2012fb36f0e021cd86d828d142effd5df283b`.

## Exact objects reviewed

- Package directory: `research_math/vertex_excess_manuscript_20261008/`.
- Reader PDF: `vertex_excess_sharp_exponent.pdf`, 17 pages, 393130 bytes.
- PDF SHA-256: `1897d4059800e2a7612d65f816c0eb274d844375aebcf1f551144eec56c4fc05`.
- Archive: `research_math/vertex_excess_manuscript_20261008.tar.gz`.
- Archive SHA-256: `f34c5db90da4c16b625ea9cdf885cb20b231e9593c3fee6801476473a7d24a50`.

Both supplied hashes were independently recomputed and matched.

## Mathematical-copy checks

I read `main.tex` and all nine section files against the frozen proof, its separately reviewed sharpness addendum, and the previous referee findings.

1. **Literal theorem and invariant.** Equations (1.1)--(1.4) preserve the actual projection-body pyramid defect, the dilation excess rather than dilation factor, the sharp exponent 1/min(r,d-1), H_d=3d^2(d+1)^3(d+2), T_(d,r)=min{64(d+1)r,16(d+1)^2}, and the exact limiting coefficient. The quantifier is every prescribed maximum-volume inscribed simplex, with the same simplex's original centroid.
2. **Cone and projection step.** Positive integer N,m, the N=1 case, the affine section identification, binomial mixed-volume normalization, vanishing of higher mixed terms, radial enlargement, all ray-collapse cases, and actual-facet counting are faithfully retained. The separate all-directions sharpness formula is included with homogeneous brightness, removing the previous nonunit-direction ambiguity.
3. **Expanded assignment proof.** Section 3 preserves the determinant sign budget D=B-A, the number (d+1)(d+2)/2 of witnesses, the restriction to nonsingular tuples in volume-weighted selection, the clipped seminorm estimate, the coefficient R_0(d+1)(d+2)D/B, and the D=0 endpoint. No silent singular-tuple division or extra law hypothesis was introduced.
4. **Expanded finite-law enclosure.** The raw facet/pyramid identities, iid factorials, a=B/(nA), actual defect conversion, R_0=n, C=n^3(n+1), same-anchor simplex, actual-facet incidence, multiplicative probability correction, finite first mixed-volume inequality, and coefficient 3d^2 all agree with the checked chain. No compact-limit Main is used to assert facet incidence.
5. **Retention.** Both 64nr and 16n^2 bounds apply to the same original S. The independent determinant-sampling argument includes nonvertex maxima. The bootstrap, local thresholds, original-centroid coordinate formula, and universal E<=n branch are unchanged.
6. **Assembly and endpoints.** Section 6 explicitly handles e=0 without division, e=H_d^(-1) with a still-strict enclosure gate, and e>H_d^(-1). Affine normalization is undone on the original prescribed simplex and its centroid.
7. **Actual sharpness family.** The exact core defect, m=2 formulas, maximality among arbitrary inscribed simplices, raw pyramid identities, invariant Delta, d+1+k vertex count, E=nt, and ambient exact defect conversion and asymptotic limit are faithfully present. Stronger exponents are ruled out for the literal actual-body class.

All five requested nonblocking clarifications from the original review are implemented: positive integer ranges, unit/homogeneous projection notation, explicit m=2 core, actual `Entry005` theorem namespaces, and the cited-source factorial warning.

## Verification and literature language

The first-page status, README, source map, and Appendix A consistently distinguish the independent model's traditional review from professional peer review and from Lean formalization. The new cone/counting/facet-specialization/exponent assembly is explicitly not claimed to have a Lean certificate. No first-discovery or exhaustive literature-overlap claim appears. Classical convex-geometric inputs remain credited. The supplied older historical source status is preserved rather than silently rewritten.

## PDF and package checks performed here

- Recomputed every entry of `SHA256SUMS` successfully.
- Verified all 34 payload entries in `PACKAGE_MANIFEST.json` against their bytes and hashes.
- Verified the archive contains exactly the 37 regular files in `RELEASE_FILES.txt`, and compared **every archived file byte-for-byte** with the reviewed directory copy. No unlisted build cache or render file is present.
- Extracted fresh PDF text and confirmed it is byte-identical to the saved layout text. It has 17 pages and no unresolved `??` reference marker.
- Checked 74 distinct TeX labels, with every `ref`/`eqref` resolved and no duplicate label.
- Rendered the supplied final PDF with Poppler at 75 dpi and visually inspected all 17 pages in contact sheets. The theorem constants, core displayed formulas, original-defect normalization, projection comparison, endpoint assembly, sharp limit, and verification appendix are present and legible. No visible formula omission, clipping, overlap, missing glyph, or damaged page boundary was found. This contact-sheet inspection complements, rather than relabels, the author's separately recorded 100-dpi page-by-page inspection.
- Read the supplied clean-archive build receipt. I did not rerun TeX or Lean during this limited check, and do not claim a new clean-build result.

Machine-readable results are recorded separately in `FINAL_COPY_BINDING.json` beside this receipt. Render images are local review artifacts only and are not additions to the publication package.

## Boundary

No manuscript, source snapshot, PDF, archive, release manifest, or old formal source was modified. No commit, push, upload, publication, or external sharing was performed. This PASS is bound to the exact PDF and archive hashes above; a later substantive copy requires an appropriately scoped delta check.
