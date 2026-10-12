# Frozen polynomial simplex stability final copy audit

Date: 7 October 2026.

Verdict: **PASS. No corrections are required for this frozen release.**

This is an independent model-based final-copy audit of the exact 35-file public stage for the polynomial-dimensional simplex-stability supplement. It verifies the release against the frozen basis, its complete mathematical Markdown, its typeset derivative, and independently retrieved pinned public sources. It is not human peer review, proof-assistant verification, a novelty assessment, or authorization to publish.

## Exact reviewed release

- `source.zip`: 672029 bytes; SHA-256 `4fc6de94915be740c03f48e4b437b5481c3dbcddef946c86aaee78494264820a`
- `MANIFEST.json`: `a16e45b0e35373622da8cc887887fb03a193a235937805c42145a1da2e0c2895`
- `SHA256SUMS`: `a31044b364e1e005739823918f58ff74ae4d9209669e87171e867d574f5fbbbf`
- Main mathematical Markdown: `2b398cba3afd73819dbf90d5106e64be64ba06a07f9e42d23f4c2037ff5cd791`
- Exact Sections 1–8 core: `94c4e777b0000e5e33e024d59c47e258594fbfacc554e4faa91f8b5264c503f5`
- Square-pyramid proof: `dee887e50590cd750d5b211acd9015fa57db5bd70786dcd67ec701674139596e`
- `proof.tex`: `73ff46719e442da83eb773ff0f1ee7d9b49d30bfa2200786a11fe433fe09572c`
- `proof.pdf`: 354063 bytes, 11 pages; `1972edd13d2b43d6318fbb0ccdbc192ef14139b83f429249da9bc06ae764f2d9`
- Sanitization ledger: `c2c2c08f8fba846c9f88a22d2b6384578035ae0123aef0e165e869e223e05b78`
- Frozen basis manifest: `8fdac6d99df6f57a97552998fb6a4415306ac1ce196c01935a72e1bd08ee5da0`

The initial and final frozen-tree hashes agree. No release file was edited; no repository mutation or publication was performed.

## Mathematical fidelity

Read and compared the complete 318-line refinement, 74-line square-pyramid proof and 681-line TeX derivative. The companion `math_fidelity/MATHEMATICAL_FIDELITY_AUDIT.md` records passage-by-passage coverage, line references and analytic checks.

The exact invariant, first absolute determinant moments, V-weighted selection with the nonsingular indicator, clipped negative-coefficient cases, measurable tie-breaking, fixed-norm assignment theorem, and weighted barycentric correction are preserved. The proof does not assume arbitrary centered laws are cone laws of convex bodies.

The same prescribed maximum simplex is normalized, retained and pulled back about its own original centroid. The theorem is valid for every such simplex; no selectable-simplex or Banach–Mazur replacement is substituted. The Cauchy factor, actual-body dispersion, mixed-volume scale correction, genuine enclosing simplex, projection cap, all local gates, zero-defect case, and global branch remain present.

All exact constants and their argument order agree. The coefficient bound is the frozen d^6 result, with the complete analytic chain ending in 737280 d^6 < 2^20 d^6. The square-pyramid proof preserves arbitrary-vertex maximality, its full facet data, both exact minor sums, E=d+1, e=1/[d(d+1)], and the lower coefficient (d+1)[d(d+1)]^(1/(d−1)).

The main mathematical file, its core, lower-bound companion, four original mathematical sources, three original checkers and original verification outputs are byte-identical to the frozen basis. Twelve file-level fidelity rows were independently checked. Audit technical Sections 1–7 and the square-pyramid audit calculation are also unchanged.

The typesetting clarifications are faithful: explicit projection-body and pyramid conventions, local reuse of H and L in the appendix, and specification of the maximum simplex used in the truncation obstruction. All theorem hypotheses and zero/local/global cases remain intact.

## Sources, citations and links

All seven public source-pin files were independently fetched through the GitHub connector at their exact commits. Every byte count and SHA-256 matches the included copy. This includes the original provenance notice and upstream Apache-2.0 text. Existing attribution is preserved; the release assigns no new blanket license.

All 24 new public Markdown relative links resolve inside the package. Every external URL in the PDF matches its TeX source, and all PDF internal destinations resolve. The four manuscript citations and three external literature-positioning URLs in the bibliography were verified. The cited classical Schneider source is explicitly inherited and is not represented as a newly proved input.

Fresh inspection of the three primary literature pages confirms their stated limited roles: polar projection-body/Banach–Mazur stability, cone-volume concentration/U-functionals, and mean-width/ell-norm stability in John/Löwner positions. No estimate from a different deficit is silently imported.

The untouched historical sources contain three relative links which do not resolve from the flattened offline `sources/` directory. This is already disclosed in README and SOURCE_PINS. All three resolve in the exact pinned GitHub directory context: the v2 paper, its spectral supplement and its research log. The v2 paper is also bundled locally. The supplement and research log are not missing dependencies of this release's theorem.

The broader URL inventory was checked as well: five additional historical GitHub references resolve, and the inherited external literature/license URLs identify the cited resources. Two DOI landing requests were unavailable through the web tool; their exact DOI and bibliographic identities were confirmed on the publishers' pages. One version-specific arXiv abstract request was unavailable; the exact v2 HTML and canonical arXiv page were accessible. These are access-route limitations, not evidence of invalid citations. No new release-facing link is unresolved.

## Sanitization, privacy and scope

Independently reconstructed all 12 disclosed editorial operations from original fragments, sequential line positions, fragment hashes and replacement text. They reproduce both sanitized derivatives exactly: three changes to the anchor report and nine to the independent audit. The broader construction-class omission is explicit, and no technical argument is silently excised.

The 35-file stage has no symlink or unlisted file. Text, PDF extracted text and PDF metadata were checked for private filesystem locators, private attachment/thread schemes and common secret markers. None occurs except the public checker literally naming the patterns it rejects. The archive contains only the exact reviewed payload.

No unreviewed anisotropic, simultaneous-truncation, broader construction-class or stronger quadratic-dimensional theorem is included as a release claim. The d^6 release remains isolated. No human-peer-review, Lean/kernel-verification, first-discovery, best-known-result, institutional-affiliation or priority claim has been added.

## Regression and integrity behavior

All three unchanged mathematical checkers pass through `verify.py` normally and with both an optimized parent and PYTHONOPTIMIZE=1. The wrapper launches isolated, unoptimized children and explicitly checks that assertions are enabled. Recorded rational-law/facet logs match exactly, and the floating constant certificate matches the frozen data.

An independently extracted source archive also passes normal and optimized `--extracted` verification. Regenerating MANIFEST, SHA256SUMS and source.zip gives byte-identical results. The archive has 34 sorted member paths, fixed 7 October 2026 timestamps, stored compression and normalized file permissions.

Twenty-four negative controls, twelve cases under normal Python and -O, all fail as required. Cases cover changed main proof; regenerated manifest after main/source/square-pyramid/audit/anchor/checker changes; changed TeX; an unlisted file; missing or altered archive; and malformed checksums. Error messages and return codes are recorded in `AUDIT_EVIDENCE.json`.

Integrity checks protect exact bytes and immutable mathematical sources; they do not mechanically prove the equations or replace this textual/analytic audit. As with any self-contained checksum package, externally retained release hashes remain the identity anchor.

## PDF and clean builds

Rendered all 11 pages anew with Poppler at 115 dpi and opened every page individually. No clipping, overlapping text/equations, missing glyphs, broken numbering or unreadable reference URLs was found. The deliberate Section 2 heading break is clean. `VISUAL_QA.json` identifies every inspected image and its hash.

Two separate clean directories received only proof.tex and build.sh. Each generated its own fresh format from the installed TeX sources, ran the three-pass build with shell escape disabled, and reproduced the exact frozen PDF bytes. Neither build copied a format cache or downloaded dependencies. Compiler logs contain no overfull/underfull boxes, undefined references/citations or missing characters. The sole epstopdf shell-escape warning is expected and irrelevant because the document has no EPS graphics.

The reproducibility result is for the recorded TeX Live/pdfTeX toolchain. Cross-toolchain PDF byte identity is not claimed. Similarly, floating diagnostic output may differ at the last bit across platforms, as the README already explains.

## Retained public audit evidence

This public copy preserves the complete verdict and mathematical, source, sanitization, regression, PDF and clean-build findings above. The retained records are:

- `AUDIT_EVIDENCE.json`: reviewed hashes, basis comparisons, editorial reconstruction, source-fetch checks, links/privacy, archive tests, negative controls and clean-build results
- `math_fidelity/MATHEMATICAL_FIDELITY_AUDIT.md`: full mathematical/textual audit with line references
- `VISUAL_QA.json`: per-page visual inspection record and hashes of all eleven inspected renders
- `verify_normal.log` and `verify_optimized.log`: unchanged successful checker replay logs
- `PUBLIC_COPY_LEDGER.json`: exact original/public byte identities and disclosed editorial operations

The audit's disposable extraction/build directories, rendered image files, original workspace-bound audit harness, raw retrieval responses and compiler logs are not included in this compact evidence copy. Their recorded results and render hashes remain in the retained evidence; this copy does not claim those omitted files are bundled. The only report edits are this evidence-location paragraph and removal of workspace-specific locators from companion metadata. No mathematical finding, check result or limitation is changed.

The frozen mathematical packages provide their own portable `verify.py`, package checks and deterministic archive generators. The sibling publication-integration records separately identify the fresh checks run on these exact frozen packages. The underlying audit used the installed pypdf library for PDF inspection; the polynomial release's verifier uses only the Python standard library.

**Final disposition: PASS for the exact frozen hashes above. No source correction requested.**
