# Independent local public-package review

Date: 7 October 2026. Result: PASS for the checked local package, with no remaining packaging blocker.

This is a packaging review of the separately reviewed revision-2 traditional manuscript. It is not a new mathematical proof audit, Lean build, kernel replay, human peer review, legal clearance, or verification that any file is published remotely. The reviewer did not modify the package or contact GitHub.

## Findings and publication boundary

- No concrete content, privacy, preservation, or standalone-verification blocker remains in the checked snapshot.
- All 12 external README destinations exist at the supplied local formalization roots and match the intended repository-relative layout. They do not resolve in the isolated manuscript staging directory, which intentionally omits those formalization packages. Remote presence was not checked and needs separate publication receipts.
- Earlier wording that described the formalization projects as “separately published” was corrected to “separately distributed.” This avoids making an unverified publication claim.
- Any final reproduction note or verified remote provenance changes require a fresh manifest/checksum seal and another integrity run. This report applies to the exact hashes below.

## Preserved record and attribution

Direct byte comparison confirms all 17 claimed unchanged revision-2 members, including the current TeX/PDF, correspondence evidence, baseline TeX/PDF, exact patch, correction record, and regression script. The historical original manuscript manifest is byte-identical. All three original independent-review hashes match; public copies differ only by the disclosed private delivery-identifier removals and derivative notices.

README and NOTICE retain the missing-hypothesis defect and its subsequent correction rather than concealing the revision history. The superseded baseline is clearly marked. The independent AI review, publication-priority limits, blank authorship, and absence of a new blanket license are stated accurately. The retained upstream license and collection notice are identical to those in the supplied continuum formalization distribution.

## Independent verification

The standalone checker passes with normal Python and with optimization enabled. The explicit-local-source comparison also passes in both modes on the current checker: 65 module hashes, 759 source-visible declaration locations, 57 mapped declarations across 20 paper steps, 45 reused geometric modules, and 18 frozen continuum modules.

Fifteen control cases were executed on the earlier 27-entry payload in both normal and optimized modes, for 30 expected outcomes. The final 28-entry payload adds a reproduction record and documentation and retains the identical checker. Final standalone and explicit-source checks were separately rerun in both modes and all pass; the earlier control outputs are retained honestly as historical results. The unchanged positive control passes. Fourteen negative controls per mode fail with nonzero exit status: altered manuscript, altered notice, missing PDF, extra file, symlinked file, symlinked directory, duplicate manifest key, malformed manifest, duplicate checksum entry, malformed checksum line, manuscript corruption with regenerated ordinary manifest/checksums, missing requested external roots, one-sided external-root arguments, and conflicting source-input routes. The independently frozen manuscript anchor catches the regenerated-manifest case. Details are in independent-corruption-controls.json.

The checker uses explicit runtime requirements rather than optimization-removable assertions. It authenticates the exact file inventory and frozen revision anchors, regenerates and replays the source patch with zero fuzz in a temporary directory, and executes the historical origin controls only from a temporary copy. Requested source checks fail when unavailable; otherwise the report explicitly says NOT_RUN. Hashes are described as consistency records rather than signatures, as they should be.

The 20/57 declaration map and 759-entry inventory are properly described as source/name/line correspondence. They do not establish equivalence between prose and elaborated statements. The 65-module/172-edge record is a local import map, not a kernel dependency graph. Linked replay program/log paths exist locally, and their recorded 34,923/35,620 closure sizes and 1,445 safe-owned-root scope agree with the README. No replay was performed during this review.

## Privacy and local reproducibility

Targeted scans found no private delivery identifiers, credential patterns, or private execution paths in the payload text. The known removed identifiers are absent from all payload bytes and extracted PDF text. Both PDFs have blank Author metadata and 14 pages; the current PDF contains no embedded files. This is a targeted inspection, not an exhaustive secret-detection guarantee.

Standalone checking requires only the Python 3 standard library and GNU patch. Code inspection found no network or private-service dependency. The optional PDF rebuild uses local installed TeX tools with shell escape disabled. Its Debian fallback reads standard installed files and writes generated formats, font maps, hyphenation configuration, and caches only under the temporary build directory. It does not install or download dependencies and does not relax exact extracted-text comparison.

The packager's normal-full.json and optimized-full.json both report successful isolated 14-page PDF rebuilds with every extracted text byte equal to the frozen PDF, text SHA-256 ba9167b9a458b40394d99af196983e7f4e44f15082c59006ef8523ad16572e77. This reviewer inspected both reports and the fallback implementation but did not duplicate the PDF builds. The public reproduction summary faithfully preserves their substantive results and exact raw-report hashes; its additional 44-member archival comparison is a packager-reported check not independently repeated here. The supplied reviewed PDF itself remains byte-preserved.

## Final sealed snapshot

- run_checks.py SHA-256: b23bc9c04cc325d6d969e219c9b2536502adc48c55291d8aebc942e4c1d10acc
- MANIFEST.json SHA-256: 123a35b05bc84b73cc778fd4f870a4c14fd1cf67155848f3e1728e95342e0bab
- SHA256SUMS SHA-256: 70c025455888cb309f9e6416c3542022338afd162a51bf581d71006f1e945c33
- Payload inventory: 28 manifest entries plus MANIFEST.json and SHA256SUMS, 30 regular files total.
- Public archive: 827,349 bytes; SHA-256 26be553e00f704324770213d5ac1f51b756ac66e9a4ab199a92e9d3d9ea4c6d2.

The final archive was inspected without extracting it. It contains exactly the 30 expected regular files, with no duplicate/traversal/symlink members, normalized owner metadata, and every member byte-identical to the final staged package. Standalone and explicit-local-source verification pass in normal and optimized modes on this final sealed snapshot.
