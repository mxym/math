# Reproduction and verification scope

The final public copy passed the supplied exact checker, the independently
implemented sharp-endpoint checker, the previous independent integrated-witness
checker and the inherited truncation checker, each normally and under Python -O.
The two modes produced identical logs and, where applicable, certificates.
The exact checker bytes and historical certificates remain unchanged.
All six pinned mathematical source entries matched their hashes and byte counts.

The proof PDF has eight pages and repeated offline builds produced identical
PDF/text bytes. No overfull boxes or unresolved references were reported.
All pages were rendered and visually inspected; see PDF_QA.md. Details and
hashes appear in results/verification.json. MANIFEST.json, SHA256SUMS and
PACKAGE_FILES.txt describe the complete public package and exact archive contents.

The original independent analytic model audit passed without mathematical
correction. Its complete analytic chain and finite-check limitations appear
in INDEPENDENT_ANALYTIC_AUDIT.md. Finite evidence is not human peer review or
proof-assistant formalization and does not enumerate arbitrary convex bodies.
The sharp power is proved only in the stated every-maximum-simplex theorem class;
no priority, literature-wide novelty or journal-acceptance claim is made.
