# Withdrawn: KeyBreak final-GCD probability audit

**Status: withdrawn on 2026-11-28. Do not cite the earlier audit as a mathematical finding.**

The earlier files in commit `fb8861b0b11379a2d2acb24fb917a56470ed02f5`
were prepared from text extraction that misread the superscript in equation
(5.5).

Direct visual inspection of the authors' fixed published PDF, page 18, shows
the exact factor `1 - 2^{1-omega(N)}`, agreeing with equation (5.4). It does
not print `1 - 2^{-omega(N)}`. Thus the alleged probability overstatement
does not exist in the fixed source.

Published PDF: https://crypto.sjtu.edu.cn/factoring.pdf
SHA-256: 2b534eaf77fb2b9712018879059d8d4667c40c0a4adf2fff90efc22fb356cfc9

The proof, checker, results, and source note from the erroneous audit have
been removed from the live branch. Git history is retained only for
traceability.
