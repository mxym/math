# Withdrawn: KeyBreak character identity audit

**Status: withdrawn on 2026-11-28. Do not cite the earlier audit as a mathematical finding.**

The earlier files in commit `90347f6ae3a5346ea658a0135d0946fe1c6a1494`
were prepared from text extraction that lost overbars in equation (C.46).

Direct visual inspection of the authors' fixed published PDF, page 69, shows
the right-hand side as
`̅chi(iota) V_{1,delta}(chi) ̅V_{2,delta}(chi)`,
with the required complex conjugations. Thus the printed identity is correct
on this point and the alleged missing-conjugation error does not exist.

Published PDF: https://crypto.sjtu.edu.cn/factoring.pdf
SHA-256: 2b534eaf77fb2b9712018879059d8d4667c40c0a4adf2fff90efc22fb356cfc9

The proof, checker, results, and source note from the erroneous audit have
been removed from the live branch. Git history is retained only for
traceability.
