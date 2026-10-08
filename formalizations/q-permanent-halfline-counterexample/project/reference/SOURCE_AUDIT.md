# Source and literature audit, 2026-10-08

## Decision

The research target resolved by the certificate is da Fonseca's real positive-definite half-line monotonicity extension, not Bapat's original [-1,1] conjecture. The precise extension appears in a 2010 published paper, is repeated in the author's 2018 manuscript, and remains discussed as conjectural in Mitchell's 2020 published note. Focused searches through 2026-10-08 located no later disproof of that positive-definite statement. This is a bounded literature audit, not an absolute priority guarantee.

## Primary sources inspected

1. C. M. da Fonseca, *The mu-permanent of a tridiagonal matrix, orthogonal polynomials, and chain sequences*, Linear Algebra and its Applications 432 (2010), 1258–1266.
   - DOI: https://doi.org/10.1016/j.laa.2009.10.036
   - Publisher metadata/abstract: https://www.sciencedirect.com/science/article/pii/S0024379509005503
   - Complete OCR of the published article: https://www.academia.edu/103682178/The_%CE%BC_permanent_of_a_tridiagonal_matrix_orthogonal_polynomials_and_chain_sequences
   - The uploaded article retains journal pagination and DOI. The entire OCR, including pp. 1258–1266 and references, was read. A locally saved original PDF was not obtained; the download link failed to fetch. No access controls were bypassed.
   - p. 1259 defines A>0 as real symmetric positive definite. Section 2, Conjecture 1 asks for a left endpoint at or below -1 with strict increase up to +infinity, for arbitrary A>0. This is not restricted to tridiagonal A. The paper then proves the tridiagonal special case in Section 4.
   - The OCR does not preserve the exact less-than/less-than-or-equal glyph reliably. This is immaterial here: q=49 and 50 belong to both versions of the claimed interval.

2. C. M. da Fonseca, *The mu-permanent revisited*, arXiv:1804.02231v1, 6 April 2018.
   - https://arxiv.org/abs/1804.02231
   - https://arxiv.org/html/1804.02231
   - https://arxiv.org/pdf/1804.02231
   - Conjecture 1 is the original [-1,1] claim. Conjecture 2 is the half-line extension, attributed to the 2010 paper, and explicitly uses epsilon < -1.
   - The arXiv manuscript is nine pages. The journal paper associated with DOI 10.1080/03081087.2018.1466860 is reported as Linear and Multilinear Algebra 67 (2019), 1713–1714, only two pages. Its full published text could not be fetched. We do NOT silently identify its contents with the nine-page preprint. The 2010 published article independently supplies the target.

3. L. Mitchell, *A note on Bapat's q-permanent conjecture*, Operators and Matrices 14(4) (2020), 915–919.
   - https://doi.org/10.7153/oam-2020-14-56
   - Full official published PDF, all five pages inspected: https://files.ele-math.com/articles/oam-14-56.pdf
   - The note's main extension is from positive definite matrices to singular PSD matrices on [-1,1]. This is a different use of the word "extended."
   - The Remark on pp. 917–918 separately restates da Fonseca's half-line conjecture for non-diagonal PD matrices. It explains why a rank-one PSD analogue is false and explicitly distinguishes that from a counterexample in the PD domain.
   - Its low-order calculations show nonnegativity of the order-three derivative for every real q. Our minimal-order proof independently verifies the needed fact and claims no novelty for that fact.

4. E. Marques de Sa, *Letter to the editor on flawed mu-permanental formulas*, 2015 preprint; associated published letter in Linear and Multilinear Algebra 67 (2019), 1711–1712.
   - Full institutional preprint, all three pages inspected: https://www.mat.uc.pt/preprints/ps/p1519.pdf
   - Corrects formulas and the tree-case argument in da Fonseca's 2005 paper. The counterexamples concern identities and invalid index relabeling; this is not a disproof of the 2010 PD half-line conjecture. The 2019 final publication was checked only through its journal record; its full typeset text was not obtained, and identity with the preprint is not assumed.

5. E. Marques de Sa, *Noncrossing partitions, noncrossing graphs and q-permanental formulas*, 2017 preprint; published as *Noncrossing partitions, noncrossing graphs, and q-permanental equations*, LAA 541 (2018), 36–53.
   - https://www.mat.uc.pt/preprints/ps/p1722.pdf
   - Search-located text, especially p. 12, Corollary 4.5 and following explanation, again identifies the 2005 derivative-formula error and the illegitimate reordering of zero entries. Independent review did not find a disproof of the separate 2010 half-line conjecture in the inspected discussion.

6. E. Marques de Sa, *Linear preservers for the q-permanent, cycle q-permanent expansions, and positive crossings in digraphs*, LAA 561 (2019), 228–252.
   - Institutional manuscript: https://www.mat.uc.pt/preprints/ps/p1809.pdf
   - Theorem 8.3 and the following remark on p. 21 correct an earlier arbitrary-row expansion. Independent review did not find a disproof of the separate 2010 half-line conjecture in the inspected discussion. Search-returned material did not state a PD half-line monotonicity counterexample.

## Current public status checks

- MathDB problem 338857: https://mathdb.com/p/338857/de-falco-s-extension-of-the-monotonicity-conjecture-for-the
  It specifically displays the half-line statement, lists no solutions and no refreshed progress summary. It incorrectly calls the conjecturer "de Falco," so we use it only as an auxiliary discovery/status signal. A zero-solutions database record is not proof of openness.
- OpenProblemsInNLA MI-18, last checked 2026-09-10: https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-18/README.md
  Concerns Bapat's original [-1,1] problem. It must not be cited as proof of the separate half-line extension's status.
- Focused web searches used q-permanent/mu-permanent/Greek-mu variants with monotonicity, counterexample, disproved, da Fonseca, 2010, and 2025/2026. They repeatedly returned the 2010, 2018, 2020 primary sources and the 2005-formula corrections; no prior matching disproof was found.
- This bounded audit does not establish worldwide priority. Inaccessible final texts and unindexed work remain limitations.

## Excluded apparent overlaps

- A non-monotone singular rank-one example to the left of -1 does not refute a claim only about PD matrices; Mitchell explicitly says so. Our example is strictly PD and decreases at positive q.
- Disproofs of permanent-on-top, Bapat–Sunder, and Drury inequalities are different statements.
- A q-permanent conversion theorem or a counterexample to a Laplace expansion is different from failure of q-monotonicity on the PD cone.
- We have not resolved Bapat's original interval [-1,1].
