# Sharp Chebyshev Atom Moduli for Fixed-Rank Subset Actions

## Preferred typeset revision (v2)

The [21-page revised PDF](v2/paper.pdf) and its [matching editable source](v2/paper.md) use the same mathematical proof as the preserved first 22-page typesetting, but more balanced A4 page breaks and margins. This revision was compiled, visually checked (first, proof, and final pages), and independently rebuilt from the public source.

- v2 compiled PDF SHA-256: \`ace1367323ab6dbc0a2ad53c199fe24723a2ca471c9a3e8ad56e415b1099d262\`.
- v2 Markdown source SHA-256: \`3fc60615906235f8d2bf1060c2a338af9c2c32e57389c82fd2d90bfe007f3ffa\`.
- v2 Git PDF blob: \`5f860617a1b03bcf57bebcfda8c7bd8df6977c7d\`.

The historical first paper.pdf and paper.md remain unchanged for reproducibility; cite v2 unless a specific earlier publication snapshot is required.


This directory contains a **22-page independently readable research manuscript** on the sharp leading asymptotic coefficient for marginal-preserving permutation laws, its exact cycle-index transfer-matrix proof technology, and its finite four-subset classification.

- **[Compiled paper](paper.pdf)** — A4, 22 pages; visually checked in sample pages and programmatically inspected on the authorized VPS.
- **[Editable Markdown source](paper.md)** — mathematical definitions, full two-sided fixed-rank asymptotic proof, exact all-rank cycle compression, and complete finite k=4 certificate interface.
- **[Full source dossier](../paper.md)** — retains Sections 1–26, detailed provenance of the earlier rank-one through rank-three results, the exact rank-four primal-dual certificates and all related derivations.
- **[Verification and trust boundaries](../VERIFICATION.md)** — what has been symbolically or exhaustively replayed, and what remains analytic or unreviewed.

## Main mathematical statement

For the natural action of \`S_n\` on its \`k\`-subsets, let \`C_{n,k}\` be the smallest universal constant in

\`\`\`math
|\nu(\sigma)-1/n!|
\le C_{n,k}\|\nu-u_{S_n}\|_{\mathrm{TV}}
\`\`\`

for every probability law \`nu\` whose image of **every** \`k\`-subset is uniformly distributed among all \`k\`-subsets. For every **fixed** integer \`k>=1\`, the paper proves

\`\`\`math
C_{n,k}=1-\frac{2k^2}{n}+O_k(n^{-2}).
\`\`\`

The proof gives both (i) a corrected shifted-Chebyshev orbital dual yielding the uniform upper bound and (ii) **positive conjugation-invariant measures with exactly identical subset-image marginals** giving the matching lower bound. It also proves that every rank-k orbital statistic depends only on permutation cycles of lengths \`1,...,k\`, by an exact 2-by-2 transfer-matrix identity valid for **all finite n,k**.

## Supporting evidence

- **[Exact k=4 Chebyshev checker](../code/check_k4_chebyshev_dual.py)**: symbolic identities and six genuinely positive finite rational primal examples; Python + SymPy.
- **[All-rank transfer-matrix integer checker](../code/check_all_k_orbital_compression.py)**: independent direct subset enumeration on all conjugacy partitions of n=3,...,12 with k up to 6; standard-library only.
- **[k=4 fixed exact certificates, n=8,...,64](../certificates/four_subset_n8_64.json)**, and **[independent integer/Fraction checker](../code/check_four_subset_n8_64.py)**: exhaustive proof of the finite degree range through 440,670 compressed cycle types.
- **[k=3 fixed exact certificates through n=120](../README.md#three-cycle-compression-full-degree-120-classification-and-sharp-18n-asymptotics)**: separately preserved historical exact classification.

These computations verify the stated finite certificates or selected algebraic identities. They do **not** replace the universal analytic proofs.

## Rebuild

From this directory with Pandoc and a LaTeX installation (pdflatex):

\`\`\`bash
pandoc paper.md --from markdown+tex_math_dollars -s --toc --toc-depth=2 --pdf-engine=pdflatex -o paper.pdf
\`\`\`

The exact public compiled PDF has SHA-256

\`\`\`text
a25586b8a78e1d3f52b6217ebedcf66f2de1e86b8b68f321f342ef1d99ab4be6
\`\`\`

and Git blob object SHA \`ac2976278868d23d57466bb9699b439a3776900e\`. The editable source has SHA-256 \`2c2aab0ed0220e5a79770b1362d3bdd59aabbbffa473549195da2a5cde6f2a60\`. The above build command is reproducible as a source compilation; bit-for-bit binary PDF agreement may depend on TeX engine build metadata and fonts.

## Attribution and review status

This is AI-assisted mathematical research. Its use of finite LP strong duality, classical Chebyshev and Bernstein polynomial interpolation, and cycle-index transfer matrices is stated explicitly. The numerical LP stages were used for **finite-certificate discovery only**; the published proof does not import solver output as a premise. The full paper has not yet undergone external human peer review, systematic novelty analysis or Lean/Coq formalization. No universal exact finite-(n,k) optimum formula is asserted, and the asymptotic result treats each **fixed** rank k rather than growing k.
