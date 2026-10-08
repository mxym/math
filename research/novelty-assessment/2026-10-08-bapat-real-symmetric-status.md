# Bapat q-permanent: bounded status check for the real-symmetric result

**Screen date:** 2026-10-08 UTC

**Repository snapshot:** `/workspace/math`, commit `2509263c1028d6814658174b2830a3d658e76c1c` (`2026-10-08T06:33:02-07:00`), “Publish real symmetric positive-definite Bapat counterexample existence proof”. This is a literature/scope check, not a verification of the proof.

## Exact new claim checked

I read `notes/bapat-real-symmetric-existence-counterexample/proof.md`, Theorem 1, and `SOURCES_AND_REVIEW.md`. With

\[
P_q(A)=\sum_{\pi\in S_N}q^{\operatorname{inv}(\pi)}\prod_i a_{i,\pi(i)},
\]

Theorem 1 asserts that some integer `N>4`, non-diagonal real symmetric positive-definite `B` (indeed with integer entries), and rational `0<q0<q1<1` satisfy `P'_1(B)<0` and `P_{q0}(B)>P_{q1}(B)`. The result is existential: it supplies no particular dimension, matrix, or parameter pair. Rank at most four is used only for an intermediate PSD Gram matrix; the final matrix is full-rank PD. It does not assert entrywise nonnegativity. Thus it is a counterexample to the real-symmetric restriction on the original interval `[-1,1]`, not just an extension to `q>1`.

The note’s own prior-work record identifies the formulation as Bapat’s conjecture, citing Lon Mitchell (2020), *A note on Bapat’s q-permanent conjecture*, *Operators and Matrices* 14(4), 915–919, DOI [10.7153/oam-2020-14-56](https://doi.org/10.7153/oam-2020-14-56). It says the publisher PDF was read in preparation and that p. 915 states the Hermitian positive-definite problem. A fresh direct fetch during this screen redirected to HTTP 400, so this bibliographic/source detail is being reported from the repository’s documented earlier primary-source check, not a new successful download.

The already documented explicit order-200 counterexample is **complex Hermitian**, with a rank-two Gram construction plus a positive-definite perturbation; it does not settle the real-symmetric subcase. The newly checked result claims real symmetric matrices and the original `[-1,1]` interval, but remains non-explicit. The real theorem itself expressly says it does not use or relabel the complex example. De Sá’s noncrossing special cases recorded in the older review are also not the unrestricted real-symmetric statement.

## Bounded current-literature checks

- Searched the current OpenAI/math snapshot at `/workspace/scratch/openai-math`, HEAD `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, with `rg` over text/TeX/Markdown/BibTeX sources for `Bapat`, `q-permanent`, `inversion-weighted`, and related forms. No matching source item was found. This is a repository-content search only.
- The closest recent public q-permanent paper I located and actually read is E. Marques de Sá, “The limits of Schur multipliers in Pólya conversion problems for the q-permanent function,” arXiv:[2605.24349v2](https://arxiv.org/abs/2605.24349v2), 31 May 2026. Its full v2 text defines the same inversion-length q-permanent, but studies linear Pólya conversion, Schur-multiplier preservers, Hessenberg conversion, permutation symmetries, and zero loci. It does not state or resolve monotonicity for real-symmetric/Hermitian positive-definite matrices. Its cited Bapat-related work is not a same-scope counterexample.
- A broad arXiv search also returned Dmitriy Kunisky, Daniel A. Spielman, and Xifan Yu, “Inequalities for rank-two permanents and finite free convolutions,” arXiv:[2608.28520v1](https://arxiv.org/abs/2608.28520v1), 28 Aug 2026. I checked the arXiv primary metadata/abstract: it concerns the ordinary permanent and finite free convolution for rank-at-most-two real matrices, not the inversion-weighted q-permanent monotonicity question. This is only an abstract-level exclusion.
- Exact or near-exact arXiv queries used: `all:"Bapat" AND all:"q-permanent"`; `all:"Bapat q-permanent"`; `all:"real symmetric" AND all:"q-permanent"`; `all:"Bapat" AND all:"monotonicity" AND all:permanent`; `all:"q-permanent" AND all:counterexample`; plus the broad `all:q-permanent` query. Crossref keyword searches for “Bapat q-permanent”, “q-permanent conjecture”, “Bapat monotonicity permanent”, and “inversion weighted permanent” produced no verified same-scope 2026 result. These keyword and metadata searches are not exhaustive.
- The earlier complex-counterexample review in `notes/bapat-q-permanent-counterexample/referee_report.md`, especially its scope discussion around lines 209–237, records a bounded 2026 search for the original Hermitian conjecture and explicitly leaves the real-symmetric restriction unsettled. That review predates the current real theorem. It records that full texts for Bapat (1992) and Bapat–Lal (1994) were not obtained in that audit; Mitchell’s 2020 paper and Bapat’s 2007 survey are the source checks described there.

## Limited conclusion

Within the repository snapshot and the limited arXiv/Crossref/current-OpenAI checks above, I did **not locate** a prior result with the same real-symmetric, positive-definite, integer-matrix, original-interval scope, nor a 2026 source proving or refuting that exact restriction. The q-permanent papers located are adjacent but answer different questions. This is a bounded non-match report, not evidence of historical priority or a claim that no such result exists; unpublished work, differently indexed work, and sources outside the inspected set remain possible. No proof validation was performed.
