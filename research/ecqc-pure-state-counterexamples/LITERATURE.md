# Literature and task selection record

Checked October 8, 2026, America/Los_Angeles. This record is a scoped literature check, not a proof of priority or an exhaustive bibliographic survey.

## Repository overlap check

The initial `mxym/math` main snapshot was `b8a6ab42d8f9b8046bb3a3072fa409cca325017e`. README.md, SOLVED_PROBLEMS.md, RESEARCH.md, recent commits, and the recursive tracked-file tree were inspected. No tracked AGENTS.md was found at that snapshot; the Windows worktree ancestor directories also had no AGENTS.md. The existing checkout had unrelated untracked permanent-research files, which were left untouched. A separate worktree and branch were used. Later parallel main commits were fast-forwarded rather than overwritten. The first standalone qutrit proof was added to main as `038aba8eb24ecd446f2ba5f7389f94abd364bdf7`.

The public `openai/math` README and ECQC-related code search were checked as an additional overlap screen. Neither a repository label nor a failed code search was treated as evidence that a theorem was proved or still open. Existing Bapat, Gaussian, graph-Chollet, and mutual-information continuity projects were excluded as duplicate or parallel work.

## Candidates screened and excluded

1. **Sharp continuity of quantum conditional entropy.** Berta, Costa Rico, Kossmann, Lami, and Zeiss, *Sharp continuity of quantum conditional entropy*, arXiv:2607.24687 (2026), already publicly claims the sharp result. It was not selected for a new-solution claim.
2. **Unrestricted PPT-squared / general CQC / general ECQC.** Public counterexamples or solution claims were found, including existing reference-repository work for PPT-squared and the 2026 CQC papers below. These unrestricted statements were not treated as unsolved targets.
3. **Pure-state ECQC.** Iqbal explicitly poses this in the closing section. The retrieved later ECQC counterexample is mixed, not pure. The task was narrowed to the pure-state statement before the construction was developed. Subsequent research strengthened it to the prime-dimensional validity classification and sharp ratios at dimensions three and five.

## Primary sources and exact scope

- Hasan Iqbal, *On the CQC Conjecture: A sufficient condition and an extension*, arXiv:2509.08286v2; journal DOI [10.1007/s11128-026-05258-2](https://doi.org/10.1007/s11128-026-05258-2). The statement is Conjecture 3.1 / equation (6), with a minimum over `p` of `p+1` mutual informations. Section 5 separately asks for the pure-state case. Both [the arXiv HTML](https://arxiv.org/html/2509.08286v2) and the journal text were consulted; same-basis measurement conventions and the logarithm-base change were checked.
- Jinbo Wang, Qihang Wang, Kun Chen, *When Complementary Measurements Count the Same Classical Bit Twice: Counterexamples to CQC, ECQC, and Complementarity-Based Certification*, [arXiv:2608.03828v2](https://arxiv.org/html/2608.03828v2), Section IV and Appendix B. Its ECQC state is a rank-two classical–classical **mixed** state, with a displayed dimension-seven violation and unbounded prime-dimensional overrun. The revised title and ECQC content, not merely the earlier CQC-only abstract, were checked.
- James Schneeloch, Curtis J. Broadbent, John C. Howell, *Uncertainty relation for mutual information*, [Physical Review A 90, 062119 (2014)](https://doi.org/10.1103/PhysRevA.90.062119). The original two-basis CQC statement has an established pure-state case; the new examples do not contradict it.
- A. S. Holevo, *Bounds for the Quantity of Information Transmitted by a Quantum Communication Channel*, Problems of Information Transmission 9(3), 177–183 (1973), [primary publication record](https://www.mathnet.ru/eng/ppi903). The accessible-information theorem is explicitly used for the universal pure-state upper bound and the dimension-two boundary, not assumed as a new unproved ECQC bridge.
- *Separable Counterexamples to Complementary Quantum Correlations, and Why Random Search Missed Them*, [arXiv:2608.14806v2](https://arxiv.org/html/2608.14806v2), was also screened for overlapping CQC counterexample claims and surviving scope.

## Searches and limits

Searches included combinations of ECQC / extended CQC with pure, pure-state, qutrit, Schmidt, Bell, singlet, dimension five, and counterexample, using both available public search engines. The retrieved primary sources were read for their quantifiers and state classes. No public pure-state ECQC resolution was identified in those checked sources before this work; that statement is deliberately narrower than an assertion that none exists anywhere. Search results, publication dates, release timestamps, and DOI assignment do not establish historical priority.

## Discovery versus proof

Initial structured calculations found the embedded Bell family in prime dimensions at least five. A finite qutrit optimization then suggested a stronger three-dimensional extremum. It was replaced by the explicit real singlet, and exact algebra proved its four identical Born tables. The parity mechanism yielded the five-dimensional singlet and its exact six identical scores. The optimization, its convergence, and any finite search coverage are absent from all theorem dependencies.

The global optimum ratio is proved only for dimensions two, three, and five, from the established Holevo upper bound and matching exact examples. No numerical optimizer is used as an optimality certificate.
