# Public-status and definition checks

Checked 2026-10-08, approximately 09:57–10:10 UTC.

## What was established

1. The journal's live PDF still contains Conjecture 21, asserting infinite log-concavity of absolute chromatic coefficients. It explicitly lists cycles among the tested examples. No correction to that claim appears in the inspected section.
2. The journal landing page identifies the article as T. Amdeberhan and V. H. Moll, *Infinite log-convexity*, Online Journal of Analytic Combinatorics, Issue 17 (2022), Paper 6, 1–10, DOI 10.61091/ojac-1706. The PDF itself carries a December 30, 2023 date; we do not try to resolve that bibliographic discrepancy.
3. The standard finite-sequence boundary convention is explicit in the paper cited as reference [9]: Brändén, *Iterated sequences and the geometry of zeros*, page 2, defines L on the same index set 0,...,n and sets a_(-1)=a_(n+1)=0. This validates the retained-endpoint calculation for C17 and C12.
4. Independently of that convention, adding one isolated vertex to C17 shifts the negative entry far enough into the initial coefficient range that three rounds of endpoint-deleting local computations also produce the negative value. The verifier checks this directly.
5. Targeted searches did not locate an earlier public C12/C17 counterexample, the n>=17 cycle formula, or an erratum resolving Conjecture 21. This is a bounded negative search result, not proof of priority or an exhaustive claim about the literature.

## Primary sources inspected

- Original journal PDF:
  https://combinatorialpress.com/article/ojac/vol17/305.pdf
  Pages 1 and 8–9 inspected, including the definition, cycle formula, experimental claim, and Conjecture 21.
- Journal record:
  https://combinatorialpress.com/ojac-articles/issue-17-2022/infinite-log-convexity/
- Brändén's reference defining zero extension and retained endpoints:
  https://arxiv.org/pdf/0909.1927
  Page 2, introductory definition.
- BIRS workshop report repeating the chromatic infinite-log-concavity question as Problem 5:
  https://www.birs.ca/workshops/2022/22w5004/report22w5004.pdf
- Tewodros Amdeberhan's homepage and publication list:
  https://math.tulane.edu/~tamdeberhan/
  https://www.math.tulane.edu/~tamdeberhan/publications.html
  The inspected publication list had no matching chromatic-polynomial correction. Author pages are mutable; the independent audit records its own observation separately.
- Victor Moll's homepage and papers list:
  https://www.math.tulane.edu/~vhm/
  https://www.math.tulane.edu/~vhm/pap22-short.html
  These lists contain older material and cannot by themselves establish the current status.

## Discovery indexes checked, with limitations

- MathDB: https://mathdb.com/
- ProbXiv: https://probxiv.com/?sort=title
- Exact-title and site-restricted web searches for the conjecture and proposed witnesses.

No matching problem or solution entry was retrieved from MathDB or ProbXiv. Only the first displayed archive page was read directly, so we do not claim that every archive item was inspected. Site-restricted searches returned unrelated chromatic quasisymmetric-function counterexamples, which do not settle this conjecture.

ResearchGate's article page still summarized the original paper and showed one citing item, a 2025 overpartition paper; this is secondary metadata, not a proof of the conjecture's open status.
https://www.researchgate.net/publication/388859647_Infinite_log-convexity

## Representative exact searches

- "chromatic" "infinitely log-concave"
- "Amdeberhan" "Moll" "Conjecture 21"
- "chromatic polynomial" "2-log-concave"
- "chromatic polynomial" "infinite log-concavity" counterexample
- "cycle" "infinite log-concavity" chromatic
- "cycles" "infinitely log-concave"
- "chromatic" "C12" "log-concave"
- "chromatic" "12-cycle" "log"
- "chromatic" "log-concave" "17" "cycle"
- "chromatic" "28272276537344"
- "chromatic" "249621701601"
- "Amdeberhan" "Moll" "log-convexity" erratum
- site:mathdb.com "infinite log-concavity" chromatic polynomial
- site:probxiv.com "chromatic" "infinitely log-concave"
- site:probxiv.com "Amdeberhan" "Moll" "log"

## Appropriate claim

The exact calculation gives a complete mathematical disproof of the stated conjecture under its standard interpretation, and a shifted graph gives the same disproof under the endpoint-deleting alternative. The public search found no prior resolution. It would be inappropriate to assert priority, peer review, journal acceptance, or author confirmation without further evidence.

## Earlier primary formulation

Amdeberhan, *Theorems, Problems and Conjectures*, arXiv:1207.4045v7, August 25, 2022, Section 13, page 14, states the same question as Conjecture 13.1. Its preceding definition explicitly imposes a_(-1)=0. The live arXiv record identifies v7 as the most recent revision. Section 14 lists updates but does not list a resolution of Conjecture 13.1.

https://arxiv.org/abs/1207.4045
https://arxiv.org/pdf/1207.4045

The author’s separate conjectures.html updates page linked by that paper could not be fetched through the web tool during the investigation. We therefore do not claim that this separate updates page was inspected.
