# Foregger power conjecture: prior-work collision and target withdrawal

Status checked on 8 October 2026. This records a research-selection decision,
not a newly solved conjecture or a certification of another author's proof.

## Two different conjectures

The Foregger power question asks whether, for each fixed order n, one
integer k(n) > 1 satisfies per(A^k(n)) <= per(A) for every real doubly
stochastic n-by-n matrix A. Cheon--Wanless (2005), Conjecture 17, is in
section 5 on printed page 326; earlier working notes incorrectly gave
section 7 and page 333.

The Foregger--Sinkhorn tie-point conjecture is a different implication
about a prescribed zero of a nearly decomposable, face-minimizing doubly
stochastic matrix. Yair Lavi's arXiv:2608.13025v1 (13 August 2026),
Theorem 1, gives an **8-by-8** counterexample to that implication. Its
cofactor is the permanent of a deleted-row/deleted-column submatrix,
not a determinant cofactor. That counterexample does not refute the
power question.

## Earlier public full-scope candidate

The repository
<https://github.com/infinityscroll/foregger-1978-candidate-proof>
was created on 7 September 2026. Its initial public-source commit is
`d5106a3ee4ab4be7df24ce4bf1df06a0b5821d6a`; the checked HEAD is
`a2b5ff091a95d703c757cf970f3b75ed587ad7fe`.

Its manuscript, `manuscript/UNIFORM_EVENTUAL_PERMANENT_POWER_DRAFT.md`,
has SHA-256
`92d43334ef63182838619795ed96a34edf7b67e3d0e49b6387424982f57aa2a0`.
It states exactly the stronger eventual-tail conclusion:

> For every n there exists K(n) >= 2 such that per(A^k) <= per(A)
> for every doubly stochastic A of order n and every integer k >= K(n).

The accompanying right-factor corollary also treats per(A^k C) for
arbitrary doubly stochastic C. Its status document explicitly calls the
work a candidate proof, distinguishes internal AI-assisted checking
from external peer review, and does not claim complete Lean verification.
The complete analytic text was read here; no immediately substantive
gap was identified. This is not a new external validation or a claim of
journal acceptance.

Yair Lavi's public source-navigation page
<https://yairlv.github.io/research-site/mincs-list/conjecture-17/>
also points to this earlier candidate and reports an audit finding no
gap. Such a page and a Git posting are distinct from journal refereeing.

## Decision and retained record

Our independent working manuscript reached the same all-large-integer
power conclusion, including a cyclic uniform-block equality
classification. Its frozen SHA-256 is
`af62b3b4cc1061ce730ae06279871503473f0869c0a93a4ae5b661097830cce3`.
It used a sector estimate and slow/fast spectral perturbation, whereas
the earlier public candidate uses a compression-probability identity
and a local arbitrary-right-factor estimate. A different proof route
does not establish a new conjecture resolution.

The earlier candidate was located before any release or theorem-package
publication of our draft. Foregger is therefore withdrawn from the
project's list of unaddressed conjectures to attack. We do not publish
it as our original conjecture breakthrough or make a priority claim.
The independent scratch derivation and its internal audits are retained
for provenance. No third-party manuscript is copied into this repository.

The initial screen considered arXiv and OpenAI/math but missed this
web/GitHub-hosted source. Future target screens must additionally check
general web searches, author pages and public proof repositories, using
equivalent formulations and exact quantifiers. A bounded search that
finds no result never proves present openness.

## Sources

- G.-S. Cheon and I. M. Wanless, *An update on Minc's survey of open
  problems involving permanents*, LAA 403 (2005), 314--342,
  <https://doi.org/10.1016/j.laa.2005.02.030>.
- F. Zhang, *An update on a few permanent conjectures*, Special Matrices
  4 (2016), 305--316, <https://arxiv.org/abs/1608.02844>.
- Y. Lavi, *A counterexample to the Foregger--Sinkhorn tie-point
  conjecture*, <https://arxiv.org/abs/2608.13025v1>.
- Earlier candidate and status pages linked above, inspected at the
  specified Git commit.
