# Bapat q-permanent: bounded OpenAI/math scope screen

Screen date: 2026-10-08. This is an incremental repository comparison, not a proof review or priority assessment.

## Target being compared

The synchronized note `notes/bapat-q-permanent-counterexample/proof.md` states Bapat's original conjecture: for every non-diagonal complex Hermitian positive-definite matrix (A), the inversion-weighted q-permanent

\[
P_q(A)=\sum_{\sigma\in S_n}q^{\operatorname{inv}(\sigma)}\prod_i A_{i,\sigma(i)}
\]

is strictly increasing in real (q\in[-1,1]). Its proposed (n=200) rank-two Gram construction followed by (+\varepsilon I) claims an exact counterexample inside the original interval. The note expressly does not settle the real-symmetric restriction and distinguishes proposed extensions beyond (q=1). This screen does not validate that construction.

## OpenAI/math checkout screened

Checkout: `/workspace/scratch/openai-math`, HEAD `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

I searched `CONTENTS.md`, `overview.tex`, preprint source files (Markdown, TeX, BibTeX), and Lean source for `Bapat`, `q-permanent`, `q permanent`, `mu-permanent`, `inversion-weighted`, and combinations of permanent with inversion. The only direct q-permanent/Bapat search hits were none. Generic mentions of “inversion” were unrelated mathematical uses.

The closest lexical false positive was the companion preprint **“A strict four-row permanent inequality and permutation moments”**, at `preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026/`, §§1–2. `CONTENTS.md` lists it among the companion sources for catalog entry **#238, “Optimal logarithmic mixing of the Thorp shuffle.”** Its theorem concerns the ordinary permanent expectation \(\mathbb E_\nu\prod_{i=1}^4f_i(\pi(i))\) for a marginal-preserving probability law on (S_4), used in a Thorp-shuffle argument. It has no q-parameter, inversion statistic, Hermitian-matrix hypothesis, or monotonicity assertion. It does not imply or refute Bapat's conjecture. Catalog entry **#096** is instead “The Gaussian propeller conjecture in every dimension”; it is not the Thorp-shuffle result.

The repo's “Gaussian propeller” and other permanent/quantum-permanent materials also concern different objects. No q-permanent/Bapat theorem or same-scope counterexample appears in the searched indexed public source tree. This conclusion is limited to the recorded checkout and search terms; it is not a GitHub code-search result or a claim about all OpenAI publications outside the checkout.

## 2026 outside-repository check

I queried the arXiv API on 8 Oct 2026 for `all:"Bapat" AND all:"q-permanent"`, `all:"Bapat q-permanent"`, `all:"inversion-weighted permanent"`, and `all:"q-permanent monotonicity"`; each returned zero records. A Bing RSS search endpoint was tested but returned irrelevant keyword-noise, so it is not counted as meaningful negative evidence. The target note's own external literature search (described in its §6 and referee report) reports no located general proof or counterexample before this construction, but this screen did not repeat that full review.

## Scope distinctions to preserve

- No OAI hit was found for the original complex-Hermitian monotonicity statement on \([-1,1]\).
- No OAI hit was found that proves/refutes only the real-symmetric subcase.
- No OAI hit was found for an extension of the q-domain beyond \([-1,1]\).
- Bapat–Sunder immanant/permanent-on-top results and de Sá noncrossing special cases are discussed in the target's bibliography, but the OAI source-tree search found no work matching them to this q-monotonicity target.
- Ordinary permanents, operator “quantum permanents,” and standard permutation-moment inequalities are different objects and were excluded from the match set.

## Bounded conclusion

No same-scope proved or refuted claim was found in the searched OpenAI/math snapshot or the arXiv query. This is a bounded non-match, not confirmation of novelty, priority, or global absence of a 2026 counterexample.
