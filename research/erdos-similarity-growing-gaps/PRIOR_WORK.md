# Prior-work comparison: growing logarithmic gaps

**Scope.** This is a finite source comparison for the statement in `paper.md`, not a proof review or a literature-wide priority determination. The relevant conclusion is positive-measure affine non-universality: for each prescribed sequence in the stated family, the paper constructs a closed periodic set of measure arbitrarily close to one that avoids affine copies, and also handles the specified power-controlled perturbations. The comparison separates exact affine avoidance from dimension-one avoidance and from bi-Lipschitz embedding.

## Closest sequence-avoidance result

Angel Cruz, Chun-Kit Lai, and Malabika Pramanik, “Large Sets Avoiding Affine Copies of Infinite Sequences,” *Real Analysis Exchange* 48(2) (2023), 251–270, [arXiv:2204.12720v1](https://arxiv.org/abs/2204.12720), [DOI 10.14321/realanalexch.48.2.1681628520](https://doi.org/10.14321/realanalexch.48.2.1681628520). The full arXiv text was read; the downloaded PDF hash is recorded in `SOURCES.json`.

Their Theorem 1.1 and Corollary 1.2 assume a decreasing null sequence satisfying

\[
 \log(a_n/a_{n+1})=e^{\phi(n)},\qquad
 \phi\text{ strictly increasing},\qquad \phi(n)/n\longrightarrow0.
\]

They construct a Borel set of Hausdorff dimension one avoiding every nontrivial affine copy of \(A\cup\{0\}\). For the explicit family
\[
 a_n=2^{-n(\log\log(n+20))^\beta},\quad 0<\beta<1,
\]
the natural-log gap is asymptotic to \((\log 2)(\log\log n)^\beta\), so one can take \(\phi(n)=\beta\log\log\log n+O(1)\), sublinear. Strict increase follows separately, rather than from this asymptotic: for $z(x)=x(\log\log(x+20))^\beta$, direct differentiation gives $z''(x)\sim\beta(\log\log x)^{\beta-1}/(x\log x)>0$ eventually. Hence the increments $z(n+1)-z(n)$, and their logarithms, are eventually strictly increasing. Discarding a finite prefix places this example within their hypothesis; avoiding a tail also avoids the whole sequence.

The measure quantifier is different. Their Theorem 1.1 gives a compact set \(K\) of arbitrarily large measure whose Erdős-point set \(E_K\) has Hausdorff dimension one; \(E_K\) is the Borel avoiding set in Corollary 1.2. They prove that a particular subset \(O\subset E_K\) has measure zero (Proposition 4.4), but do **not** prove that all of \(E_K\) is null. Section 4.4 explicitly asks whether \(m(E_K)>0\); a positive answer there would prove non-universality for the sequences covered by their condition. Consequently, their theorem does not already supply the positive-measure avoiding set in `paper.md`. The present explicit example is covered by their dimension-one conclusion, while its positive-measure conclusion is a stronger measure statement.

The general hypothesis \(z_{n+1}-z_n=o(\log\log z_n)\) does not itself impose the monotonicity of \(\phi\) required in the CLP statement. No equivalence of those hypotheses is asserted here. The intermittent-annulus condition in Theorem 2 also permits arbitrarily large gaps outside the selected windows, a regime not stated in CLP's theorem.

## Bi-Lipschitz embedding is a different conclusion

D.-j. Feng, C.-K. Lai, and Y. Xiong, “Erdős Similarity Problem via Bi-Lipschitz Embedding,” *International Mathematics Research Notices* 2024(17) (2024), 12327–12342, [arXiv:2312.01319v1](https://arxiv.org/abs/2312.01319), [DOI 10.1093/imrn/rnae167](https://doi.org/10.1093/imrn/rnae167). The full preprint text was read; its PDF hash is recorded in `SOURCES.json`.

Their Theorem 1.1 says that if a positive decreasing null sequence satisfies
\[
 \limsup_{n\to\infty} a_{n+N}/a_n<1
\]
for some fixed integer \(N\), then every positive-measure set contains \(f(a_n)\) for a bi-Lipschitz map \(f:\mathbb R\to\mathbb R\) differentiable at zero with \(f'(0)=1\). The example above satisfies the ratio hypothesis with \(N=1\). This is not affine universality: differentiability gives an \(o(a_n)\) remainder, not the power-controlled \(O(a_n^{1+\alpha})\) remainder in the present theorem, and it does not force \(f\) to be affine. The two results concern different classes of embeddings.

## Fixed geometric ratios and earlier repository scope

OpenAI Mathematics, “The Geometric Case of the Erdős Similarity Conjecture” (5 October 2026), Theorem 1.1, proves positive-measure affine non-universality for each fixed geometric sequence \(\{q^n:n\ge1\}\), for every \(q\in(0,1)\); its avoiding set may depend on \(q\). The source text was read; the PDF is available at [the pinned source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026/geometric-erdos-similarity.pdf). This is an important method and exact-geometric precedent, but it does not state the variable-ratio theorem for (4) or the intermittent-window class.

The repository's earlier `manuscripts/continuum-power-avoidance` theorem assumes bounded gaps in occupied dyadic logarithmic bins for each configuration. The earlier `preprints/006-modulus-nonlinear-similarity/v2` result assumes positive logarithmic upper Banach density. The paper's examples (4) and (28) have zero upper Banach density of occupied bins, and (28) has arbitrarily large gaps between its useful annuli, so these earlier hypotheses do not cover the new cases. The finite routing, parameter sign-arrangement, and open-repair mechanisms are explicitly inherited and reproved in the current paper; the attribution is to the variable-parameter schedule and annular sampling scope, not to invention of those mechanisms.

Other 2026 work found in the targeted arXiv search addresses different objects. A. Iosevich, N. Kulkarni, N. Mora Cuéllar, I. Rojas Aravena, and A. Yavicoli, “The Erdős Similarity Conjecture and Rajchman Measures,” [arXiv:2609.04456](https://arxiv.org/abs/2609.04456), proves large-set avoidance for sets supporting a Rajchman probability measure; a countable sequence cannot support an atomless probability measure. N. Mora Cuéllar, A. Iosevich, N. Kulkarni, I. Rojas Aravena, and A. Yavicoli, “The Erdős Similarity Conjecture for Two-Fold Sumsets with a Geometric Summand,” [arXiv:2607.03584](https://arxiv.org/abs/2607.03584), proves non-universality of the sum or difference of a geometric sequence and an arbitrary infinite set, and more generally certain two-fold sumsets containing a lacunary summand. Neither abstract states a theorem for the single variable-ratio sequence here. These two entries were checked at abstract level only, not full-text theorem verification.

## Search limits and attribution

The comparison checked the primary full texts of CLP and FLX, the cited 2026 fixed-geometric research manuscript, the current repository avoidance results, and a targeted arXiv search for recent Erdős-similarity work through 8 October 2026. It did not exhaust journal databases, unpublished manuscripts, or all follow-up citations. No first-result or worldwide-priority claim follows from this screen. CLP's positive-measure question is an especially close open comparison for its regular-gap subclass; the current paper's positive-measure conclusion should be positioned as the stated growth-gap and intermittent-window extension, with inherited routing machinery credited.
