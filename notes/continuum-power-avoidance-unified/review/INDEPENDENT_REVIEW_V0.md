Public derivative note: two private delivery-identifier lines were omitted. Mathematical review text is unchanged; original report SHA-256 is recorded in PROVENANCE.json. This is the superseded v0 review, retained to show the correction history.

# Independent review of the unified avoidance manuscript

Date: 2026-10-07. Scope: traditional mathematical proof, exact quantifier order, citations, and all 14 rendered PDF pages. Frozen sources and manuscript source were not edited. No Lean build was used as a substitute for checking the written proof.

## Verdict

The main construction is mathematically coherent and independently readable. I found one real omission in an intermediate lemma statement: the early-start restriction needed for the sample count has not yet been imposed when Lemma 4.1 invokes it. The final schedule already imposes it, so the main theorem's actual application is valid. This should be corrected before submission rather than dismissed because formal proofs exist.

After the standing-hypothesis correction described below, I found no unresolved mathematical gap in the main theorem, its geometric/compact corollaries, or Proposition 9.1. This is an independent AI proof audit, not a claim of human peer review, journal acceptance, or exclusive priority. A revised manuscript still requires diff and condition-propagation review.

## Input identity and audit evidence

- ZIP: continuum-avoidance-paper-and-evidence.zip, 3,887,507 bytes.
- ZIP SHA-256: 6b5f63f2d53720288b2f71b82cbd0a0c94ba6d36fa5a6dc8835105d2e795eb4a.
- PDF: 14 A4 pages, 368,642 bytes; SHA-256 ad6c51378aa6105336183ead1596b8310c4d5bc76544e79938881effc9ab14d2.
- All 30 outer-manifest file sizes and hashes matched.
- The preserved geometric archive verified all 358 manifest hashes; its ZIP SHA is 747386b02dbd12ae6f7b763d79fdb1e9bd70ca1e195e1b84d943cb0bcff82cb5.
- The preserved stronger archive verified all 228 manifest hashes; its ZIP SHA is b8fb480b8888321b864cf3c58a81cad3dfc223cc837071b940be58a93cca0e51.
- All 45 reused geometric modules are byte-identical across those archives.
- Independently checked all 57 mapped declaration short names at their claimed source lines and source hashes, covering 20 steps. Existence/name correspondence is not itself proof of mathematical equivalence.

## Required correction R1: missing standing lateness hypotheses

Location: PDF pages 4-7; TeX lines 232, 336-345, 435-456.

Lemma 2.2's lower count needs u >= s1*z1-k. Lemma 4.1 assumes only L >= ceil(2D), then asserts at least eta*(b-1)*Lr active tests. At that point the template start U remains an arbitrary integer. The lemma as a standalone statement is false.

Exact counterexample mechanism: fix s0,s1,k and the syndetic-gap constants; take an admissible configuration and sample starting sufficiently late that s0*z1-k > U+T. Sampling can start arbitrarily late without increasing its log-gap constant B0, hence without increasing D. Choose the permitted L >= ceil(2D) and an early U >= 4. All windows have no active indices at every exponent in the rectangle. The all-local-tests-fail event has conditional probability 1 on any first-default exposure atom, contradicting exp(-lambda*Lr) < 1.

Minimal repair, before constructing grids/probability spaces in Section 3:

For the rest of the routing construction assume L >= max{2,ceil(2D)} and that U is an integer with U >= 4, U > |k|, and U >= s1*z1-k. Further restrictions will be imposed in Section 6.

Equivalent fixes may add these hypotheses separately to the probability and entropy lemmas, but a single standing convention is less error-prone. It also ensures N_v=2^(v+3) is an integer grid size, the no-wrap separation applies, and candidate/error inequalities use U+k>0.

Propagation checked:
- Every u_e >= U, so Lemma 2.2 applies to every outgoing edge at every s.
- Every Lr >= L, so count and entropy requirements hold.
- U >= 4 supplies the geometry premise in Lemma 3.2 and fixed-parameter miss argument.
- U > |k| is already assumed in the representative construction and is used later for the active-error estimate.
- Section 6's L(U) includes ceil(2D) and 2; equation (21) explicitly includes all three U restrictions. Therefore the eventual schedule meets the proposed standing conditions for all sufficiently large U, with no circularity and no loss of the theorem's stated scope.

The corresponding formal sampling and assembly declarations explicitly carry hstart; this is evidence that the manuscript dropped a hypothesis, not a reason to ignore the written omission. No change to the frozen mathematical Lean sources is called for.

## Recommended wording precision

R2. PDF p5 / TeX 306-307: the own-grid width 2^(-u_e-Lr-2) is exactly one quarter of the displayed lower bound 2^(-u_e-Lr), not less. It is strictly less than one quarter of every actual active offset. Replace the sentence accordingly. Separation remains valid.

R3. PDF p7 / Lemma 5.2: say explicitly that for an exposure atom C, P(C intersect {there exists a parameter with local miss}) <= P(C)*5120*b^2*(U+T+|k|+2)^2*exp(-kappa*ell). The current 'On an atom ... probability ... atom mass times' wording can be mistaken for a conditional probability times atom mass. The proof uses the correct joint probability.

R4. PDF p10 / TeX 695-699: in the closed-activation illustration, specify the ambient exponent domain, for example s in [1/2,5/2], while the activation interval is [1,2]. Otherwise the sequence s<1 used in the example appears to leave the parameter space. The intended elementary example is correct.

R5. Definition 1.1: explicitly write j in N, j>=1, and quantify integer j>=J. Integer bins are plainly intended, but this avoids leaving the ambient type implicit.

R6. Submission metadata: the author field is intentionally blank. Actual submission requires the user's authorship/contact choice. The long Lean names on pp12-14 wrap legally but are visually dense; moving detailed module lists to the supplement is optional, not mathematically required.

## End-to-end proof audit

1. Statement and quantifiers: the countable configuration family is fixed before E. The same E then handles all positive real s,alpha, all translations, nonzero signed coefficients, finite error constants, arbitrary tail domains, and arbitrary maps with an eventual bound. No measurability of A or f is used. The conclusion is infinitude of distinct output values in every input tail.

2. Separated sampling: occupied-bin syndeticity produces a decreasing sample with log gaps strictly between 3/s0 and B0. The strict open-window count works at both endpoints; its lower bound uses the late-start premise identified in R1. The proof covers the window by r+1 successive gaps and retains enough slack at length >=2D.

3. Tree schedule: the preorder span recurrence is consistent, including gaps and default edges. A local edge plus its subtree has span at most 2Lr, while total T is affine in base length L with fixed tree constants. These local spans are essential to avoiding a global-grid entropy loss.

4. Actual periodic geometry: all grid sizes are nested dyadic integers after imposing U>=4. Bad-center intervals have total density at most K*2^(3-g). Stable centers give all needed preceding grid addresses. Own/test addresses are distinct, persist at finer grids, and cannot coincide modulo one because offsets lie in an interval shorter than 1/8. Boundary floors consistently use left-closed/right-open cells.

5. Random-set density: conditional on all selector entries, the terminal entry for any point remains Bernoulli-p. The random set is a finite union of cells of the actual finest grid N=2^(U+T+2), so E dens(B)=p by finite summation and integration.

6. Center exposure and first default: exposing the center's entry in every selector table is sufficient. At each reached level, its fresh selector entries make the probability of no default exactly (1-2^(1-b))^d. Preorder stability makes candidate points follow the center through strict ancestors and pass the earlier siblings at the first-default vertex.

7. Local-test probability: own selector coordinates are distinct and outside the center exposure. After conditioning on all selector entries, terminal coordinates are pairwise distinct for every assignment: different child subtrees/leaves have different tables; points ending in the same leaf retain different keys. Therefore failure conditional on selectors is (1-p)^(sum A_j), and averaging the free own-selector bits gives exactly (1-p/2)^m. No independence of whole routes is assumed or needed.

8. Continuum representatives: the active candidate set is finite with the claimed absolute-position-dependent bound P. Activation cuts and lifted local-grid crossings are affine in (s,log t). Full sign vectors, including zero signs, determine inactivity or the exact local finest-grid address. This determines every table read independently of outcomes. Boundaries at x itself and at the strict upper offset limit need no cuts because active offsets are strictly between those bounds.

9. Sign count and entropy: the planar-stratum count <=2m^2+1 handles repeated lines, constants, vertices, and edges. Restriction to the closed rectangle adds no patterns. The bound 20[P(3+2^(2ell+3))+5]^2 is valid. P<=b(U+T+|k|+2) and P(3+2^(2ell+3))+5<=16P2^(2ell) yield constant 5120 and kappa=lambda-4log2. The representative set is chosen before the remaining random tables; its dependence on x requires no measurable selection.

10. Noncircular choice: b,d,K,g are fixed first. L(U)=O(log U), and T(U)=O(log U) with a possibly enormous but finite fixed constant. Hence T(U)<=U eventually. The explicit entropy bound tends below p at those same values. The positive remainder exponent makes 4N*r_U=2^(T(U)+4)*(q2^(-k)+1)*2^(-alpha0*(U+k)/s1) tend to zero. Increasing U satisfies every restriction simultaneously; no parameter is chosen in terms of an already-dependent parameter.

11. Buffer and missed-center measurability: B1 and B2 are open periodic thickenings. Their density cost uses the actual finest grid N. Potential active indices are finite. Open activation makes 'inactive or missed' closed in the full center/parameter product; compact parameter projection makes R closed. The finite outcome space makes all expectation/interchange arguments ordinary finite sums of measurable indicators.

12. Every-center repair: expected dens(B2)<2p and expected dens(R)<=3p yield one common outcome with their sum <=5p. Closed periodic R has a periodic open thickening of density <dens(R)+p. Outside R, an active B1 hit remains in B2 under every allowed error. Inside R, the entire sampled tail converges to the center even with errors, so eventually enters its open repair neighborhood. No random or independence assumption about the errors is made.

13. Countable exhaustion: summable budgets are assigned only to configurations, exponent rectangles [1/N,N], reciprocal remainder gains 1/j, dyadic coefficient scales k, integer error bounds q, and input cutoffs h. Reflection handles c<0. This produces a single E independent of all later maps/parameters. The strict total budget gives strict >1-epsilon measure in every real unit interval by periodicity.

14. Distinctness, topology, and corollaries: the two-sided leading-term estimate forces hit values to be noncentral and converge to y, so they cannot form a finite set. The identity map on one prescribed configuration excludes an interval in E. Taking E intersect [0,1] preserves all misses and gives compact nowhere density. The dyadic singleton configuration and s=-log2(q) correctly give one common compact set for every geometric ratio and every affine coefficient/center/tail.

15. Scope controls: the finite threshold r=7/160 example is arithmetically correct, including the endpoint counterexample and strict interior success. Proposition 9.1 correctly constructs logarithmic upper Banach density one while defeating every O(log U) uniform output window: at most one tiny occupied block lies in the candidate range and its activating exponent interval has length tending to zero. It is correctly limited to an obstruction to this mechanism, not to the broader theorem.

## Primary-source comparisons

- BGKMW Question 1 explicitly includes a translation and an existential ratio; its Theorem 1.1 only avoids untranslated progressions. The manuscript's Corollary 1.4 genuinely negates Question 1. Verified against the original arXiv HTML/PDF, not merely its abstract: https://arxiv.org/html/2210.09284v1 . This comparison does not certify current worldwide priority.
- Kolountzakis-Papageorgiou, Theorem 4.1 and its proof, pp13-14: parameter-space hyperplanes and polynomially many representatives are indeed prior ingredients. The paper describes the precedent accurately without importing it as a missing proof: https://arxiv.org/pdf/2208.02637v2 .
- Feng-Lai-Xiong, Theorem 1.1, printed p3: fast-decay hypothesis gives a bi-Lipschitz embedding differentiable at zero with derivative one, hence an o(a) remainder at dyadic inputs, without a promised positive power rate. The stated boundary comparison is accurate: https://arxiv.org/pdf/2312.01319v1 .
- The pinned OpenAI introduction/main files explicitly fix q before choosing E and identify OpenAI in their author field. The manuscript's attribution and fixed-ratio comparison are correct: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026/build/sections/01-introduction.tex .
- The pinned profile source Theorem 3.1 prescribes countable profiles/moduli with positive logarithmic upper Banach density. It expressly declines a continuum-of-exponents assertion. The manuscript accurately distinguishes that scope: https://raw.githubusercontent.com/mxym/math/87868bcb65bf0460a90d6bc2efc3324e46481230/preprints/006-modulus-nonlinear-similarity/v2/paper.md .

## Reproduction and presentation

The appendix correctly says the old KernelReplay.lean is only an import, and does not pretend the paper package contains the later true replay. The later independent replay files and logs already exist in the separate verified audit; joining that material is an evidence-packaging improvement, not a mathematical correction. A future package should cite or include the actual programs/logs and their manifests rather than repeat attributed counts alone.

All 14 PDF pages were rendered and visually inspected. No clipped equations, overlaps, missing glyphs, unresolved references, or overfull boxes were seen. The source log has only harmless underfull boxes and disabled-shell-escape warning. Theorem 1.2, repair proof, and geometric corollary cross page breaks without loss of text. The correspondence table is dense but legible; all long names wrap inside the page. Author/PDF metadata remain intentionally blank.

## Next verification gate

Check the revised TeX diff for R1-R4, confirm no changed theorem scope or frozen archives, recheck all earlier probability uses inherit the added hypotheses, compare new manifest/hash, and inspect the new PDF pagination. The current result is 'main proof checks out; manuscript requires the stated local correction', not an unconditional claim that the supplied v0 is ready for submission unchanged.
