# Post-publication comparison: logarithmic density and simplex products

This comparison was performed after the complete-source disclosure commit `e6c776cae39477baa4e1a03d59a1547417f1a68e` (2026-10-07 01:00:08 UTC). It does not modify the disclosed proofs or establish first priority. It is a narrow source comparison, not a comprehensive MathSciNet/Zentralblatt or full-corpus review.

## Manuscript 004: logarithmic density

1. **OpenAI, The geometric case of the Erdos similarity conjecture (October 5, 2026).** This is the explicitly acknowledged source of finite routing, local entropy and exceptional-center repair. The comparison is with the pinned commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, not an assertion about every future upstream revision. The proposed extension in 004 is the positive upper Banach density of occupied logarithmic annuli, proved using simultaneous density flattening. Countable simultaneous avoidance and infinitely many hits use summable budgets applied to all tails; they are consequences of that criterion, not a claimed resolution of arbitrary infinite configurations.
   Source: https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026

2. **Xiang Gao, Yuveshen Mooroogen and Chi Hoi Yip, On an Erdos similarity problem in the large.** Theorem 1.5 concerns an increasing sequence whose INTEGER PARTS have positive upper Banach density. That is not the condition in 004, which is imposed on LOGARITHMIC SCALE INDICES of a null configuration. Applying an exponential or logarithm does not preserve general affine copies, so a change of coordinates is not an immediate reduction. Their large-measure-in-every-unit-interval conclusion is already part of the literature and is not claimed as a new general format here.
   Sources: https://arxiv.org/html/2311.06727v3 ; https://doi.org/10.1112/blms.70062

3. **Alex Iosevich and Alexia Yavicoli, Falconer lattice sets and the Erdos similarity problem, arXiv:2604.01493.** The displayed Theorem 1.2 produces an infinite triple sumset inside a specified nested-lattice intersection, then applies Bourgain's theorem. This supplies a different class and mechanism. The squarefree-indexed dyadic configuration in 004 contains no nontrivial two-fold sumset, by uniqueness of two-term sums of dyadic powers. The cited nested-lattice theorem therefore does not directly imply this example by finding its additive witness inside it. This observation is a comparison of stated mechanisms, not an exhaustive non-implication theorem about all consequences of that paper.
   Source inspected: https://arxiv.org/html/2604.01493v1 (page labels the arXiv identifier as v1 from April 2, 2026, while its manuscript date is August 24, 2026; these are recorded as displayed, not reconciled by assumption).

4. **Jung, Lai and Mooroogen, Fifty years of the Erdos similarity conjecture.** The survey is cited for background only, not for the new criterion. Its January 2025 version cannot settle priority relative to later work.
   Source: https://arxiv.org/html/2412.11062v2

## Manuscript 005: simplex products

1. **OpenAI, A product counterexample to the simplex maximum for projection-body volume (September 24, 2026).** The product identity, simplex value and 10+10-dimensional witness are inherited and credited, not claimed as new. Our additional statements concern optimization over every integer partition, the unique root-optimal block thirteen, the sharp recurrence threshold 100, uniqueness of the optimal dimension multiset, and the sharp stability constant 112.
   Source: https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-product-counterexample-to-the-simplex-maximum-for-projection-body-volume-September-24-2026

2. **Yibin Feng, Shengnan Hu, Weiru Liu and Lei Xu, On the Reverse Projection Inequality.** The author-uploaded archive abstract states counterexamples in every dimension n>=9 using polytopes with at most n+2 facets. Thus neither the first unrestricted counterexample nor a smallest general counterexample dimension belongs to 005. In this pass the archive abstract was checked; no claim is made to have independently audited that paper's full proof.
   Source: https://archive.ymsc.tsinghua.edu.cn/pacm_paperurl/20260821091122099811781

## Search limits and conclusion

Targeted web queries included combinations of 'Erdos similarity', 'logarithmic', 'upper Banach density', 'projection body', 'products of simplices', and 'thirteen'. Both available search indexes were used; many results were unrelated. No equivalent version of the two principal stated extensions was located in the sources compared above. This negative search result does not certify novelty, journal significance, or priority. General separable integer-optimization literature and the complete upstream catalogue have not been exhaustively compared.

The source commit and versioned release document what was disclosed. They do not certify correctness, exclusive rights to a theorem, or first discovery. Corrections or newly found prior results should be recorded in a new commit without rewriting earlier disclosure history.
