# Research selection, prior work and next obstruction

**Date:** 7 October 2026. **Upstream snapshot:** `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Actual scope of the scan

The upstream catalogue was scanned across its numbered result families, including its substantive descriptions for 084, 088, 092, 098, 100, 156, 191 and 374. This is catalogue screening, not verification of every theorem. The full product-counterexample source in family 088 was examined for its facet formula, affine covariance, product identity, simplex value and exponential-product mechanism. The projector-geometry and strict-gap reduction section of family 156 was also read directly. For 084 and 374, the immediately actionable developments were examined through the complete shared manuscripts 004/006 and 001/007's available statements and dependency audits; no assertion is made that every upstream dependency was re-proved.

Four candidates emerged. The projection-volume direction had an explicit obstruction in 005: its complete optimizer was confined to products. The similarity direction had room for irregular scales and perturbation moduli, but concurrent tasks had already produced 004 and 006 covering those extensions. The transport direction had room for tail-sensitive interpolation, which the newly published 007 addressed; redoing it would duplicate work. The Borsuk projector construction raises a dimension-reduction question, but the trace-one dimension count alone does not preserve the global topological obstruction on an eight-dimensional slice. No such dimension reduction is claimed.

The selected route was therefore to enlarge the projection-volume construction grammar and derive a closed invariant calculus, rather than to add more partitions to 005's already complete optimization. It leads to arbitrary-body formulas, a rigidity statement for equality among polytopes, a universal obstruction to a fixed optimal repeated block, a sharp finite recursive-class theorem, and an infinite self-similar family.

## Post-disclosure literature comparison

The core source was made public in commit `09c1d3e10839ac76eb3c861472c2ead3a929f1b9` before this focused follow-up. The entries below are evidence about related work, not a comprehensive novelty certificate.

**Brannen (1996).** N. S. Brannen, *Volumes of projection bodies*, Mathematika 43(2), 255–264, DOI [10.1112/S002557930001175X](https://doi.org/10.1112/S002557930001175X). The publisher's abstract describes the proposed simplex maximum and a counterexample to a different centrally symmetric upper bound. The conjecture is historical context, not our invention.

**Lutwak–Yang–Zhang (2001).** E. Lutwak, D. Yang and G. Zhang, *A new affine invariant for polytopes and Schneider's projection problem*, Transactions of the AMS 353(5), 1767–1779, DOI [10.1090/S0002-9947-01-02726-X](https://doi.org/10.1090/S0002-9947-01-02726-X); [author-hosted paper](https://cims.nyu.edu/~yangd/papers/trans.pdf). Its introductory bounds and Definition 3.1 were inspected in the actual PDF, with the displayed formulas checked visually. It defines a centro-affine functional using products of facet cone-volume weights indexed by independent normal tuples. Our displayed a uses a translation-invariant ratio involving lifted (d+1)-minors. These are different definitions; this observation does not exclude a deeper relationship or establish priority for either our invariant or our join formula. Corollary 4.12 gives a general upper bound

$$R_d(K)\le d^d(d+1)^{(d+1)/2}(d!)^{-3/2}.$$

That existing upper-bound theory is distinct from the explicit lower constructions here. We do not claim to close its gap or to improve the best known unrestricted asymptotic bound.

**Saroglou (2011).** C. Saroglou, *Volumes of projection bodies of some classes of convex bodies*, Mathematika 57(2), 329–353, DOI [10.1112/S0025579311001860](https://doi.org/10.1112/S0025579311001860). The publisher's primary abstract explicitly covers sharp three-dimensional zonoid, cone and double-cone extrema and equality cases. Thus projection bodies of cones are not a previously unstudied subject. The full text was not obtained in this pass; comparison of its cone identities with our general-dimensional calculus remains necessary. No assertion of disjointness is made.

**Feng–Hu–Liu–Xu (2026).** Y. Feng, S. Hu, W. Liu and L. Xu, *On the reverse projection inequality*, MathSciDoc 2608.23002, [author-uploaded archive record](https://archive.ymsc.tsinghua.edu.cn/pacm_paperurl/20260821091122099811781), and [Zenodo record](https://zenodo.org/records/22037130), DOI 10.5281/zenodo.22037130. Both records state counterexamples in every dimension n >= 9 with at most n+2 facets. The upstream 088 manuscript also explicitly credits this earlier result. PDF retrieval failed in this pass; the direct confirmation is the primary abstract, not an independent audit of their construction. Consequently our n >= 14 pyramid family is not a new smallest-dimensional unrestricted counterexample. Its role is an exact, simple witness in a class for which we also prove the sharp threshold.

**OpenAI family 088 and shared 005 v1.1.** The upstream source rederives the classical product and simplex ingredients and gives a two-ten-dimensional-simplex witness. Version 1.1 of this shared entry already optimizes over all simplex products, with asymptotic root c13^(1/13) approximately 2.8099647. Those are credited inputs. The present formulas for lifted data, joins, equalities, universal amplification and self-similarity are the additional results recorded in v2; a systematic literature review may show some of them to have antecedents.

Public search in both engines for combinations of projection-body volume, joins, pyramids, cones and asymptotic maxima did not identify an exact match for the complete two-invariant recursive framework or the stated self-similar family. Search non-detection is not evidence of first discovery. MathSciNet/zbMATH's complete coverage, all citing papers, and full cone literature have not been exhausted.

## Highest-value next mathematical step

The exact optimum in the product/join closure in arbitrary dimension is the central remaining target. A finite list of candidate repeated blocks cannot settle it, because Theorem 7.1 strictly improves every such individual block. Finite numerical hulls likewise cannot certify an infinite-dimensional upper bound.

The concrete missing object is a dimension-uniform family of upper regions in the (R,aR) plane, preserved under both positive bilinear operations, together with a matching construction. One must either prove a sharp preserved envelope or develop a verifiable limiting Bellman-type equation with certified truncation error. The present rational hull certificate stops at dimension fourteen; the analytic tail certificate controls one explicitly prescribed self-similar recursion, not all possible recursions.

A second question is equality and quantitative stability for the bound a >= 1/(d+1) beyond polytopes. The exact polytope equality proof is complete here. Mere Hausdorff continuity of a does not pass rigidity to arbitrary limits, so that extension needs its own argument; no limit-of-strict-inequalities shortcut is permitted.

The fourteen-dimensional construction, finite sharpness and asymptotic 1.015^n improvement are useful consequences, but the two-invariant calculus and universal no-fixed-block theorem are the main structural outputs. Their publication value should be judged after the outstanding literature comparison and external mathematical review, not assigned a journal tier in advance.
