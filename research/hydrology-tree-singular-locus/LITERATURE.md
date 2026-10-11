# Literature and novelty audit

Search cutoff for this cycle: 11 October 2026. Sources below are primary papers or their authors' manuscript pages. A search failure is not evidence that no earlier proof exists. No external mathematician has reviewed this new proof.

## Exact targets, rather than a broad hydrology claim

1. Elizabeth Gross, Nicolette Meshkat, and Anne Shiu, *Identifiability of linear compartmental models: the singular locus*, final arXiv text 28 June 2021, arXiv:1709.10013; journal publication in Advances in Applied Mathematics (2022).
   - https://ar5iv.labs.arxiv.org/html/1709.10013
   - Section 5.3, Conjecture 5.5, equation (11): endpoint-input/output/leak catenary Jacobian monomial. Remark 5.6 explicitly reports the missing inductive step.
   - Section 5.4, Conjecture 5.9: exact coordinate multiplicities on arbitrary bidirected trees with root input/output/leak. The authors attribute the recursive rule to Molly Hoch, Mark Sweeney, and Hwai-Ray Tung.
   - Our edge-wise formula is the same catenary monomial up to parameter/coefficient ordering sign. For a child subtree of size s, our return exponent is s and outgoing exponent s−1. The scaling lemma excludes additional coordinate factors hidden in the resultants, closing the exact-multiplicity requirement.
   - Earlier author-hosted versions use different numbering (the catenary conjecture is numbered 5.3 in one early PDF); this package consistently uses the final text.

2. Saber Ahmed, Natasha Crepeau, Paul R. Dessauer Jr., Alexis Edozie, Odalys Garcia-Lopez, Tanisha Grimsley, Jordy Lopez Garcia, Viridiana Neri, and Anne Shiu, *Identifiability of Directed-Cycle and Catenary Linear Compartmental Models*, SIAM Journal on Applied Dynamical Systems 25(1), 304–350 (2026), DOI 10.1137/25M1728636.
   - https://epubs.siam.org/eprint/IXIEMIECP3TISXXACWXU/full
   - Section 6 explicitly discusses a possible future resolution of GMS Conjecture 5.5. It separately leaves multiple-input/output catenary classification open. Our result resolves the first stated polynomial problem, NOT that more general classification.

## Close results that are not new here

3. Cashous Bortner, Elizabeth Gross, Nicolette Meshkat, Anne Shiu, and Seth Sullivant, *Identifiability of linear compartmental tree models and a general formula for input-output equations*, Advances in Applied Mathematics 146, 102490 (2023), arXiv:2106.08487.
   - https://arxiv.org/abs/2106.08487
   - Graph-level generic local identifiability for a single input and output on a tree is already classified. We do not claim that classification; we determine the exceptional polynomial and exact multiplicities in a colocated-input/output single-leak family.

4. C. Cobelli, A. Lepschy, and G. Romanin Jacur, *Identifiability results on some constrained compartmental systems*, Mathematical Biosciences 47(3–4), 173–195 (1979), DOI 10.1016/0025-5564(79)90036-1.
   - https://www.sciencedirect.com/science/article/pii/0025556479900361
   - https://research.unipd.it/handle/11577/2509174
   - Its abstract and citations in GMS establish close earlier work on constrained tree-system inversion and the number of solutions. We did not obtain the full proof text in this cycle. Consequently we do not promote a proposed generic fibre-count formula as a new result. Global endpoint-path identifiability, and the factorial star degree, are already known.

5. Tyler Huneke and Tegan Keen, *On the Identifiability of Linear Compartmental Model Parameters*, Texas A&M REU report, 17 July 2025.
   - https://artsci.tamu.edu/mathematics/_files/_docs/reu/results/2025/huneke-keen-report.pdf
   - The report includes a different conjecture on generic solution counts for rooted trees and discusses the 1979 work. Its count conjecture is not the singular-Jacobian conjecture proved here. We do not claim to resolve its numbering or formula by analogy. The relevant pages were read as rendered PDF pages, not inferred from a search snippet.

## What is and is not proposed as a contribution

Proposed: the all-tree branch-resultant Jacobian identity; its extension to an arbitrary single leak location; the resulting written proofs of the two precise GMS conjectures; the direct full-resultant relation; the interior spectral-collision criterion and exact distinct-rates counterexample.

Not proposed as new: resultants, Vandermonde determinants, Schur complements, polynomial identity continuation, finite-dimensional spectral theory, diagonal symmetrization of positive tree matrices, the input-output coefficient approach, or generic local identifiability of tree compartment models. These ingredients are elementary or established tools, and the manuscript proves the tree-specific steps it needs.

Not claimed: a general nonlinear hydrological theory, an improved real-world forecast, a complete theory for unknown topology or multiple leaks, a universal cure for equifinality, or a formally checked Lean proof.

## Search record and limits

Both available web search engines were used with the original paper title, the exact conjecture numbers, the names Hoch/Sweeney/Tung, and combinations including:

    "catenary" "singular locus" proof conjecture 2026
    "tree conjecture" "singular" "compartmental"
    "catenary" "Jacobian" "continuant"
    "compartmental" "resultant"
    "tree" "singular-locus equation"

The final 2021/arXiv and 2026/SIAM texts were inspected directly. No searched result gave the exact general formula or a later proof of the two targeted conjectures. Unindexed manuscripts, unpublished proofs, terminology variants, and indirect consequences of older inverse spectral theory remain possible. An expert comparison is still required before claiming historical novelty or first resolution. The 2026 reference is stronger evidence of a live target than merely finding an old conjecture, but it does not establish worldwide priority.
