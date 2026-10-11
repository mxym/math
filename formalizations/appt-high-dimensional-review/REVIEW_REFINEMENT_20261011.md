# Baseline-sensitive graph and scalar variance refinement

This continuation formalizes two further proof dependencies without asserting the assembled APPT purity theorem.

`baseline_graph_refined_budget` works for every nonnegative, symmetric, zero-diagonal row-major matrix G of size m=h+1, a nonnegative baseline w, and positive cap c. With B=G+w*A_complete and c*I-B positive semidefinite, it proves exactly

    m*sum_(i<j) G_ij^2 + 4h*w*sum_(i<j) G_ij + m*h^2*w^2 <= 2m*c^2.

The two upper-triangular sums are represented respectively as the sum of row energies and the sum over the proved UpperPair finite type. `degree_background_identity` proves the complete expansion before squaring, including the 4h*w cross term. No chosen graph shape replaces the row-order, symmetry, sign, and PSD hypotheses.

`sorted_centered_variance` works for every decreasing real length-D vector of sum one, every positive R with 2R<=D, delta_i=f_i-f_(D+1-i), and w=f_R-f_(D-R+1). It proves

    sum_i f_i^2-1/D <= sum_(i=1)^R delta_i^2 - w*sum_(i=1)^R delta_i + D*w^2/4.

A full finite three-band decomposition pairs top and reversed bottom entries and bounds the middle interval. The least-squares centering term is retained exactly; no probability sign assumption is required beyond the explicitly stated ordering and unit total. The API is generic in D and R, not a special dimension or finite enumeration.

A fresh local package build, regression run and empty-kernel replay passed with 41,969 declarations, 49 roots and 44 hash-pinned inputs. Only propext, Classical.choice and Quot.sound are allowed. The first root's proof, baseline_graph_refined_budget, was replaced by True.intro with its type unchanged and rejected. The prior independently replayed physical paired-gap root and other physical endpoints remain in the closure. Local kernel log SHA-256: ba94d692328e18cebf73c2179f673c71cbfc6335cbf6ec50b2198c1f63c03571. Source-manifest SHA-256: d7eb97899292bd7a9f5b1acf92f3c968b46cee5dbbe3951c5b6e1067a044d4d4. Remote CI is recorded separately after source binding and positive replay.

Still missing: instantiating the baseline with the final paired gap in the actual spectrum, assembling these inequalities into the sharp max{8,4+D/(m-1)^2} centered-purity root, normalization, quantum purity/eigenvalue moment connection for that root, and all previously listed upper optimizations and asymptotic arguments. These modules close dependencies, not those remaining claims. No preprint or Release is created.
