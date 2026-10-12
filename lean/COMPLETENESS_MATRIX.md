# Formalization completeness matrix

This checkpoint adds proofs without claiming the whole paper is formalized.
The 101 public exports are supporting results and mechanisms, not 101 separate
published paper theorems. Compiler-generated auxiliaries are audited but excluded
from that public source-declaration count.

| Component | Status | Exact scope / remaining requirement |
| --- | --- | --- |
| Original finite/scalar project | PROVED, unchanged | All 68 original signatures, axiom sets and protected proof/pin/reference/vendor bytes are identical to the 72d04 revision. Their original per-theorem assumptions remain explicit. |
| Finite stochastic determinant rigidity | PROVED | Seven exact exports, including near-permutation and zero-defect permutation results for nonnegative column-stochastic real matrices. No actual-simplex correspondence is inferred. |
| Closest support, cap ball, Haar gain | PROVED | Actual sets, derived closest point/normal for nested bodies, actual inclusion/disjointness and intrinsic volume gain. |
| Unit-ball cube volume estimate | PROVED | Actual canonical Euclidean volume, dimension m >= 1, bound (2/m)^m. |
| Orthogonal projections and codimension | PROVED | Actual projected convex bodies, inherited ball bounds, preserved functional and hyperplane dimension d-1. |
| Projection-cap to Hausdorff endpoint | PROVED | For d >= 2, B subset K subset P subset M B and M,eta >= 0, an upper bound eta on every actual intrinsic hyperplane projection-volume deficit implies d_H(K,P) <= (d-1)(M+1) eta^(1/(d-1)). Includes eta=0. The deficit hypothesis is required. |
| Exact constants | DEFINED; positivity PROVED | R0,b,M,Q,L,J,rSharp,eSharp,aSharp,gSharp are explicit; ten exports prove only positivity in their printed dimension ranges. |
| Entry functional, pyramid, projection body, defect, simplex, centroid dilation, excess, truncation | DEFINED, typechecked | Concrete mathematical definitions. Projection-body support representation and functional correspondence remain unproved. |
| sharpMainGoal | DEFINED, unproved | Universal full-dimensional body and every maximum inscribed simplex, original centroid, explicit gSharp and exponent 1/(d-1). |
| sharpLocalGoal | DEFINED, unproved | Same body/simplex quantifiers, explicit nonnegative local defect and eSharp threshold; no threshold gate is assumed as a proved dependency. |
| thresholdGateGoal | DEFINED, unproved | Explicit aSharp(d) eSharp(d)^(1/(d-1)) <= 1/2 for every d >= 3. Positivity does not prove this. |
| truncationSharpnessGoal | DEFINED, unproved | Concrete truncation bodies, maximum simplices and arbitrarily small positive defect. The corrected target explicitly requires 0 < entryDefect(K) < epsilon. |
| simplexMatrixVolumeInterfaceGoal | DEFINED, unproved | Concrete augmented vertices and barycentric matrix. Invertibility, stochasticity, barycentric reconstruction, finite positive actual volume, and determinant/real-volume ratio are outputs to prove. |
| Arbitrary-body cone law / determinant representation | MISSING | No cone law, normalization, determinant integral or general centered-law identity is supplied as an axiom or theorem. |
| Cauchy projection identity | MISSING | No derivation of genuine projection deficits from entryDefect. |
| Minkowski / first-variation scale control | MISSING | No scale-repair or mixed-volume interface is formalized. |
| Integrated witnesses / nonatomic anchor assignment | MISSING | The finite matrix and finite defect mechanisms do not implement this analytical bridge. |
| Every-maximum-simplex affine normalization | MISSING | Maximum existence/normalization, shrink containment and maximality consequences remain unproved. |
| Actual simplex-volume bridge / same-centroid conversion | MISSING | The stochastic theorem cannot yet be applied geometrically. |
| End-to-end local/global assembly | MISSING | No complete sharp simplex stability theorem is present. |
| Actual truncation sharpness | MISSING | No exact defect formula, maximum-simplex argument or asymptotic sharpness proof for the truncation family is present. |

No dependency marked DEFINED or MISSING is counted as a proved theorem.
No custom axiom, sorry or native proof shortcut closes these gaps. The written
paper snapshot is source material, not evidence that its unformalized sections
have been checked by Lean. No novelty, priority or best-known-result claim is made.
