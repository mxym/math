# A type-A twelve wing cannot accompany two seven-unit twelve wings at rank 36

In the 12+12+12 triangle-wing decomposition at mod-seven Seidel rank 36, A+U+U is impossible. A denotes the connected tree-7350 type, and U the eleven unit types in the [published inventory](triangle-wing-twelve-currents.md). Its determinant test excluded the 36 same-sign U pairs. The following common mechanism excludes **all 30 remaining unordered U pairs**, six square choices times five nonsquare choices.

In the published representative A=(M0,M1,M0,(0,2,1,3)), two independent centered harmonic currents are
\[
 h_1=(2,1,6,5;\ 6,4,3,1;\ 6,3,4,1),\qquad
 h_2=(1,4,3,6;\ 6,4,3,1;\ 0,0,0,0).
\]
The checker verifies harmonicity and the entries directly; the pair-tag incidence span in the inventory shows their images in the actual marking space stay independent. The full 36-mark wing Gram has rank 32 (one constant, centered ranks 9,11,11). Its nondegenerate complement in the rank-36 form is four-dimensional, containing the totally isotropic plane of these two marks \(u_1,u_2\). Thus on far words of first-current value zero, the residual products are computed in the split plane \(u_1^\perp/\langle u_1\rangle\), where the image of \(u_2\) is nonzero isotropic.

Of the admissible pair tags \(e\) in A, fourteen distinct tags have \(h_1(e)=0\) and positive compulsory multiplicity. Twelve have multiplicity one and the other two multiplicity two: this test asks only for **one member of each of the fourteen distinct classes**, hence is a necessary relaxation even on the repeated classes. Form all full six-site words from one positive-multiplicity pair per component and exactly two contacts per physical wing. For \(a=-h_2(e)\) and the projected \(g_{zz'}\) of the 32 nonsingular basis rows, allow all \(d\in\mathbf F_7\) with \(2ad=-g_{zz}\), including every \(d\) if \(a=g_{zz}=0\). Pair adjacency \(4-g_{zz'}-ad'-da'\) must be 0 or 1; impose literal common-neighbor, near-pair capacity and adjacent-word quota tests exactly as for [BBU](bbu-hyperbolic-quotient.md). A fourteen-colour clique is necessary.

Fix the true physical order of A, not the ordering of the two other components. The independent [ordered U template procedure](buu-line-quotient.md) yields 12 physically ordered square-unit types and 13 physically ordered nonsquare-unit types. All 156 choices of the ordered square and nonsquare templates are covered. The [exact smallest-domain checker](auu_plane_quotient.py) rejects every chart, maximum 68,177 nodes and no numerical solver; native total about 3½ minutes. The argument does not classify pure-unit multisets or other wing splits.
