# The eleven-triangle extreme of an actual 33-set

Suppose that T in an SRG(99,14,1,2) is a union of eleven pairwise anticomplete graph triangles. The ratio-bound equality (or the real spectral projector) gives A1_T=6−4·1_T: its 33-site degree is 2, and since 33 saturates the negative-eigenvalue bound each outside vertex sees six in T. Alternatively assume T is an actual G(3,33) as in the two-type face. The results in the first paragraph do not need that face or a Hoffman coclique.

The six T neighbors of any exterior vertex v are on six different T-triangles (otherwise v gives a second cap to a triangle edge). Thus they are pairwise nonadjacent. The graph on N(v) consists of seven disjoint edges: each of those six neighbors uses a different exterior neighbor as its mate, leaving two exterior neighbors paired with each other. In particular each v lies in exactly one triangle wholly outside T. The 66 exterior vertices themselves partition into **22 vertex-disjoint triangles**, giving an actual 33-triangle spanning partition.

On the rank-42 two-type face let C be the unique Hoffman coclique. Its overlap with T must be 5 (the other option 12 exceeds the one-per-triangle cap). Let L=A_T and H=3I−L. Over each triangle of T, H is 4I−J_3 and H^{-1}=(I+J_3)/4. Using the [actual 33-site Gram](all-cycles-hit.md), the T-site Gram of u_i is H+J/9 and its inverse H^{-1}−J/42. For a true oriented neutral norm18 field t, x=t/√7, η=t·(−1_T), put g=#T-triangles meeting supp(t), and r=pr_(span of the 33 T-site marks)^⊥(x). Each triangle has zero, one, or two supported sites (the last case must consist of opposite signs). The squared T-site evaluations plus squared triangle total sum to precisely 2 per touched triangle. Since the evaluations are the literal entries of t, this gives

    ||r||² = 18/7−g/2+η²/42.

For exterior v, write Y_v=N(v)∩T, and σ_i=sum of t on triangle i. The real projection coefficients of u_v onto the T-site basis equal 1/6−H^{-1}1_(Y_v), because |Y_v|=6. Thus

    4(r,u_v)=4t_v+sum_(i∈Y_v)(t_i+σ_(triangle of i))+(2/3)η.

All evaluations at T vanish. For η=0 the displayed evaluations of 4r are integral, and r lies in the neutral graph -4 eigenspace. If g=5, then ||r||²=1/14, so its scaled evaluation field has squared integer norm 16·7/14=8, contrary to the universal minimum 14 of a nonzero integer neutral field. Larger g violates positivity. Consequently every one of the 2n true N18 fields perpendicular to [T] (η=0) touches **at most four** T-triangles. They are balanced inside each touched triangle: flipping any triangle component gives a true 33-set with opposite residue, so t is perpendicular to this flip as well, and their two evaluations force σ_i=0. Here n=50,51,52,53 in the four live tuples.

In the opposite extremal angular situation, η=9, all nine negative sites of t lie in T, one in each of nine different triangles; all its positive sites are outside. Hence g=9 and r=0. In particular t is uniquely determined by these nine chosen sites N. Let E consist of the two omitted triangle groups. For each exterior v define k_v=|Y_v∩N| and let e_v be the number of omitted groups touched by Y_v. The same evaluation equation gives

    t_v=(k_v−e_v)/4.

Therefore k_v−e_v is either zero or four, with exactly nine occurrences of four. The condition is also sufficient for this choice of N: take the vector x in the span of the T sites whose T evaluations equal −1_N. It is unique by invertibility. The formula above with r=0 determines all its exterior evaluations. Their sum is nine because sum_v(k_v−e_v)=9·12−2·36=36. Thus if all k_v−e_v are 0 or4, the full evaluation field is an integral neutral norm18 field with η=9 and its switch T' is a true 33-set. No search for arbitrary external signs is needed.

For the fixed C at overlap5 the projection of y_C=(-1_C)°/√7 on the T-site span has coefficients 1/6−f_i, where f=H^{-1}1_(C∩T); f equals 1/2 at each marked C site, 1/4 at its two triangle mates, and zero on the six untouched groups. Since x for a switch is wholly in that span, (x,y_C)=0 forces sum_(i∈N) f_i=9/6. If j of the five C-marked triangle groups are used by N and κ of the selected sites actually lie in C, then (j+κ)/4=9/6. Equivalently κ=1+#C-marked groups omitted.

Finally the residual site marks r_v=pr_(T-sites)^⊥u_v have squared norm 7/6; for distinct exterior v,w their ordinary dot is 7/6−A_vw−(h+k)/4, where h counts the T triangle groups touched by both and k counts their common actual T neighbors. This follows by the same inverse Gram and |Y_v|=|Y_w|=6. It is not a classification or an exclusion of this eleven-triangle case.
