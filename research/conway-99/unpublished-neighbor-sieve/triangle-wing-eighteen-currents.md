# Every centered seven-current of an 18-site triangle-wing component is visible

In any hypothetical Conway graph, fix a triangle T with cubic wing graph W and 60 far sites X, as in [triangle-complement.md](triangle-complement.md). If D is a connected component of W of size 18, let K be the centered kernel over F7 of its Laplacian 3I−A_D. For h in K let R(h)_x be the sum of h on the three neighbors of x in D. **The map R:K→F7^60 is injective**, independently of the Seidel rank, the other wing components or any assumed symmetry.

For i≠j in D the number of far vertices meeting both is
 m_ij = 2−[i~j]−|N_D(i)∩N_D(j)|−[i,j in the same wing].
All possible near common neighbors were counted because D is a component. Each far vertex meets exactly three sites in D by component balance; each i in D has ten far neighbors, so sum_j m_ij=20 with m_ii=0. Were R(h)=0, for any fixed i every triple through i would place its two remaining colors b and −h_i−b together. Thus for all sites i the exact integers
 q_i(b) = sum_(j≠i:h_j=b) m_ij
must satisfy q_i(b)=q_i(−h_i−b), and q_i(−h_i/2) must be even. These are tests of a single putative current using only the triangle wing graph, not the unknown triple assignment. Every nonzero projective current fails at least one test in the complete bounded component catalogue below.

## Catalogue and exact replay

Each of the three named wings has six sites in D, by the three cross matchings. Label the six sites of the first, name the second and third by two successive cross matchings, and call the last cross matching the return permutation f on six letters. The internal matchings are fixed-point-free involutions P,Q,R. By coordinated relabeling fix P=(01)(23)(45). For Q,R there are 15 choices each and for f there are 720, hence 162000 initial named parameter triples. Conjugating simultaneously by the 48-element centralizer of P gives 3802 orbits before local tests. The code first normalizes (Q,R) and then f by the stabilizer of that pair, checking that the total orbit mass is 162000. It discards only disconnected charts and those with negative pair quota. Of the 2413 named-wing survivors, 1957 have d=dim K zero, 410 have d=1, 45 have d=2 and 1 has d=3. There are exactly 410+45·8+57=827 projective currents to test. Each fails the anchored color pairing or evenness. The rank-free visibility statement follows.

For optional reporting with three unnamed wings, permute their six orderings, renormalize P and apply the same centralizer convention. Let ε be the quadratic character of the determinant of the nondegenerate part of the centered component Laplacian over F7. It can be found by congruence elimination on the basis e_i−e_17. The numbers of surviving unlabelled types by d, with (positive,negative) signs, are
 d=0: (259,184); d=1: (42,62); d=2: (1,14); d=3: (1,0).
This counts 563 formal local types, not graphs. The [standard-library replay](triangle_wing_eighteen_currents.py) reconstructs every item and checks the stated integer and finite-field arithmetic.

## Rank-36 consequence for a split into two 18-components

Write d,e and ε,η for their two radical dimensions and signs. The near Gram rank is ell=35−d−e. Its nondegenerate determinant sign is εη since its global constant direction has square norm 144. Let s denote the dimension of the sum of the two current images on X, a subspace over F7. By visibility, s≥max(d,e); by the hyperbolic-block argument in [triangle-wing-twelve-currents.md](triangle-wing-twelve-currents.md), full rank is at least ell+2s. Rank 36 consequently requires |d−e|≤1 and that the smaller of the two images lie inside the larger (equality if the dimensions coincide): any extra dimension beyond max(d,e) costs two in full rank. Furthermore if |d−e|=1 the entire complement is accounted for by hyperbolic blocks, so εη(−1)^max(d,e) must be negative, the ambient rank-36 determinant character. No sign condition is asserted when the rank inequality is strict.

Among the 158766 unordered pairs with repetition of the 563 formal types, this rules out 31902. By unordered radical dimensions the exclusion counts are (0,1):23786; (0,2):6645; (0,3):443; (1,2):910; (1,3):104; (2,3):14. Each rejection is independent of the relative naming of the common triangle wings. Remaining pairs are not claimed to admit a consistent far array. Nor is an 18+18 split known to occur in every graph.
