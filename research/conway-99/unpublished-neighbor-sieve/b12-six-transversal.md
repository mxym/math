# The 24-site companion of B12 has at most five transversal triangles at rank 36

Under the hypotheses of the [flat 24-site exclusion](b12-flat24-zero-words.md) (rank 36, one B12 wing component of tree number 7140, one connected seven-unit 24-component), the cross-return permutation in the large component has at most **five** fixed points. The flat / eight-fixed-point case was excluded there, exactly seven is impossible for a permutation, and here we exclude six. These fixed points are exactly the transversal triangles of the 24-component.

Number eight sites in each wing so two consecutive interwing perfect matchings are the identity. The remaining one is the cross-return \(\pi\in S_8\). Exactly six fixed points means \(\pi\) is a transposition. By simultaneous index relabeling, normalize the internal mate matching in the first wing to \(01,23,45,67\). Relative to this matching the transposition exchanges either two partners, or two points from different pairs. Name it \((01)\) or \((02)\), respectively. Keep all three wing roles distinguished relative to B12. The subgroup preserving the normalized data has size 96 or 16 respectively. Enumerate the \(105^2\) ordered choices of the remaining two perfect matchings modulo this subgroup. The resulting inventory is:

| exchanged sites | ordered matching representatives | cases at tree residues \(0,1,2,3,4,5,6\pmod7\) | nonsquare unit tests |
|---|---:|---|---:|
| partners | 191 | 88,18,19,12,16,20,18 | 50 |
| nonpartners | 863 | 262,105,81,95,71,123,126 | 344 |

For each nonsquare-unit type, regenerate its literal cubic adjacency and apply exactly the previous ten-part compatibility proof. The tests on the B12 pairs, six-contact words, zero-current projected Gram, site-pair capacities and mandatory transversal clique are unchanged. In the two rows the numbers of search nodes are respectively 5956 and 36794, with a maximum in any one chart of 334 or 324; none contains a ten-colour clique. Multiple disconnected templates in the raw inventory cause no issue because disconnected graphs have zero tree cofactor. This finite calculation does not classify the cases with up to five fixed points, and does not assume a graph automorphism. [Standalone Python/NumPy source](b12_six_transversal.py), exact integers, no solver.
