# Line partition and projective additive code

## 1. Coordinates and certificate

Identify \(\mathbb F_2^{10}\) with the 10-bit nonnegative integers, least significant bit first. Addition is bitwise XOR. Over \(\mathbb F_2\) each nonzero vector represents a unique projective point of \(\operatorname{PG}(9,2)\). A line is the three-point set \(\{a,b,a+b\}\) for distinct nonzero \(a,b\).

The file **partition.tsv** lists 66 triples \((a_i,b_i,c_i)\). In every row \(c_i=a_i+b_i\), and all 198 entries are distinct, nonzero and less than 1024. Thus the lines are pairwise disjoint. Let \(P\) be the union of their points.

The set \(P\) is exactly the column set of the binary \([198,10,\{96,112\}]_2\) generator in SageMath 10.8's Eric Chen database entry: take row 1 as bit 0 through row 10 as bit 9. The optional provenance check in `verify_independent.py` extracts the known source record by its parameters, without executing that source, and checks equality of the sets. For this comparison the row bytes and sorted point lists have separately pinned hashes. The theorem itself uses only the listed triples.

One way to find the certificate is to enumerate all unordered triples of distinct points of \(P\) whose XOR is zero, giving 726 lines (11 incident with each point). The partition is an exact cover of these points. A minimum-choice exact-cover search finds the listed witness; the argument does not use any assertion about the search's completeness or performance.

## 2. Binary hyperplanes and quaternary weights

For any \(x\in\mathbb F_2^{10}\), write \(x\cdot a\) for the binary inner product and set
\[
     C(x)=\bigl((x\cdot a_i)+(x\cdot b_i)\omega\bigr)_{i=1}^{66}
       \in\mathbb F_4^{66},\qquad \omega^2+\omega+1=0.
\]
This is a linear map of binary vector spaces. Each coordinate is nonzero precisely when the associated line is not contained in the hyperplane \(H_x=\{v:x\cdot v=0\}\). Such a line has exactly two points off \(H_x\), since a nonzero functional on its 2-dimensional space has two nonzero evaluations. The whole line is inside \(H_x\) when both binary coordinate evaluations vanish. Consequently
\[
 \operatorname{wt}_2((x\cdot v)_{v\in P})
    = 2\operatorname{wt}_4(C(x)),\qquad
 |H_x\cap P|=66+2\,\#\{i:L_i\subseteq H_x\}.
\]
The first equality is also the standard inner binary simplex expansion, applied coordinate by coordinate.

The exact verification ranges over all 1024 values of \(x\). The binary weight counts are 1 at weight 0, 825 at 96, and 198 at 112. Independently the quaternary weight counts are 1 at 0, 825 at 48, and 198 at 56. Hence \(x\mapsto C(x)\) is injective, the binary dimension is 10 (quaternary dimension parameter 5), and the codelines are projective: each block has binary rank 2, and any pair of blocks occupies disjoint projective point sets. This also proves that the nonzero \(x\) run over precisely all 1023 hyperplanes, whose contained-line counts are 825 occurrences of 18 and 198 of 10. This verifies the published point-set partition question and the two-weight existence question.

The answer concerns the referenced point-set representative from the public generator database, not a classification of all binary \([198,10,\{96,112\}]_2\) codes or all their partitions. It does not assert a Griesmer minimum at these parameters.

## 3. Strict additivity certificate

Let \(L_i=\operatorname{span}_{\mathbb F_2}\{a_i,b_i\}\) now denote the binary 2-dimensional vector space, and consider its simultaneous stabilizing algebra
\[
 \mathcal R=\{J\in M_{10}(\mathbb F_2):J L_i\subseteq L_i
                 \text{ for every }i\}.
\]
This is the usual necessary-condition test for linearizability via a quadratic field action (Abdukhalikov–Ho, Theorems 3.2–3.4). For this certificate the dimension of \(\mathcal R\) is exactly 1. Here are two different ways of computing it, both in the replays:

1. The 100 binary entries of \(J\) are unknowns. For \(p=a_i,b_i\) and each nonzero \(h\in L_i^\perp\), the homogeneous equation \(h\cdot Jp=0\) requires \(Jp\in L_i\). The 33,660 rows so obtained have rank 99. In this representation the row on \(J\)'s column \(j\) is \(p_jh\).
2. Add separate four binary unknowns for the \(2\times2\) matrix \(T_i\) on each line and impose \(J\,(a_i\ b_i)=(a_i\ b_i) T_i\). All \(T_i\) are uniquely determined by \(J\) if consistent, since \(a_i,b_i\) are independent. The expanded \(1320\times364\) binary system has rank 363, again giving a one-dimensional algebra.

The identity always belongs to this algebra, so \(\mathcal R=\{0,I\}\). If a coordinate permutation and invertible binary relabelings within the coordinate pairs made \(C\) \(\mathbb F_4\)-linear, multiplication by \(\omega\) would induce a binary linear action on its 10-dimensional message space with minimal polynomial \(X^2+X+1\). Pulled back to \(C\), it preserves the kernel of each coordinate map, and its dual action therefore preserves that coordinate's 2-dimensional codeline. This gives a \(J\in\mathcal R\) with \(J^2+J+I=0\), impossible for \(0\) or \(I\). Even if all symbol permutations are allowed, an equivalence can be translated by the image of the zero codeword in the proposed linear code, to fix zero in each coordinate. Every permutation of the three nonzero binary 2-vectors is linear (the group \(\mathrm{GL}(2,2)\) acts as their full symmetric group). Thus there is no hidden linear equivalence in the larger Hamming-isometry convention either.

Kurz's separate Proposition 1 excluding the corresponding projective \(\mathbb F_4\)-linear parameters is a prior result; the calculation here certifies strict additivity of this particular constructed code independently of that nonexistence classification.
