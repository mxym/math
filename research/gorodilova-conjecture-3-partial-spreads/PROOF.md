# Counterexamples and exact five-dimensional classification

Let \(V=\mathbb F_2^n\), let \(\mathcal R\) be a set of \(k=(2^{n-1}-1)/3\) binary 2-dimensional **linear** subspaces with pairwise intersection \(\{0\}\), and set \(M=\bigcup_{R\in\mathcal R}R\). Thus \(0\in M\), \(M\setminus\{0\}\) is a disjoint union of the three-point sets \(R\setminus\{0\}\), and \(|M|=2^{n-1}\). For two distinct coordinates \(i,j\), denote by \(N_0^{ij}\) the number of planes with **no nonzero** point whose \(i,j\) coordinates are both zero. This is the convention of the three-nonzero-point table in Step 2 of the source. Fixing these assumptions, Conjecture 3 asserts that having all \(N_0^{ij}\) even characterizes being a coordinate hyperplane. We give counterexamples even to the weaker conclusion of being any hyperplane.

## 1. The parity condition

For any independent linear forms \(u,v\) on \(V\), let \(K=\ker u\cap\ker v\). A plane contributes 3, 1 or 0 nonzero points to \(M\cap K\), according to \(\dim(R\cap K)\). Since \(k\) is odd,
\[
 |M\cap K|\equiv 1+(k-\#\{R:R\cap K=\{0\}\})
 \equiv \#\{R:R\cap K=\{0\}\}\pmod2.
\]
This gives the source's parity test for \(u=x_i,v=x_j\).

The sum of the three nonzero points of each plane is zero, so \(\sum_{x\in M}x=0\). Also \(|M|=2^{n-1}\) is even. Taking all sums from now on in \(\mathbb F_2\), we therefore have
\[
 N_0^{ij}\equiv \sum_{x\in M}(1+x_i)(1+x_j)=\sum_{x\in M}x_i x_j.
\]
Consequently all the coordinate counts are even if and only if \(1_M\) is orthogonal under the truth-table dot product to every polynomial of degree at most two. This implies the same parity for *all* codimension-two linear subspaces since their indicators have degree two. The reverse implication includes all the coordinate pairs.

Equivalently, in the usual binary Reed–Muller notation, \(\deg 1_M\le n-3\). For completeness, any product of polynomials of degrees at most two and at most \(n-3\) has degree at most \(n-1\); its sum over \(V\) is zero, since the sum of a multilinear monomial with support size \(d<n\) is \(2^{n-d}\equiv0\). The two subspaces have dimensions \(\sum_{r=0}^2\binom nr\) and \(\sum_{r=0}^{n-3}\binom nr\), whose sum is \(2^n\), so the resulting containment of orthogonal subspaces is equality. In particular every (not necessarily coordinate) linear hyperplane in \(n\ge5\), equipped with any 2-plane partition as above, satisfies the parity condition.

## 2. A counterexample in every odd dimension at least five

Let \(n=2m+1\ge5\). Identify \(V=H\oplus\mathbb F_2\) with \(H=\mathbb F_4^m\), and write
\[
 q(x)=\operatorname{Tr}_{\mathbb F_4/\mathbb F_2}(x_1 x_2),\qquad
 M=\{(x,q(x)):x\in H\}.
\]
The finite field trace is \(z\mapsto z+z^2\). For a nonzero \(a\in H\), lift the field line \(\mathbb F_4 a\) to
\[
 R_a=\{(\lambda a,\operatorname{Tr}_{4/2}(\lambda^2 a_1a_2)):
                 \lambda\in\mathbb F_4\}.
\]
This map from \(\mathbb F_4\) is \(\mathbb F_2\)-linear, as squaring is additive in characteristic two and the trace is linear, and it is injective by its first coordinate. Its image is a binary linear 2-space. Choosing exactly one representative per field line gives \((4^m-1)/3\) distinct spaces. Their nonzero projections lie in disjoint field lines, so they intersect only at 0 and their union is the entire graph.

The polynomial \(q\) has binary degree at most two, because field multiplication is binary bilinear and the trace is linear. In the ambient binary coordinates \((x,z)\),
\[
 1_M(x,z)=1+z+q(x)
\]
has degree at most two. For any two independent linear forms \(u,v\) on \(V\), the intersection size of \(M\) with \(\ker u\cap\ker v\) is the sum of the polynomial \(1_M(1+u)(1+v)\). Its degree is at most \(4<n\), so that size is even by the monomial calculation in Section 1. This proves the required parity in every basis.

Finally choose \(\omega\in\mathbb F_4\) with \(\omega^2+\omega+1=0\). The two graph points with \(x=e_1\) and \(x=\omega e_2\) have last coordinate zero, but \(q(e_1+\omega e_2)=\operatorname{Tr}_{4/2}(\omega)=1\). Their sum is not in \(M\). Thus \(M\) is not a linear subspace; since it contains 0 it is not an affine hyperplane either. This refutes Conjecture 3 in its intended dimension range, \(n\) odd and \(n\ge5\).

In dimension five, encode \((x_1,x_2,z)\) in binary with \((1,\omega)\) in the first two and next two bits, and \(z\) in the most significant bit. The five nonzero triples are
\[
 (1,2,3),\ (4,8,12),\ (5,26,31),\ (11,22,29),\ (14,23,25).
\]
For the ten coordinate pairs in lexicographic order on the least to most significant bit, \(N_0^{ij}\) is \((4,2,2,2,2,2,2,4,2,2)\). The points 1 and 8 are in the union but \(1+8=9\) (binary addition) is not.

## 3. Scope of the refutation in relation to APN functions

The paragraph preceding Conjecture 3 obtains one kind of \(M\) from a quadratic APN map \(F:V\to V\), but the conjecture then quantifies over an arbitrary family of planes satisfying its size and disjointness hypotheses. Our examples obey those hypotheses. They are not asserted to come from \(F\).

Indeed, for a quadratic APN \(F\), its alternating polar form is \(B(a,b)=F(a+b)+F(a)+F(b)+F(0)\). For \(a\ne0\), \(B(a,\cdot)\) has kernel \(\langle a\rangle\) because its translate is the corresponding derivative and APN gives fibers of size at most two. Thus it has a unique nonzero normal \(\Phi_F(a)\) in the dual. The normal is zero by convention at \(a=0\). Given \(v\ne0\), a nonzero \(a\) with \(v\cdot\Phi_F(a)=0\) is on exactly one plane \(R=\langle a,b\rangle\) with \(B(a,b)=v\): the two possible \(b\)'s are \(b,b+a\), and neither belongs to \(\langle a\rangle\). The other two nonzero points of \(R\) have the same property, so these planes partition the nonzero part of the zero set. For odd \(n\), \(\Phi_F\) is a bijection: each nonzero output functional \(\lambda\) has an odd-dimensional alternating form \(\lambda\cdot B\) with nonzero radical, and each nonzero vector in that radical has normal \(\lambda\); surjectivity then implies bijectivity on the \(2^n-1\) nonzero vectors. Hence the APN zero set has exactly \(k\) planes as above.

Write \(p_R=a\wedge b\in\Lambda^2 V\) for any basis of \(R\). This is independent of the basis since every invertible \(2\)-by-\(2\) matrix over \(\mathbb F_2\) has determinant one. Its \((i,j)\) coefficient is \(a_i b_j+a_j b_i=\sum_{x\in R}x_i x_j\). Hence our parity condition is \(\sum_{R\in\mathcal R}p_R=0\). In the APN situation, the linear map \(\Lambda^2 V\to V\) induced by \(B\) sends each \(p_R\) to \(v\), so it sends the sum to \(kv=v\ne0\). Thus those APN zero sets cannot satisfy the all-even condition. This is compatible with the later proof of the original paper's main Conjecture 2, and is not a counterexample to Conjecture 2 or 4.

## Appendix. Exact five-dimensional classification of the all-even supports

Set \(n=5\). By Section 1, an all-even \(M\) has a quadratic-or-affine indicator \(1_M=1+q\), where \(q(0)=0\). The size condition says that \(q\) is balanced. Let \(A\) be its alternating polar bilinear form and \(R=\operatorname{rad} A\). One has
\[
 \left(\sum_{x\in V}(-1)^{q(x)}\right)^2
     =\sum_{t\in V}(-1)^{q(t)}\sum_{x\in V}(-1)^{A(t,x)}
     = 2^5 \sum_{t\in R}(-1)^{q(t)}.
\]
Since \(q|_R\) is linear, balance is equivalent to that restriction being nonzero. Choose \(e\in R\) with \(q(e)=1\) and any complement \(H\) to \(\langle e\rangle\). Then \(q(h+te)=q(h)+t\) and \(M\) is a graph over \(H\); the rank of \(A|_H\) is the rank of \(A\). Each 2-plane of \(M\) projects injectively to \(H\), and their five projected 2-planes partition \(H\setminus\{0\}\). On each projected plane \(q\) must be linear, so all five are isotropic for \(A|_H\).

* **Rank zero.** \(q\) is nonzero linear, so \(M\) is a linear hyperplane. Every hyperplane admits the field-line partition of a binary 4-space identified with \(\mathbb F_4^2\).
* **Rank two.** The radical of \(A|_H\) has dimension two, with only three nonzero vectors. At most three of the five projected planes can meet it nontrivially. Any plane disjoint from it maps isomorphically onto the two-dimensional nondegenerate quotient and therefore is not isotropic. This rules out rank two.
* **Rank four.** There is only one nondegenerate alternating form on a binary 4-space up to linear change of coordinates: choose a nonzero \(a\), choose \(b\) paired to it with value 1, and choose such a pair again in their nondegenerate orthogonal complement. The form of \(\operatorname{Tr}_{4/2}(x_1x_2)\) has rank four by nondegeneracy of the field trace pairing. Hence a linear bijection of \(H\) identifies the polar of \(q|_H\) with that form; the resulting quadratics differ by a linear form \(\ell\), removable by the linear shear \((h,z)\mapsto(h,z+\ell(h))\). Therefore all such supports are linearly equivalent to the explicit five-dimensional graph and do admit a partition.

The rank of the polar of the indicator is a linear invariant, so precisely two equivalence classes occur. There are 31 linear hyperplanes. For rank four there are 31 possible one-dimensional radicals and 28 nondegenerate alternating forms on each four-dimensional quotient. The latter count is \(20160/720\): there are \(15\cdot14\cdot12\cdot8\) ordered bases and \(15\cdot8\cdot3\cdot2\) ordered symplectic bases for a fixed alternating form. For each lifted form there are \(2^5\) quadratics \(q\) with \(q(0)=0\), differing by linear functionals. Exactly 16 take the value 1 on its nonzero radical vector, equivalently are balanced. This counts \(31\cdot28\cdot16=13{,}888\) distinct rank-four supports, for \(13{,}919\) total coordinate-labelled supports. The count is of point sets, not of choices of a partition.
