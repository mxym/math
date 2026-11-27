# Proof

## 1. Statement and conventions

Write \(V=\mathbb F_2^n\). The subspace distance is
\[
d(X,Y)=\dim X+\dim Y-2\dim(X\cap Y).
\]
A BEV linear subspace code is a set of subspaces of \(V\) containing \(0\), with an elementary abelian two-group law with zero \(0\) for which \(d\) is translation invariant. Let \(G\) denote this group in additive notation, \(X_g\) the subspace of label \(g\), and \(r(g)=\dim X_g\). Thus
\[
d(X_g,X_h)=r(g+h).                                                     \tag{1}
\]
This does not assume that addition is ordinary subspace sum. An **equality code** has \(|G|=2^n\). Equivalence of the underlying sets means an invertible linear map of \(V\); no group-law enumeration is intended. Hyperplanes always have vector dimension \(n-1\).

For a one-dimensional subspace \(L\le V\), define
\[
\mathcal P_n(L)=\{0\}\ \cup\ \{X:\dim X=2,\ L\subseteq X\}\
                  \cup\ \{Y:\dim Y=n-1,\ L\nsubseteq Y\}.               \tag{2}
\]
For every \(n\ge5\), if an equality code has more than \(2^{n-2}\) hyperplanes, then its underlying set is \(\mathcal P_n(L)\) for a unique \(L\). Conversely (2) is an equality code with \(2^{n-1}\) hyperplanes. The threshold \(2^{n-2}\) is sharp among codes not of form (2). We also give the complete equality-set classification for \(1\le n\le4\).

## 2. The known construction and the sharp lower endpoint

For \(n\ge4\), the nonzero subspaces in the second set of (2) are in bijection with the nonzero points of \(V/L\), so there are \(2^{n-1}-1\). The hyperplanes are kernels of the \(2^{n-1}\) linear functionals that take the value 1 on the nonzero element of \(L\). Two distinct members in either one of these layers have distance 2. A two-space through \(L\) meets a hyperplane avoiding \(L\) in dimension 1, hence has distance \(n-1\) from it. Assign zero and the two-space layer to an index-two subgroup of \(\mathbb F_2^n\) (zero is assigned to zero) and the hyperplanes to the other coset by any bijections. Equation (1) follows, including pairs involving zero. This establishes the linearity exercise in Braun–Etzion–Vardy's Remark 3.

For a direct sum of ambient spaces, take all direct sums of codewords of the factors, and use their product group. Dimensions and intersection dimensions add, so (1) is preserved. The product of \(\mathcal P_{n-1}\) with the two-element coordinate code in a complementary one-space has \(2^n\) words. For \(n\ge5\), its hyperplanes are exactly a hyperplane of \(\mathcal P_{n-1}\) summed with the full coordinate one-space: \(\mathcal P_{n-1}\) has no ambient-full word. The product therefore has \(2^{n-2}\) hyperplanes, and contains a one-space, so it is not of form (2) in dimension \(n\).

## 3. A dense layer of hyperplane labels

Let \(S=\{g:r(g)=n-1\}\) and let \(D=S+S\) (all sums, including zero). For distinct hyperplanes \(X_s,X_t\), their intersection has dimension \(n-2\), hence
\[
D\setminus\{0\}\ \subseteq\ \{g:r(g)=2\}.                              \tag{3}
\]
In particular, for \(n\ge4\), \(S\) is sum-free: \(S\cap D=\varnothing\). For \(t\in D\setminus\{0\}\) and \(s\in S\), use the intersection of a two-space and a hyperplane in (1) to obtain
\[
s+t\in S\quad\Longleftrightarrow\quad X_t\nsubseteq X_s.                \tag{4}
\]
There are only the two possibilities \(\dim(X_t\cap X_s)=1,2\), giving respective distances \(n-1,n-3\). In (4) the exclusion of \(t=0\) is essential.

**Elementary doubling lemma.** Suppose \(A\) is a subset of a finite elementary abelian two-group \(K\), \(|A|>|K|/4\), and \(|A+A|\le |K|/2\). Then \(A+A\) is an index-two subgroup and \(A\) is contained in one of its cosets. To prove this, put \(B=K\setminus(A+A)\). If \(b,c,b+c\in B\), then \(0,b,c,b+c\) are distinct and the four corresponding translates of \(A\) are pairwise disjoint, impossible. Thus \(B\) is sum-free. For any \(b_0\in B\), the sets \(B\) and \(b_0+B\) are disjoint, so \(|B|\le |K|/2\); equality follows from the hypothesis. For every \(b\in B\), \(B+b=K\setminus B\). This complement contains zero and is exactly the set of translations stabilizing \(B\): each \(b+b_0\) stabilizes \(B\), and no translation by an element of \(B\) does. Hence \(K\setminus B\) is the required subgroup. Fixing any \(a_0\in A\) gives \(A\subseteq a_0+(A+A)\).

If \(n\ge6\) and \(|D|>|G|/2\), every label is a sum of two elements of \(D\). By (1) and (3), all the codeword dimensions are at most 4, contrary to \(S\ne\varnothing\) and \(n-1\ge5\). Thus for \(n\ge6\) and \(|S|>2^{n-2}\) the lemma gives an index-two subgroup \(D\), with \(S\) in its nonzero coset. In dimension five we will derive the same conclusion by a separate argument.

## 4. The exceptional five-dimensional step

Here \(G\cong\mathbb F_2^5\), and we assume \(h=|S|\ge9\). Suppose \(S\) is not in a coset of an index-two subgroup. There is then an odd-size subset of \(S\) summing to zero: otherwise the linear rule assigning 1 to each element of \(S\) would be consistent on \(\operatorname{span}S\) and extend to a nonzero functional on \(G\). A shortest odd dependence is a circuit. In fact, any proper nonempty dependent sublist would, if odd, contradict minimality directly, and, if even, leave a shorter odd dependence upon deletion. Because \(S\) is sum-free and omits zero, the circuit has length at least five; because \(G\) has dimension five, its length is at most six. Thus it is a set \(E=\{e_1,\ldots,e_5\}\) of five distinct elements, any four independent, with sum zero. Put \(W=\operatorname{span}E\), of dimension four.

The fifteen nonzero elements of \(W\) are exactly \(E\) and the ten distinct pair sums \(e_i+e_j\). Distinctness, and disjointness from \(E\), follow because no proper nonempty subset of \(E\) sums to zero. Since \(S\) is sum-free, \(S\cap W=E\). Choose any \(a\in S\setminus W\), and write the outside points as \(a+C\), with \(C\subseteq W\) and \(0\in C\). We have \(|C|\ge4\). Every other element of \(C\) is a pair sum, because its difference from 0 cannot be in \(E\) (else two outside points of \(S\) would sum to an element of \(S\)). Moreover the pairs indexing the nonzero elements of \(C\) are pairwise intersecting: two disjoint pairs have sum equal to the fifth element of \(E\), which is forbidden. A pairwise intersecting family of two-element subsets consists of pairs through a common index, or the three edges of a triangle. Indeed, from two different pairs sharing an index, a third avoiding it must join their other indices, and no other edge can meet all three. We get two cases.

**Common index.** Say the common index is \(i_0\). Because \(C\subseteq e_{i_0}+E\), \(S\) occupies the five groups
\(\{e_i,e_i+b\}\) where \(b=a+e_{i_0}\notin W\), with at least four groups full and the rest nonempty. Choose any two full groups \(i,j\). The two distinct nonzero labels \(t=e_i+e_j\) and \(t+b\) lie in \(D\) and label two-spaces. For each \(s\) in the remaining three groups, neither \(s+t\) nor \(s+t+b\) is in \(S\): modulo \(\langle b\rangle\), the five representatives are the images of \(E\), and the only pair with difference \(e_i+e_j\) is \(\{e_i,e_j\}\). Thus by (4) both two-spaces lie in each of at least five hyperplanes, those from the remaining groups.

**Triangle.** Here \(C\) is a two-dimensional subspace (its three nonzero elements are the three pair sums of the triangle). For any \(t=e_i+e_j\notin C\), the only elements \(s\in S\) with \(s+t\in S\) are \(e_i,e_j\). The outside layer \(a+C\) is moved disjointly from itself, and \(t\in W\) does not exchange the two layers. There are seven possible \(t\), all in \(D\setminus\{0\}\). Choose two different ones; at least \(9-4=5\) hyperplanes contain both associated two-spaces by (4).

In either case, distinct two-spaces have distinct three-dimensional annihilators in \(V^*\), whose intersection has dimension at most two and so contains at most three nonzero points. Every binary hyperplane has a unique nonzero normal. Having at least five common hyperplanes contradicts that bound. This excludes the noncoset possibility. Since \(S\) has more than half the size of the coset that contains it, every element of the associated subgroup is a sum of two elements of \(S\); hence \(D\) is again that entire index-two subgroup.

## 5. Recovering the pencil and forcing the full layer

We return to any \(n\ge5\) and \(h>2^{n-2}\). By Sections 3–4, \(D\) is an index-two subgroup and each nonzero label of \(D\) denotes a two-space. For two distinct such labels their distance is also 2, so their two-spaces meet in dimension one. A pairwise intersecting family of two-dimensional subspaces either has a common one-space or lies in a common three-space. For completeness, select distinct members \(A,B\), put \(M=A+B\) and \(L=A\cap B\). Any member \(C\) avoiding \(L\) is spanned by its distinct intersections with \(A,B\) and lies in \(M\). Any member \(Z\) outside \(M\) meeting both \(A,B\) has \(Z\cap M=L\), then cannot meet such a \(C\) nontrivially. This proves the dichotomy. A three-space has only seven two-spaces, but \(|D|-1=2^{n-1}-1>7\). Thus the two-spaces of \(D\) share \(L\), and exhaust the pencil through \(L\) by their number. The common \(L\) is unique.

If \(X_s\) is a hyperplane with \(L\nsubseteq X_s\), it contains none of the pencil. Equation (4) implies \(s+D\subseteq S\), so \(S\) is the whole coset and we obtain (2).

Otherwise every \(X_s\) contains \(L\). Its nonzero normal descends to a functional \(\lambda_s\) on \(V/L\). The nonzero labels \(t\in D\) correspond bijectively to the nonzero quotient vectors \(v_t\) via \(X_t/L=\langle v_t\rangle\). Equation (4) gives the precise translate
\[
S+s=\{0\}\cup\{t\in D\setminus\{0\}:\lambda_s(v_t)=1\}.                \tag{5}
\]
For distinct \(s,s'\in S\), the functionals \(\lambda_s,\lambda_{s'}\) are distinct, hence independent over \(\mathbb F_2\). Formula (5) gives \(|(S+s)\cap(S+s')|=1+2^{n-3}\), odd. But translation by the nonzero \(s+s'\) interchanges \(S+s,S+s'\), and acts without fixed points on their intersection, so its size is even. This contradiction proves the theorem.

## 6. Complete small-dimensional classification

We use Pai–Rajan's Theorem 2 for an equality code containing the full ambient space: such a set necessarily consists of spans of subsets of a fixed basis (the coordinate code). No converse below claims that all group laws are ambient-linearly equivalent.

First we give a projection lemma for a one-dimensional codeword. Suppose \(X_\ell=L\) is in the code. Translation by \(\ell\) pairs each \(X\) avoiding \(L\) with \(X+L\), and each word containing \(L\) with a complementary subspace within it. Indeed for \(Y=X_{g+\ell}\), from (1) we have \(r(g+\ell)=r(g)\pm1\) according as \(X\) avoids or contains \(L\). If \(X\) avoids, \(d(X,Y)=1\) makes \(X\subset Y\), and \(d(L,Y)=r(g)=\dim Y-1\) makes \(L\subset Y\), so \(Y=X+L\). The other direction follows by the involution.

For any two words \(X_g,X_h\) avoiding \(L\), quotienting by \(L\) preserves the distance: it equals the distance between \(X_g+L,X_h+L\), which equals \(d(X_g,X_h)\) by translation invariance. Consequently
\(\dim(\pi X_g\cap\pi X_h)=\dim(X_g\cap X_h)\) for the quotient \(\pi:V\to V/L\). This also gives \(\dim(X_g\cap(X_h+L))=\dim(X_g\cap X_h)\), since \(\pi\) restricted to \(X_g\) is injective. Therefore \(d(X_g,X_h+L)=d(X_g,X_h)+1\). By (1) and the translation pairing, \(X_{g+h}\) avoids \(L\). The labels avoiding \(L\) form an index-two subgroup, and their distinct images yield an equality code in \(V/L\).

If the projected code covers every pair of quotient vectors with at least one word, the original is geometrically a direct product of this projected code with the coordinate code on \(L\). In fact the projection of each pairwise intersection is the intersection of the two projections, by the equality of dimensions. Thus the individual linear lifts \(\pi^{-1}|_{X_g}\) (meaning the inverse of \(\pi|_{X_g}\)) agree on overlaps, giving a section on the entire quotient. Any two vectors are in a common projected word, so the section is additive, hence linear. Its image is a complementary subspace containing all avoiding words; the other half are exactly their sums with \(L\).

- For \(n=1\) there is only the coordinate code. For \(n=2\), if the ambient space is absent the three nonzero codewords are all one-dimensional, and two distinct such words would have distance 2 with no codeword of dimension two. Thus only the coordinate type occurs.
- For \(n=3\), an equality code not containing the full space cannot have a one-dimensional word: quotienting by it gives a two-dimensional equality code containing the full quotient, whose translate by that word then lifts to the full ambient space. It must therefore consist of zero and the seven two-spaces, the known Fano code. Its nonzero words are all mutually at distance two and have dimension two, so any bijection of those words to the nonzero labels of \(\mathbb F_2^3\) gives (1).
- In \(n=4\), if the full space is absent but a one-space occurs, the quotient has dimension three and cannot contain its full space, by the same reasoning. The quotient is Fano, which covers all pairs of quotient vectors, so the projection lemma gives the Fano times coordinate type.
- In \(n=4\) when neither the full space nor a one-space occurs, the only possible positive dimensions are two and three. If all dimensions were even, all fifteen nonzero words would be two-spaces intersecting pairwise in dimension one. The dichotomy of Section 5 allows at most seven in this ambient dimension, impossible. Thus the parity homomorphism \(g\mapsto r(g)\bmod 2\), which follows from (1), is nontrivial. Its odd coset consists of eight hyperplanes, and its even subgroup has seven nonzero two-spaces. They all intersect in dimension one by (1), so they are either an entire pencil or the entire family of two-spaces of a three-space. The latter is impossible: any hyperplane of \(V\) contains one of those two-spaces by the dimension formula, but all distances from the two-space layer to the odd coset must be three. In the pencil case no hyperplane can contain its common \(L\), as it would then contain a member of the pencil. There are exactly eight hyperplanes avoiding \(L\), so the set is \(\mathcal P_4(L)\).

In \(n=4\) the three types have dimension distributions, in increasing dimension, \((1,4,6,4,1)\), \((1,1,7,7,0)\), \((1,0,7,8,0)\), so they are inequivalent. All choices within each type are equivalent under ambient invertible linear maps. The numbers of distinct sets in a fixed ambient space are \(20160/4!=840\) for the coordinate code (the one-spaces determine the unordered basis), \(15\cdot8=120\) for the Fano product (the complement is its unique one-space, and the seven two-spaces determine the Fano three-space), and 15 for the pencil (its two-spaces determine the common \(L\)). In dimensions \(1,2,3\) the corresponding totals are \(1,3,29\). The all-dimensional no-density classification is not asserted.
