# Binary kernel words of weight nine

Let \(E\) be the support of a weight-nine word in either binary adjacency eigencode of a hypothetical Conway graph. The image code has even weight because every column of \(A\) has even sum. Thus the word is in the kernel, and every vertex has an even number \(d(x)\) of contacts with \(E\).

Exactly two structural alternatives are necessary:
1. \(E\) is a 2-factor on nine sites, with cycle deck \(9,6+3,5+4,\) or \(3+3+3\).
2. \(E\) consists of a five-cycle \(C\) and four isolated sites \(I\). There is one outside vertex \(y\) with four contacts, all in \(I\).

Neither alternative is asserted to be realizable. Unlike the [ternary code arguments](shared-norm-18/ternary-adjacency-code.md), this is a binary adjacency statement.

## Pair counts and layers

Subtract half the outgoing edge count from the pair-common-neighbor identity used for [binary octads](binary-octad-zero-layer.md). This gives
\[
\sum_{x\in E}\binom{d(x)}2+
\sum_{x\notin E}\left(\binom{d(x)}2-d(x)/2\right)=9 .
\]
All summands are nonnegative. A degree six on either side exceeds this budget. A degree four inside spends six, allowing at most three other vertices of positive inside degree; it cannot have its required four inside neighbors. If \(s\) sites inside have degree two and \(t\) sites outside have degree four, then \(s+4t=9\). The case \(s=1\) is impossible for a simple induced 2-factor. This proves the two shapes.

Set \(w=A1_E/2\). The full graph identity gives \(Aw=6\,1_E-w+9\mathbf1\).
* In the 2-factor case there are 54 outside sites \(U\) of degree two and 36 outside sites \(Z\) of degree zero. The equitable quotient on \(E,U,Z\) has rows \((2,12,0),(2,6,6),(0,9,5)\). Conversely an induced 2-regular nine-set with at most two outside contacts per outside site must be a binary kernel support: its 108 outgoing contacts and its 54 remaining pair witnesses force exactly 54 double contacts and no singleton contacts.
* In the five-cycle case \(w=1\) on the cycle and on the double-contact sites, \(w=2\) at \(y\), and zero elsewhere. The required neighbor sum at each isolate is 15, which forces adjacency to \(y\), while \(y\) has just four contacts into \(E\). There are six double-contact sites touching two isolates, 40 mixed labels, and ten touching two cycle sites: use the pair quotas, subtracting \(y\) at isolate pairs and the internal cycle witnesses at distance two. The neighborhood matching at \(y\) pairs its four isolates with four distinct mixed labels. A label touching two isolates cannot meet \(y\), since then an edge to \(y\) would have two triangle caps. Every mixed label touching \(y\) mates its one isolate there. The equation at \(y\) gives seven double-contact neighbors and three zero neighbors, so the remaining three double-contact neighbors have two cycle contacts. For a double-contact site \(u\), put \(\gamma=|N(u)\cap C|\), \(\eta=[u\sim y]\). Its degrees into the double and zero layers are \(8-\gamma-2\eta\) and \(4+\gamma+\eta\), respectively. Among the 33 zero sites, the three adjacent to \(y\) have induced degree six; the others have five.

## Mod-seven restriction and triangle interfaces

In the 2-factor case the marking Gram on \(E\) is \(3I-A_E+J/9\), with constant eigenvalue two. For \(3I-A_{C_\ell}\) the cycle determinants at \(\ell=3,4,5,6,9\) are \(16,45,121,320,5776\), all units modulo seven. Replacing the constant eigenvalue one by two therefore gives a nonsingular nine-site marking. Pairings from \(E\) to \(Z\) are all \(1/9\), so the Schur complement on \(Z\) is \(3I-A_Z+J/18\). It vanishes on constants since \(A_Z\) is 5-regular. On the 35-dimensional centered space it equals \(3I-A_Z\) and has rank at most \(r-9\), where \(r\) is the full mod-seven Seidel rank. Thus the nullity of \(3I-A_Z\) modulo seven is at least \(44-r\); here the constant eigenvector is not in that kernel.

If one component is a triangle \(T\), the other six support sites lie outside its closed wing. Their six words partition the 36 sites of the wing: every wing site has one contact in \(T\) and therefore exactly one among those six sites. Within each physical wing they give a perfect matching of nonmate pairs. In the \(3+3+3\) case let \(U_{ij}\) be the sites contacting triangles \(i\) and \(j\). Each class has size 18 by the cross-pair quota. A site in \(U_{ij}\) has six two-contact neighbors, and its two-walk count into the missing triangle \(k\) is six. Those six neighbors must all lie in \(U_{ik}\cup U_{jk}\), so \(U_{ij}\) is independent. The two-walk count into either incident triangle is five, with two already from its single contact inside that triangle. It therefore has three neighbors in each of the other two classes. Each zero site similarly has three neighbors in each class, by solving the three equations that give six two-walks into each of the triangles. This specifies the three 18-site independent classes and their interface with the 36-site 5-regular layer, not a completion of the graph.
