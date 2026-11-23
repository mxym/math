# Six-cycles in the 33-set switch graph

On the rank-42 norm-18/norm-24 two-type face, use the [actual switch graph](marked-cycle-switch.md): vertices are actual 33-sets, and edges have overlap 24. The graph is bipartite and has no four-cycle. This note classifies a six-cycle **if one occurs**; it does not assert a positive lower bound on switch degrees.

Let the shores of a six-cycle be \(X_1,X_2,X_3\) and \(Y_1,Y_2,Y_3\), with edges \(X_iY_j\) for \(i\ne j\). Write \(x_i=1_{X_i}-1/3,\ y_i=1_{Y_i}-1/3\) coordinatewise, and \(t_{ij}=1_{X_i}-1_{Y_j}\). The six oriented edge fields lie in the same signed \(N_{18}\) residue. Distinct fields in this residue have dot \(-3\) or \(4\).

An overlap along a two-edge path is at least 15, so the [overlap and residue restrictions](33set-rank11-and-switches.md) give same-shore overlap 19. In particular the centered same-shore dots are 8. On edges the centered dot is 13. Between \(X_i,Y_i\) the overlap is at least 6 along a three-edge path, is congruent to 3 modulo 7, and is not 24 (which would give a four-cycle). Put \(d_i=x_i\cdot y_i\in\{-1,6\}\). For \(i\ne j\) one has
\[
t_{ij}\cdot t_{ji}=16-d_i-d_j.
\]
If \(d_i,d_j\) differ, this dot is 11, neither a distinct-field angle nor the squared norm 18. Hence the opposite overlaps are either all 10 or all 17.

## Opposite overlap 17

The two cyclic triples \((t_{12},t_{23},t_{31})\) and \((t_{21},t_{32},t_{13})\) have all within-triple dots \(-3\) and all between-triple dots \(4\). Indeed a within-triple pair has dot \(16-13-6=-3\); a between-triple pair either has transposed indices or shares a shore vertex. In the latter case its dot is \(22+8-26=4\), and the transposed formula gives 4 as well. All six fields are distinct and the triple sums coincide by the definitions.

## Opposite overlap 10

The transposed dot is 18, so \(t_{ij}=t_{ji}\) and \(1_{X_i}+1_{Y_i}\) is the same literal sum for all \(i\). Its double sites form a 10-set \(I\); its single sites form a 46-set \(W\). Label each site of \(W\) by its membership word in the three \(X_i\). If the size of class \(111\) is \(r\), then \(000\) has size \(4-r\), each weight-two class has size \(9-r\), and each weight-one class has size \(5+r\), by the fixed set sizes and same-shore overlaps.

For a site \(v\) of type \(111\), the negative part of \(t_{ij}\) consists of the \(000\) sites and the weight-one class at the remaining coordinate \(k\). Each signed \(N_{18}\) support vertex has four neighbors of the opposite sign. The weight-one class at \(k\) lies in \(X_k\) with \(v\), so at most two of these neighbors can lie in that class (the induced graph on \(X_k\) has degree two). Thus \(r\le2\) whenever \(111\) is nonempty. Interchanging shores gives \(r\ge2\) whenever \(000\) is nonempty. The endpoint values \(0,4\) also violate one of these implications. Therefore \(r=2\): there are two sites of each of types \(111,000\), and seven in each of the six other classes.

The four common support sites form an induced square: every \(111\) meets both \(000\), and sites of the same sign are independent in a signed \(N_{18}\) support. Each \(111\) has exactly two neighbors in each weight-one class, with disjoint choices for the two \(111\) sites since their two common neighbors are already the \(000\) sites. The symmetric statement applies to \(000\) and the weight-two classes. Each such pair uses up the induced degree in the relevant \(X_k\) or \(Y_k\). This also forbids neighbors in \(I\) or in any of the other \(W\) classes not already accounted for. Thus each square vertex has precisely six neighbors off \(I\cup W\). Every square edge has its unique common neighbor there: none of the other square sites is a common neighbor and their possible neighbors off the square but in \(I\cup W\) have disjoint sign-weight types. These four common neighbors are distinct, since otherwise some outside vertex would touch both opposite vertices whose two-common-neighbor quota is already used in the square.

## Two switches from the same set

Orient two distinct switches out of \(X\) as \(1_P-1_N\) and \(1_Q-1_M\), with \(P,Q\subset X\) and \(N,M\) outside it. They have no sign conflicts, so their dot is 4 and \(|P\cap Q|+|N\cap M|=4\). At a site shared by \(N,M\), the four neighbors from each of \(P,Q\) must fit among the six neighbors the site has in \(X\), giving \(|P\cap Q|\ge2\). If \(N,M\) do not meet, the positive overlap is 4. If both overlaps are 2, each shared negative vertex then touches both shared positive vertices and the intersection is an induced square. A fixed such square is supported by at most two switches out of \(X\): at either negative corner, each switch chooses two additional neighbors from the other four \(X\)-neighbors, and these two-subsets must be pairwise disjoint because the square already uses the entire allowed overlap.
