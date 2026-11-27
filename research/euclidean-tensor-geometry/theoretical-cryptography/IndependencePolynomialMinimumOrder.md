# Minimum order of a graph with a non-unimodal independence polynomial

**Theorem.** The smallest order of a finite simple graph whose independence polynomial is not unimodal is **15**. The minimum is also 15 when the graph is required to be connected.

Write \(f_k(H)\) for the number of \(k\)-cliques, not necessarily maximal, of a simple graph \(H\), with \(f_0(H)=1\). Complementation turns \(f_k(H)\) into the number of independent \(k\)-subsets of \(G=\overline H\). Unimodality here is weak on both sides of the mode: it fails exactly when a strict step down is followed later by a strict step up. In particular, flat bottoms count as failures. The question here is minimum order over all graphs, not the already treated forest-unimodality question.

## 1. A connected witness on 15 vertices

Take \(H\) to be \(K_6\) with one edge deleted, together with nine isolated vertices. If \(k\ge2\), the clique count is
\[
f_k=\binom 6k-\binom 4{k-2};
\]
the second term removes the subsets containing both ends of the deleted edge. Thus \(f=(1,15,14,16,9,2)\) up to the last nonzero coefficient, with \(15>14<16\). Its complement \(G\) is connected since each of those nine isolated vertices becomes universal.

For the lower bound it suffices to take \(n=14\). If a smaller graph \(H\) had a nonunimodal clique-count sequence, adding isolated vertices would increase \(f_1\) and preserve every other count. The original down step (which cannot be \(f_0\) to \(f_1\) in a nonempty graph) and the later up step would both survive. The empty graph has sequence \((1)\). Likewise if \(r=\omega(H)\le2\) and \(H\) is nonempty then \(1\le f_1\) and there are at most two positive ranks above rank zero, so no failure is possible.

## 2. The integer bounds

Fix \(n,r\) and \(m=f_2(H)\). Let \(K\) be a clique of size \(r\), \(U=V(H)\setminus K\), and \(q=n-r\). For \(u\in U\) let \(d_u=|N(u)\cap K|\), so \(0\le d_u\le r-1\). If \(D\) is the sorted multiset of the \(q\) values and \(e\) the number of edges in \(H[U]\), then
\[
m=\binom r2+\sum_{d\in D}d+e.
\]

**Upper bound.** For each \(k\ge1\), the [Frankl–Füredi–Kalai bounds in Frohmader's paper](https://pi.math.cornell.edu/~froh/flagcomp.pdf) (Theorem 3.7, Definition 3.8, and Lemma 4.1) apply to the clique counts of \(H\) with \(r=\omega(H)\). This does not assume \(H\) is \(r\)-colorable. To evaluate the bound on \(f_{k+1}\) from \(f_k=a\), label the vertices \(0,1,\ldots\), color by residue modulo \(r\), and list admissible \(k\)-sets, those with distinct colors, in increasing binary-mask order (colex). The bound \(Q_{n,r,k}(a)\) is the number of admissible \((k+1)\)-sets all of whose \(k\)-subsets belong to the first \(a\) sets on that list. This is the colored colex extremal formulation: the first admissible \(a\) faces may support all such \((k+1)\)-faces, and FFK gives the same upper bound for arbitrary \(r\)-colored complexes having \(a\) faces at rank \(k\). Only masks on the first \(n\) labels need to be considered: Frohmader and FFK applied from rank 1, repeatedly, bound \(f_k\) by the number of admissible \(k\)-sets there. If a \((k+1)\)-set has a label outside the first \(n\), its colex-largest \(k\)-subset still does as well. That largest subset is obtained by deleting the smallest label, so a single prefix-rank lookup per candidate suffices. In particular \(Q_{n,r,1}(n)\) bounds \(m\).

**Consecutive-rank lower bound.** For a clique \(T\), write \(a(T)\) for its number of one-vertex extensions. For every \(k\)-clique \(S\),
\[
\sum_{v\in S}a(S\setminus\{v\})\le n+(k-1)a(S).
\]
The \(k\) vertices of \(S\) contribute once each. An external vertex contributes \(k\) times if it extends \(S\), and at most once otherwise. Summing over \(S\) gives \(\sum_{|T|=k-1}a(T)^2\) on the left, where the sum is over cliques. By Cauchy–Schwarz and \(\sum_{|T|=k-1}a(T)=kf_k\), this yields the [Moon–Moser inequality](https://real.mtak.hu/201267/)
\[
(k^2-1)f_{k+1}f_{k-1}\ge k^2f_k^2-nf_kf_{k-1}.
\tag{1}
\]
For triangles in an \(s\)-vertex graph with \(e'\) edges, set \(t_0(s,e')=\max(0,\lceil(4e'^2-s^2e')/(3s)\rceil)\) when \(s>0\), and \(t_0(0,0)=0\).

**Maximum-clique lower bound.** For a choice of \(D,e\), the cliques of order \(j\ge3\) with zero or one vertex in \(U\) number
\[
\binom rj+\sum_{d\in D}\binom d{j-1}.
\]
If \(uv\) is an edge in \(U\), its common neighborhood in \(K\) has size at least \(\max(0,d_u+d_v-r)\). Thus the cliques with exactly two vertices in \(U\) contribute at least the sum of the smallest \(e\) entries of the multiset of costs
\[
\left\{\binom{\max(0,d_u+d_v-r)}{j-2}:u,v\in U,\ u\ne v,\ \{u,v\}\text{ unordered}\right\}.
\]
For \(j=3\), add \(t_0(q,e)\) for triangles entirely in \(U\) and then take the maximum with \(t_0(n,m)\). For \(j>3\) keep only the indicated nonnegative contributions. Minimize separately at each rank over all \(D,e\) with the given \(m\), even if some pairs cannot be realized. Denote the result by \(L_{n,r,m}(j)\); it is a valid lower bound on \(f_j(H)\).

## 3. Exact finite reduction at order 14

The companion Python program applies the above formulas on integers only. Start with \(f_0=1,f_1=n\), and \(\binom r2\le m=f_2\le Q_{n,r,1}(n)\). At rank \(k\), a state \((m,a,h)\) records the current value \(a=f_k\) and a shape flag \(h\). Flag \(0\) means no strict drop has occurred; \(1\) means a strict drop has occurred but no later strict rise; \(2\) means a strict drop followed later by a strict rise. Store only the largest achievable preceding value \(b=f_{k-1}\) for each such key. For a candidate next value \(x\), test
\[
\max\left(L_{n,r,m}(k+1),\ \left\lceil
  \frac{k^2a^2-nab}{(k^2-1)b}\right\rceil\right)
 \le x\le Q_{n,r,k}(a).
\tag{2}
\]
Then advance to \((m,x,h')\), updating \(h'\) using the sign of \(x-a\) and storing preceding value \(a\). The lower endpoint is nonincreasing in \(b>0\), and the upper endpoint and shape update do not depend on \(b\). Thus a larger preceding value dominates any smaller one for the same state. No real clique-count sequence loses its future transitions by this compression. The check stops at rank \(r\) since the subsequent coefficients vanish and cannot produce an up step.

For \(n=14\) an initial pass for \(3\le r\le14\) returns a possible flag \(2\) only for \(r=7\). A second pass for \(r=7\) omits just two types of transition from flag 1 to flag 2: \(k=3\), \(a=m-1\), \(x>a\), with \(m=50\) or \(51\). This time it returns no flag 2. Consequently any actual counterexample on 14 vertices must have \(r=7\) and satisfy
\[
(f_2,f_3,f_4)\in\{(50,49,x):x\ge50\}\ \cup\
\{(51,50,x):x\ge51\}.
\tag{3}
\]
The second pass tests the omission on the transition itself, so merging prefixes cannot mask another possible origin of the first rise.

## 4. Eliminate the two residual cases

Let \(A=f_3-35=m-36\) denote the triangles not completely in \(K\), and let
\[
 L=\sum_{u\in U}\binom{d_u}2,\qquad V=\sum_{u\in U}\binom{d_u}3,\qquad
 c_{uv}=|N(u)\cap N(v)\cap K|,\qquad
 S=\sum_{uv\in E(H[U])}c_{uv}.
\]
If \(t\) denotes the number of triangles in \(U\), then \(A=L+S+t\). Set \(t_0=t_0(7,e)\), so \(L+t_0\le A\). Count four-cliques by the number of their vertices outside \(K\):

- Zero or one give \(35+V\).
- Exactly two contribute \(\sum_{uv\in E(H[U])}\binom{c_{uv}}2\le2S\), since \(c_{uv}\le 5\); a common neighborhood of six would give an 8-clique together with \(uv\).
- Exactly three correspond to triangles in the graphs \(H[N(z)\cap U]\) over the seven choices \(z\in K\). These graphs, counting repetitions across choices of \(z\), have \(S\) edges in total. Each edge has at most five extensions to a triangle, so this contribution is at most \(5S/3\).
- Exactly four give at most \(t\), since every such clique uses four triangles, and each triangle in the seven vertices of \(U\) extends to at most four four-cliques.

Hence \(f_4\le35+V+4S+t=35+V+4(A-L)-3t\le35+V+4(A-L)-3t_0\). The entire remaining check is over the \(\binom{13}{7}=1716\) nondecreasing lists of seven integers in \([0,6]\). For each \(m\), put \(e=m-21-\sum D\), discard \(e\) outside \([0,21]\) or \(L+t_0>A\), and take the maximum of this last upper bound. There are respectively seven and two surviving \(D\), and the maxima are respectively **43** and **40**. Both contradict (3).

Replay: run `python3 verify_independence_polynomial_minimum_order.py` from this directory with Python 3.10 or newer. The checker uses no dependencies, downloads, floating-point arithmetic, or exhaustive list of graphs. Its other exact check counts the witness subsets independently of the binomial formula.

## Relation to prior results

[Alavi, Malde, Schwenk and Erdős (1987)](https://www.renyi.hu/~p_erdos/1987-33.pdf) showed that arbitrary orderings of the nonconstant coefficients occur for suitable graphs, and asked the different question about forests. The general existence is therefore classical. The result here is the exact minimum order, not a new graph-class nonunimodality theorem or a second forest proof. Compare the earlier 16-vertex threshold-graph example of [Levit and Mandrescu](https://arxiv.org/abs/1007.0880), and the recent treatment of forests by [Li, Vallier and Zhang](https://arxiv.org/abs/2610.07943).
