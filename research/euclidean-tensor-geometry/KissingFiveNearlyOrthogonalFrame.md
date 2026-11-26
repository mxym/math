# A robust orthogonal-frame obstruction for the five-dimensional kissing problem

**Yongxian Zhang.** AI-assisted proof development and internal verification; no claim about the unrestricted kissing number.

Let \(X\subset S^4\) be a kissing code: \(\langle x,y\rangle\le1/2\) for all distinct \(x,y\in X\). Suppose \(X\) contains ten designated distinct points \(u_i,v_i\) for \(1\le i\le5\). Put
\[
\delta=\max_{i\ne j}|\langle u_i,u_j\rangle|,\qquad
\epsilon=\max_i\|u_i+v_i\|_2.
\]
If \(4\delta+\epsilon\le1/400\), then \(|X|\le39\). In particular this applies to a contained orthoplex consisting of five orthogonal antipodal pairs. The theorem also applies when none of the ten designated points are actually antipodal. No assertion of sharpness for this restricted class is made. The proof combines an orthant covering argument with averaged inequalities on the remaining Hamming edge types. This strengthens and supersedes the preliminary bound of 40 in the same frame neighborhood.

## Coordinate reduction

Write \(U\) for the square matrix with columns \(u_i\), and \(G=U^{\mathsf T}U\). The symmetric matrix \(G-I\) has row absolute sums at most \(4\delta\). Therefore \(G>0\), and the orthogonal matrix \(Q=UG^{-1/2}\) has columns \(f_i\) satisfying
\[
 \|U-Q\|_{\rm op}=\|G^{1/2}-I\|_{\rm op}\le 4\delta.
\]
The bound follows from \(|\sqrt \lambda-1|=|\lambda-1|/(\sqrt\lambda+1)\). In particular each \(f_i\) is within \(4\delta\) of \(u_i\), and each \(-f_i\) is within \(4\delta+\epsilon\) of \(v_i\). Consequently every remaining point \(x\) satisfies
\[
 |\langle x,f_i\rangle|\le1/2+4\delta+\epsilon\le c:=201/400.
\]
Use its sign label in the basis \(f_i\), with an arbitrary fixed choice at any coordinate zero. Let \(t_i=|\langle x,f_i\rangle|/c\). Then \(0\le t_i\le1\) and
\[
 \sum_i t_i^2=\rho:=1/c^2,\qquad 99/25\le\rho\le4.
\]
Scaled signed inner products between distinct points are at most \(\rho/2\le2\). For magnitudes \(a,b\) in \([0,1]\), \(ab\ge a^2+b^2-1\), since the convex function \(a^2+b^2-ab\) has maximum 1 over the four vertices of the square. Points with the same label would therefore have scaled inner product at least \(2\rho-5>2\). Thus the remaining points occupy distinct vertices of the Hamming cube on five signs.

For the estimates below we use the elementary fact that a sum \(\sum_j\sqrt{s_j}\) at fixed \(\sum_j s_j\), with all \(s_j\) in \([A,B]\), is minimized by taking all but at most one variable at endpoints. This follows by moving each pair of interior variables along their constant-sum segment to an endpoint, using concavity. For a lower bound on the total \(\sum_j s_j\), the minimum for the sum of roots occurs at the lower-bound total, whenever that total is feasible, by coordinatewise monotonicity.

## Two applications of one-coordinate adjacency

In adjacent occupied orthants with differing sign at coordinate \(i\), let \(t,s\) be their magnitude vectors. The scaled signed inner product equals \(\sum_{j\ne i}t_js_j-t_i s_i\). The elementary bound \(ab\ge a+b-1\) holds on \([0,1]^2\).

**First bound.** Every occupied adjacency at coordinate \(i\) forces both \(t_i,s_i>2/3\). Indeed, if \(t_i\le2/3\), then its four common squares sum to at least \(99/25-4/9=3+116/225\), and the partner's four common squares sum to at least \(99/25-1=2+24/25\). Their magnitude sums over the common coordinates are at least \(3+\sqrt{116}/15\) and \(2+\sqrt{24/25}\) respectively. The scaled signed product is therefore at least
\[
 1+\sqrt{116}/15+\sqrt{24/25}-2/3>2.
\]
For example \(\sqrt{116}/15>71/100\) and \(\sqrt{24/25}>97/100\) already suffice. This contradicts the kissing condition; exchange \(t,s\) to get the second bound. A vertex of the Hamming cube with all its five neighbors occupied will be called full. Each of its five coordinates is greater than \(2/3\).

**Second bound.** Suppose an occupied sign label and all labels within Hamming distance two of it are occupied. It and all its immediate neighbors are full. Choose \(i\) such that its magnitude \(t_i\le \sqrt{\rho/5}\le\sqrt{4/5}\), which exists by the norm equation. For the pair along that coordinate, the common squares of both points lie in \([4/9,1]\), and their respective totals are at least \(79/25\) and \(74/25\). The four common magnitude sums are therefore at least \(2+2/3+\sqrt{161}/15\) and \(2+2/3+\sqrt{116}/15\), by the concave minimum rule. The scaled signed product is at least
\[
 \frac43+\frac{\sqrt{161}+\sqrt{116}}{15}-\sqrt{4/5}>2.
\]
The strict comparison follows with the rational estimates \(\sqrt{161}>12.68\), \(\sqrt{116}>10.77\) and \(\sqrt{4/5}<0.895\), all checked by squaring. This is a contradiction.

Thus every Hamming ball of radius two must contain an unoccupied label. It has \(1+5+10=16\) vertices. Covering all 32 labels by radius-two balls centered on the unoccupied labels requires at least two such centers; hence there are at most \(10+30=40\) points. If there are exactly two centers their radius-two balls must be disjoint. Two radius-two balls in a binary cube intersect if the center distance is at most four (take a suitable midpoint of a shortest path); hence the two centers must have distance five.

## Excluding the two-hole case

Suppose there are 40 code points, so exactly 30 occupied labels. Flip coordinate signs so that the two antipodal holes are the binary labels of weights 0 and 5. The 20 labels of weights 2 and 3 are full. At a full vertex, call the three coordinates whose flips lead to other full vertices strong, and the two others weak. At each of the ten boundary vertices (weights 1 and 4), four coordinates lead to full vertices and are active; the remaining coordinate, whose flip leads to a hole, is exceptional. In general call a coordinate active at a vertex if its flip leads to an occupied vertex. Thus all coordinates at full vertices are active.

Let \(X_0,Y_0\) be the mean squared magnitudes of the strong and weak incidences, respectively, at full vertices, and \(B_0,A_0\) the mean squared magnitudes of active and exceptional incidences at boundary vertices. The norm equations give
\[
3X_0+2Y_0=4B_0+A_0=\rho .
\]
For squared active magnitudes \(z\in[4/9,1]\), concavity gives \(\sqrt z\ge(3z+2)/5\) by the chord between the endpoints. Hence if a common (unflipped) coordinate has two active magnitudes \(a,b\), then
\[
ab\ge a+b-1\ge \tfrac35(a^2+b^2)-\tfrac15.
\]
At the flipped coordinate use \(ab\le(a^2+b^2)/2\).

On an edge joining two full vertices, all four unflipped coordinates are active at both ends. With \(z,w\) the two squared magnitudes at the flipped coordinate, the scaled signed dot product is at least
\[
\tfrac65\rho-\tfrac45-\tfrac{11}{10}(z+w).
\]
Each strong incidence is an endpoint of exactly one such edge, so \(z+w\) has mean \(2X_0\). The exact bound \(\rho/2\) for the dot product gives
\[
X_0\ge (7\rho-8)/22.
\]

On a mixed edge joining a full and boundary vertex, the flipped coordinate is weak at the full vertex and active at the boundary vertex. Among the four unflipped coordinates, three are strong at the full vertex and active at the boundary vertex; the fourth is weak at the full vertex and exceptional at the boundary vertex. The last product is at least \(2/3\) of the squared boundary magnitude because the full magnitude is greater than \(2/3\), and the boundary magnitude lies in \([0,1]\). Each full vertex has two mixed edges, each boundary vertex has four, and each boundary active incidence is among the common active coordinates on three of the four edges. Thus the mean scaled signed dot product over the mixed edges is at least
\[
\begin{aligned}
\tfrac95(X_0+B_0)-\tfrac35+\tfrac23 A_0-\tfrac12(Y_0+B_0)
&=\tfrac{51}{20}X_0+\tfrac3{40}\rho-\tfrac35+\tfrac{41}{120}A_0 .
\end{aligned}
\]
Since \(A_0\ge0\), this lower bound minus \(\rho/2\) is at least
\[
\frac{170\rho-672}{440}\ \ge\ \frac{3}{1100}>0.
\]
This contradicts the kissing condition and proves the bound of 39.

## Scope and prior work

[Cohn–Rajagopal, *Variations on five-dimensional sphere packings*](https://arxiv.org/html/2412.00937v3) gives and compares the four known 40-point configurations. The theorem excludes the specified frame neighborhood in all four as an immediate corollary, without needing their coordinates. The general upper bound of 43 is given by the exact SDP certificates in [Tomar, *The kissing numbers in dimensions five and seven are at most 43 and 132*](https://www.mefyi.com/papers/kissing-numbers-five-seven/). The [November antipodal-count result](https://aixiv.online/abs/2611.02115) restricts the number of exact antipodal pairs; it does not exclude five such pairs in a 41–43 point code. The present result instead uses a specified Gram neighborhood of an orthoplex and excludes this neighborhood even for codes with zero exact antipodes. Searches did not identify this sign-cube obstruction in the checked sources. No SDP certificate, 40-point maximality computation, or general upper bound of 40 is claimed.
