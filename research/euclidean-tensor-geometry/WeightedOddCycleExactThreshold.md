# Exact maximum-cut threshold for a weak edge on odd cycles

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Let P be feasible for Zhou's path-strengthened completely positive bound [Theorem 5.6 and Lemmas 5.1, 5.4](https://arxiv.org/html/2610.34273v3#S5.SS3). Label the cycle 0,1,2,3,4, and color it by A={0,2,4}, B={1,3}; the internal edge is 04. Put d_ij=1-p_ij on A–B pairs. The quadratic test vector (1,2,2,2,1) balances its total weight 4 on both colors. Cancelling the contribution of the hard cut gives
\[
 p_{04}+2(p_{02}+p_{24})+4p_{13}
 \le 2(d_{01}+d_{03}+d_{14}+d_{34})+4(d_{12}+d_{23}).
\]
The spectral triangle inequalities imply d_03≤d_01+p_13, d_14≤d_34+p_13 and p_04≤p_02+p_24. Substitution proves
\[
 p_{04}\le \tfrac43(d_{01}+d_{12}+d_{23}+d_{34}).
\]
Thus a pentagon with path weights w_01,w_12,w_23,w_34 and weak edge t=w_04 has both asymptotic exponent and path-strengthened CP bound exactly W=w_01+w_12+w_23+w_34 whenever t≤(3/4) min_e w_e. Indeed, its objective is W−Σ_e w_e d_e+t p_04≤W, while the displayed cut realizes W. This direction works over every field independently of the exact rectangular theorem.

For four unit edges and 0≤t≤1 the threshold is exact: if t>3/4, group the vertices as {0},{1,3},{2,4}, producing weighted triangle (3,1,t). The pinned [OpenAI rectangular theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean#L45) gives lower bound \(4+(4t-3)^2/(12t)>4\), whereas the maximum cut stays 4. Independently of the exact rectangular theorem, the same reasoning gives sharp threshold for Zhou's path-strengthened CP and SDP bounds: take an optimal feasible triangle SDP matrix (Zhou Prop. 6.2), and copy the same Gram vector to every vertex in one group. This preserves both PSD and triangle inequalities and reproduces the triangle objective. At t=1 the weighted cut result and the conditional lower bound do not close the 49/12 to 25/6 gap for the unrestricted C5.

For longer odd cycles one can partition the even crossing path into length-four chunks, using triangle inequalities between successive endpoints and the displayed inequality on each chunk. In particular, if the odd cycle length is 1 modulo 4, the same sufficient t≤(3/4) min_e w_e holds. If an extra length-two chunk is needed, use instead the two-edge inequality with factor 2, or pair weighted adjacent edges with the asymmetric harmonic-capacity test derived from coordinates (a,a+b,b).


## All even crossing paths: the exact uniform threshold

For arbitrary even \(L\ge2\), label a path \(0,1,\ldots,L\), with even vertices on one side and odd vertices on the other. A Zhou-feasible \(P\) on the ambient graph satisfies
\[
 p_{0,L}\le\frac{L}{L-1}\sum_{i=0}^{L-1}(1-p_{i,i+1}).
\]
Use the copositive constraint with test weights \(a_0=a_L=1\), \(a_i=2\) for \(0<i<L\), and zero outside the path. The even and odd side weights both equal \(L\). Writing \(d_{ij}=1-p_{ij}\) on opposite-side pairs and cancelling the hard-cut contribution yields
\[
 \sum_{i<j,\ i\equiv j\pmod 2} a_i a_j p_{ij}
 \ \le\ \sum_{i<j,\ i\not\equiv j\pmod 2} a_i a_j d_{ij}.
\]
Keep the adjacent cross terms. For each nonadjacent cross pair \(i<j\) use:
- For \(i>0,j<L\), split its coefficient four equally between \(d_{ij}\le d_{i,i+1}+p_{i+1,j}\) and \(d_{ij}\le d_{j-1,j}+p_{i,j-1}\).
- For \(i=0\), use just the first inequality, with coefficient two.
- For \(j=L\), use just the second inequality, with coefficient two.

These substitutions follow from the spectral triangle inequalities, and no cross pair has both endpoints \(0,L\). Every same-side pair \(u<v\) entirely in the interior appears twice on the substituted right, once from \((u-1,v)\) and once from \((u,v+1)\); its coefficient four cancels. Same-side pairs touching either endpoint occur in no substitutions. Each adjacent path term receives total coefficient \(L\): if interior it starts with four and receives two from each of \((L-4)/2\) eligible pairs, while at the boundary it starts with two and receives two from each of \((L-2)/2\) eligible pairs. For clarity, on an interior edge \((i,i+1)\), \(i\) even, the eligible counts from the first and second substitutions are \((L-i-2)/2\) and \(i/2-1\); for \(i\) odd they are \((L-i-3)/2\) and \((i-1)/2\). Thus
\[
 p_{0,L}+2\sum_{0<j<L,\ j\text{ even}}(p_{0,j}+p_{j,L})
 \ \le\ L\sum_{i=0}^{L-1}d_{i,i+1}.
\]
The left side is at least \((L-1)p_{0,L}\) by the triangle inequality.

For any weighted odd cycle of length \(L+1\) this proves that the alternating cut omitting its designated closing edge of weight \(t\) is exact for the graph exponent and for Zhou's strengthened CP and SDP programs if \(t\le\frac{L-1}{L}\min_i w_{i,i+1}\). The other path edges have weights \(w_{i,i+1}\). The same proof works for arbitrary graphs when every same-side demand is routed along an even path in the crossing graph; each path of length \(L\) contributes capacity load \(\frac{L}{L-1}\) times its routed weight on every path edge, and the total load must be at most the edge's original weight. This gives an explicit sufficient exact-cut certificate independently of the OpenAI exact rectangular result.

For \(L\) unit edges and \(0\le t\le1\), the threshold \((L-1)/L\) is sharp. Group \(0\) alone and the odd and nonzero even vertices each into one group. The quotient triangle has weights \((L-1,1,t)\). The existing exact rectangular theorem gives a strict gap over the cut size \(L\) for \(Lt>L-1\) (and confirms the stated threshold in the active regime). For conic sharpness independently of the rectangle tensor equality, lift an optimal three-party SDP solution from Zhou Prop. 6.2 by repeating its three Gram vectors within the groups. No claim about the exact graph exponent strictly above the threshold.
