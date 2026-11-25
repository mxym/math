# Binary periodic alternating optimum (prior result)

Excerpt from Yongxian Zhang, [Two exact results for periodic translation-invariant quantum max-flow, v1.0.0](https://github.com/mxym/math/releases/tag/periodic-ti-quantum-max-flow-v1.0.0), preserved for the eight-cycle value at q=2. This is not a new claim of this release.

## Exact alternating quantum max-flow for the binary periodic cycle

**Result.** For every integer \(d\ge 2\), in the translation-invariant complex matrix-product-state model with physical and bond dimensions both two,
\[
  \operatorname{QMF}'(C_{2d},(\mathrm{odd},\mathrm{even}),2)=3\cdot 2^{d-2}.
\]
Thus the upper bound of Gesmundo, Landsberg and Walter, [*Matrix product states and the quantum max-flow/min-cut conjectures*](https://arxiv.org/abs/1801.09106), Theorem I.5, is attained for all lengths. The authors reported numerical tightness through \(d=10\); this note supplies a matching lower bound for arbitrary \(d\). The min-cut is \(2^d\) by the same theorem. This is a special case of periodic translation-invariant quantum max-flow, not a general max-flow/min-cut theorem.

### Witness

Use the same two \(2\times2\) slices at every vertex, \(A_i=x_i y_i^{\mathsf T}\), with \(x_0=(1,0)^{\mathsf T}, x_1=(0,1)^{\mathsf T}, y_0=(1,2)^{\mathsf T}, y_1=(2,1)^{\mathsf T}\). Put \(K_{ij}=y_i^{\mathsf T}x_j\), so \(K=\left(\begin{smallmatrix}1&2\\2&1\end{smallmatrix}\right)\). For odd and even binary words \(u=(u_1,\ldots,u_d)\) and \(v=(v_1,\ldots,v_d)\), the periodic tensor entry is
\[
 \operatorname{tr}(A_{u_1}A_{v_1}\cdots A_{u_d}A_{v_d})
 =\prod_{i=1}^d K_{u_i v_i}K_{v_i u_{i+1}},
 \qquad u_{d+1}=u_1.
\]
In the alternating flattening the row at \(u\) is therefore \(\bigotimes_{i=1}^d f_{u_i u_{i+1}}\), where the coordinates of \(f_{ab}\) are \(K_{a v}K_{v b}\) for \(v=0,1\). Explicitly
\[
 f_{00}=(1,4),\quad f_{01}=f_{10}=(2,2),\quad f_{11}=(4,1).
\]
In particular \(f_{a0},f_{a1}\) are independent for each start bit \(a\), and
\(f_{10}=\tfrac25(f_{00}+f_{11})\) with \(f_{00},f_{11}\) independent.

### Independent rows

For any fixed start bit \(a\), the \(2^k\) vectors obtained by taking products of the \(f\)'s along all \(k\)-edge paths on the two-bit alphabet starting at \(a\) form a basis of \((\mathbb C^2)^{\otimes k}\). This holds for \(k=0\). For \(k>0\), divide the paths by their first next bit \(b\). By induction their suffix vectors form a basis for each of the two choices of \(b\), and the independent first factors \(f_{a0},f_{a1}\) put the two resulting spaces in direct sum.

Select the rows with \((u_1,u_2)\) equal to \(00,10,11\), a total of \(3\cdot2^{d-2}\). Let \(U_{ab}\) be the span of their tails after the first edge factor, with \(u_1=a,u_2=b\). These tails are paths of \(d-1\) edges starting at \(b\) and ending at \(a\). Each group's tails are independent by the path-basis result. Moreover \(U_{00}\cap U_{10}=0\): these two groups partition the same fixed-start basis (start 0) by the distinct final bits.

A linear relation among the selected rows gives \(f_{00}\otimes z_{00}+f_{10}\otimes z_{10}+f_{11}\otimes z_{11}=0\), with \(z_{ab}\in U_{ab}\). Independence of \(f_{00},f_{11}\) and the displayed expression for \(f_{10}\) imply \(z_{00}=-(2/5)z_{10}\) and \(z_{11}=-(2/5)z_{10}\). The first equation and the disjointness of the two fixed-start subspaces give \(z_{10}=0\), and then all three tails vanish. Independence inside each group kills every coefficient. The claimed lower bound follows; with Theorem I.5 this proves equality.

The broader exact periodic problem is identified by Gesmundo, Lysikov and Steffan, [*Quantum max-flow in the bridge graph*](https://arxiv.org/html/2212.09794v2#S1.SS3). This argument arose from testing path and cycle factorization in the Euclidean tensor geometry research program; the actual proof is elementary linear algebra and uses no Euclidean-pricing theorem.

