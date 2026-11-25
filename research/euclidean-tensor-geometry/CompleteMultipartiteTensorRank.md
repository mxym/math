# Exact asymptotic rank for vertex-weighted complete multipartite graph tensors

**Yongxian Zhang.** AI-assisted research note.

Partition a finite vertex set into nonempty parts. Give every vertex \(v\) a positive real mass \(x_v\). Define the log edge weights \(W_{uv}=x_ux_v\) for vertices in distinct parts, and zero otherwise. Set \(N=\sum_v x_v\) and \(b=\max_P\sum_{v\in P}x_v\), where \(P\) ranges over the parts. Then over every field,
\[
 \Gamma_{\mathbb F}(W)=
 \begin{cases}
 b(N-b),& b\ge N/2,\\
 N^2/4,& b\le N/2 .
 \end{cases}
\]
Here \(\Gamma_{\mathbb F}\) is the continuous weighted graph exponent of [Zhou, Definition 2.26](https://arxiv.org/html/2610.34273v3); for weights \(\log_2 Q_{uv}\), it is \(\log_2\widetilde R_{\mathbb F}(\mathrm{WT}(Q))\). In particular, taking all vertex masses to be one determines the exponent of all complete multipartite graphs, including complete split graphs of odd total order. Zhou's Theorems 6.10 and 6.12 previously give the relevant bounds, and some exact cases, in those unweighted families. The new step is a matching grouped lower bound, using the cited exact rectangular theorem.

## Upper bounds

For any nonnegative vector \(y\) with \(y_u y_v\ge W_{uv}\) on distinct pairs, [Zhou's weighted upper bound, Theorem 5.6](https://arxiv.org/html/2610.34273v3) implies \(\Gamma_{\mathbb F}(W)\le(\sum_v y_v)^2/4\): all dual entries are nonnegative, and testing \(J-2P\) on \(y\) gives \(4\sum_{u<v}y_uy_vP_{uv}\le(\sum_v y_v)^2\). Choosing \(y=x\) gives \(N^2/4\). When \(N/2\le b<N\), put \(d=N-b\), multiply \(x_v\) by \(\sqrt{d/b}\) for vertices in a largest part and by \(\sqrt{b/d}\) for all other vertices. This keeps the cross-part weights incident to the largest part and overshoots or preserves the other weights. Now \(\sum_v y_v=2\sqrt{bd}\) gives \(bd\). For a single part \(W=0\) and the result is zero.

## Matching lower bounds

If \(b\ge N/2\), cut the largest part from the rest. The cut weighs \(b(N-b)\) and is a flattening-rank lower bound.

If \(b\le N/2\), treat the part masses as bins. While there are four or more bins, merge the two smallest; their sum is at most \(N/2\), since another two bins have total at least as large. This gives three groups of parts of masses \(a_1,a_2,a_3\le N/2\) unless there were only two parts initially, in which case their masses are \(N/2,N/2\) and the cut already proves the result. Group the tensor legs according to the three groups and project out internal edges. The resulting three-leg graph has edge weights \(a_1a_2,\ a_1a_3,\ a_2a_3\), since every cross-group pair was in distinct original parts. Neither grouping nor projecting increases tensor rank or asymptotic rank. This remains true at real weights by applying these operations before taking the approximation limit of Zhou Remark 2.29: the quotient weight on each cross-group pair is the sum of the corresponding approximating log weights, which converges to the advertised weight after division by the approximation scale.

The exact rectangular matrix multiplication exponent over every field is [OpenAI, pinned Lean theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean#L45-L55). In the reciprocal-triangle regime, when the largest of \(1/x,1/y,1/z\) is at most the sum of the other two, its value is
\[
 \frac{(xy+xz+yz)^2}{4xyz}.
\]
This is the arithmetic exponent and equals the weighted triangle exponent: the identification with rectangular multiplication is Zhou §6.1, and the bilinear rank and arithmetic-circuit exponents coincide (see the block-recursion argument in [the complete-graph note](OddCompleteGraphTensorRank.md)). With \(x=a_1a_2,y=a_1a_3,z=a_2a_3\), the reciprocal-triangle condition is exactly \(a_i\le a_j+a_k\) for each \(i\), which holds from the bin bound. The displayed expression equals \((a_1+a_2+a_3)^2/4=N^2/4\). This supplies the desired lower bound.

For example, \(K_{2,2,1}\) has exponent \(25/4\) even though its maximum cut weighs \(6\). For the complete split graph \(K_a\vee\overline K_b\) the formula gives \(ab\) for \(b\ge a\) and \((a+b)^2/4\) for \(b\le a\). No assertion is made about arbitrary non-complete split graphs, or unrelated weighted edge matrices.
