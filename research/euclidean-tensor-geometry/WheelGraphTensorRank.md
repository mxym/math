# Exact asymptotic tensor rank of wheel graphs

**Yongxian Zhang.** Research note (AI-assisted proof development and verification). This is an application of the cited exact rectangular matrix-multiplication theorem and of Zhou's upper bounds, not a new proof of either theorem.

Let \(W_m=K_1\vee C_m\), where \(m\ge3\) counts rim vertices. Each edge represents an independent two-dimensional maximally entangled pair, and the factors incident to each vertex are grouped into one tensor leg. Over every field \(\mathbb F\), the base-2 logarithm of the asymptotic tensor rank is
\[
 \log_2\widetilde R_{\mathbb F}(T_{W_m})=
 \begin{cases}
 25m/16,&m\ {\rm even},\\[2pt]
 (5m+1)^2/[16(m+1)],&m\ {\rm odd}.
 \end{cases}
\]
For example, the five-rim wheel has exponent \(169/24\), strictly above its maximum cut of \(7\). The right sides were known as upper bounds in [Zhou, Theorem 6.14](https://arxiv.org/html/2610.34273v3#S6.SS6). Here we match them by lower bounds from a three-leg restriction.

## Quotient lower bound

Partition the vertices into three sets. Group each set's tensor legs and apply a linear functional killing all but the label 1 on both ends of each internal edge. The remaining three-tensor is a matrix-multiplication tensor: its three edge dimensions are the products of the dimensions of the edges crossing the corresponding class pairs. Both grouping and local projection take each tensor-rank-one summand to a tensor of rank at most one, and the same maps apply at every tensor power.

For positive edge logs \(x,y,z\), let \(\Psi(x,y,z)\) be [OpenAI's exact rectangular exponent](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean#L45-L55), symmetric in the logs. With \(x\ge y\ge z\), it is
\[
 x+y+\frac{[(x+y)z-xy]_+^2}{4xyz}.
\]
This is a lower bound on the log asymptotic tensor rank of the three-tensor. In fact, given a rank-\(r\) decomposition of any fixed power of the three-tensor, bilinear block recursion gives matrix-multiplication circuits of size \(O(jr^j)\) at its \(j\)-fold matrix sizes: the linear work at each level uses at most a constant (depending on the fixed decomposition) times the number of blocks, and every input/output dimension is at most \(r\) by flattening. Padding to consecutive powers costs only constant factors in each matrix dimension. Infimizing over fixed powers bounds the arithmetic exponent above by the log asymptotic rank.

When all three reciprocal triangle inequalities hold (in particular \((x+y)z\ge xy\) for the smallest log \(z\)), the formula simplifies to the fully symmetric expression
\[
 \Psi(x,y,z)=\frac{(xy+xz+yz)^2}{4xyz}.
\]
This follows by expansion. We will use this symmetric form even if the smallest of the three logs varies between cases.

For an even rim take the hub as a singleton and the two alternating rim classes. The three logs are \((m,m/2,m/2)\). The symmetric formula gives \(25m/16\). For \(m=2k+1\), alternate around the rim with exactly one same-class edge. The logs are \((2k,k+1,k)\). The reciprocal condition is \(1/k\le 1/(2k)+1/(k+1)\), true for \(k\ge1\). Thus \(\Psi=(5k+3)^2/[8(k+1)]\), the stated odd expression. Apply Zhou's theorem to finish the proof.

## Constant rim and spoke dimensions

Give every rim edge dimension \(R>1\) and every spoke dimension \(S>1\), and put \(r=\log_2 R\) and \(s=\log_2 S\).

**Even \(m\).** The exact value is \(m\Psi(r,s/2,s/2)\) for all \(R,S\). The quotient above gives the lower bound by homogeneity. For the upper bound, tensor-square the wheel and identify each spoke pair of dimension \(S^2\) as two pairs each of dimension \(S\), one for each incident rim triangle. Each rim edge in the square has dimension \(R^2\). Thus the squared wheel is a regrouping of \(m\) matrix-multiplication tensors with logs \((2r,s,s)\). Their log asymptotic ranks equal \(\Psi(2r,s,s)\): the reverse inequality of the lower-bound argument follows since circuit size bounds bilinear rank up to a constant, by retaining only the bi-degree \((1,1)\) component and at each multiplication adding at most two products of a linear form of each input. Submultiplicativity under tensor products and monotonicity under grouping give the upper bound, after dividing by two.

**Odd \(m=2k+1\).** For \(4/(m+1)\le s/r\le4m/(m+1)\) the exact value is
\[
  \frac{r}{m+1}\left(m+\frac{(m+1)s}{4r}\right)^2.
\]
For \(s/r\ge4m/(m+1)\) it is \(ms\). The same quotient has logs \((2kr,(k+1)s,ks)\). The two nontrivial reciprocal conditions are
\[
 \frac1{ks}\le\frac1{2kr}+\frac1{(k+1)s},
 \qquad
 \frac1{2kr}\le\frac1{(k+1)s}+\frac1{ks};
\]
these give precisely the interval above. In it the symmetric formula, with \(xy=k(k+1)s^2\) and \((x+y)z=2kmsr\) for \(z=2kr\), gives the claimed value. Above the interval flatten across the hub to get \(ms\).

For the upper bounds apply [Zhou, Theorem 5.6 and the proof of Theorem 6.14](https://arxiv.org/html/2610.34273v3) to the weighted input. For any feasible dual matrix, let \(A\) and \(B\) be its sums over rim edges and over spokes, respectively. The path inequalities on the unweighted support of the rim and a copositive test with hub coordinate \(t\) give \((m+1)A+4tB\le(m+t)^2\) for all \(t\ge0\). The weighted objective is \(rA+sB\). Take \(t=(m+1)s/(4r)\) for the middle interval. In the high-spoke regime take \(t=m\) and use \(A\ge0\); all feasible matrix entries are nonnegative. Specifically \(rA+sB\le s((m+1)A/(4m)+B)\le ms\). The low-spoke regime \(s/r<4/(m+1)\) is not settled by this argument.

The claimed result concerns the asymptotic tensor rank, not the single-copy tensor rank or subrank. The weighted estimates are for constant dimensions within each of the two edge types.
