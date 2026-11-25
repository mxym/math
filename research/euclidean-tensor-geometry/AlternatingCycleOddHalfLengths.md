# Exact periodic alternating quantum max-flow at every odd half-length

**Yongxian Zhang.** AI-assisted, internally checked research note; no external peer review claimed.

Let \(F_s(p,D)\) be the maximum alternating flattening rank for a periodic cycle of length \(2s\) with physical dimension \(p\), bond dimension \(D\), and the same complex slice tensor at every site, as in [Gesmundo–Landsberg–Walter](https://arxiv.org/abs/1801.09106). The flattening has entries \(M_{u,v}=\operatorname{tr}(A_{u_0}A_{v_0}\cdots A_{u_{s-1}}A_{v_{s-1}})\) for words \(u,v\) of length \(s\).

**Theorem.** For every odd \(s\ge3\) and every \(p\ge1\),
\[
F_s(p,p)=
\begin{cases}
3\cdot 2^{s-2},&p=2,\\
p^s,&p\ne2.
\end{cases}
\]
If \(D\ge p\), the only failure of full rank is \(p=D=2\). This is an exact solution for the stated one-site periodic model and these lengths, not for all cycle lengths or all pairs \(p,D\).

**Odd physical dimension: character witness.** Identify physical and virtual symbols with \(\mathbb Z/p\mathbb Z\), and choose a primitive \(p\)-th root \(\zeta\). Set \(A_a=e_a y_a^{\mathsf T}\), with \((y_a)_b=\zeta^{ab}\). The trace of a cyclic word is the product of the pairwise overlaps \(y_a^{\mathsf T} e_b\), so
\[
M_{u,v}=\zeta^{\sum_i(u_iv_i+v_i u_{i+1})}
       =\zeta^{\sum_i u_i(v_i+v_{i-1})}.
\]
Let \(R\) act on words by \((Rv)_i=v_{i-1}\). Then \(R^s=I\) and \((I+R)\sum_{j=0}^{s-1}(-R)^j=2I\) because \(s\) is odd. Since \(2\) is invertible modulo odd \(p\), \(v\mapsto (I+R)v\) is bijective. Thus \(M\) is the full Fourier matrix on \((\mathbb Z/p\mathbb Z)^s\) with its columns permuted. This also works at any \(D\ge p\) by zero-padding; for \(p=1\) use one nonzero scalar slice and padding. This part uses the standard bilinear character construction, not a new Fourier theorem.

**Even physical dimension at least four: rectangular witness.** Write \(p=ab\), for example \(a=2,b=p/2\). Take letters \((u,v)\in U\times V\) on a virtual space with disjoint sets \(U,V\) of sizes \(a,b\) and slices \(A_{uv}=E_{u,v}+E_{v,u}\). Here \(a+b\le p\). The [rectangular spoke calculation](AlternatingCycleRectangularSpokes.md) gives the sum of two permutations in the flattening: each trace walk chooses one of the two starting sides, and the even word is uniquely determined by the odd word and that choice. The relative permutation has order dividing the odd integer \(s\); its eigenvalues do not include \(-1\). The sum is invertible. Zero-pad to any \(D\ge p\). Square cases at every length were already known by [GLW Remark I.6](https://arxiv.org/html/1801.09106#S1).

**Binary case.** The upper bound at \(p=D=2\) is [GLW Theorem I.5](https://arxiv.org/html/1801.09106#S1.SS4). A previously archived rank-one construction shows equality for every \(s\ge2\), not only odd \(s\): [existing immutable proof](https://github.com/mxym/math/blob/16a0c94c6893cff67780fbb64b0c4bc8addffbf1/paper.md). At \(D\ge3\), take \(a=1,b=2\) in the same rectangular witness to attain \(2^s\) for odd \(s\).

The upper bound in each full-rank case is the physical matrix dimension \(p^s\). The emphasis is the combined exact classification: the character witness covers odd dimensions but loses rank in even dimension, while the rectangular spoke witness supplies the missing even dimensions \(p\ge4\). In particular this includes all nonsquare even \(p\ge6\), with no dependence on the odd half-length. The other family of lengths, divisible by four, is separate; see the [rotation determinant note](AlternatingCycleRotationDeterminant.md) and [odd-dimensional eight-cycle note](eight-cycle-odd-poles/AllOddDimensions.md).
