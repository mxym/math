# A hyperplane-moment proof of flat breaking

## 1. Statement

For a binary vectorial function \(F:\mathbb F_2^n\to\mathbb F_2^m\), order-\(r\) sum-freedom means that \(\sum_{x\in A}F(x)\ne0\) for every \(r\)-dimensional affine flat \(A\), with \(2\le r\le n\). A \(k\)-flat is **broken** when its image as a set is not an affine subspace of the output space. In particular, a flat image of any dimension is unbroken; breaking is not just a statement about injectivity.

**Theorem.** If \(3\le k\le n\) and \(F\) is both order-\(k\) and order-\((k-1)\) sum-free, then for every \(k\)-flat \(A\) in the domain,
\[
 \dim\operatorname{aff}F(A)\ \ge\ k+1 .
\]
Consequently \(F\) breaks every \(k\)-flat. In the square case \(m=n\) this answers Open Problem 3 of Rodríguez-Aldama, Šehović, Pasalic and Kudin, which asks this implication for \(k>3\). At \(k=n=m\), the hypotheses are impossible by the same theorem.

## 2. Complementary hyperplanes on one flat

Write \(A=a+V\) with \(\dim V=k\). Translate the output by \(F(a)\), putting \(f(v)=F(a+v)+F(a)\), and let \(W=\operatorname{span}\{f(v):v\in V\}\); this has dimension \(\dim\operatorname{aff} F(A)\). For this local argument one can take \(k\ge2\): the whole flat and each of its hyperplanes have even size, so the translation does not change any of their sums.

Define \(T=\sum_{v\in V}f(v)\) and assume \(T\ne0\). For \(\ell\in V^*\), put
\[
 L(\ell)=\sum_{v\in V}\ell(v)f(v)\in W.
\]
The scalar \(\ell(v)\) is binary, so \(L:V^*\to W\) is linear. For a nonzero \(\ell\), the sums on its two complementary hyperplanes \(\{a+v:\ell(v)=1\}\) and \(\{a+v:\ell(v)=0\}\) are, respectively, \(L(\ell)\) and \(T+L(\ell)\). If every hyperplane sum is nonzero, then for all nonzero \(\ell\) we have \(L(\ell)\notin\{0,T\}\). Thus the induced map
\[
 \bar L:V^*\longrightarrow W/\langle T\rangle
\]
has zero kernel. Its domain has dimension \(k\) and codomain has dimension \(\dim W-1\), proving \(\dim W\ge k+1\). The global sum-freedom hypotheses guarantee these conditions on every \(A\): its hyperplanes are genuine \((k-1)\)-flats in the original domain. Finally, an affine subspace of dimension \(k+1\) or greater would have more than \(2^k\) points, while the image of \(A\) has at most \(2^k\) points. So the affine span cannot equal the image set.

## 3. Local count and shape of zero-sum hyperplanes

Continue with a single \(A\), \(k\ge2\), and \(T\ne0\), but drop the assumption about the individual hyperplane sums. Set \(K=\ker\bar L\), \(b=\dim K\), and \(r=\dim W\). For every nonzero \(\ell\in K\), exactly one of its complementary hyperplanes has zero sum: their sums are \(0,T\) in some order. For every other \(\ell\ne0\) both sums are nonzero. Over \(\mathbb F_2\), each parallel hyperplane pair has a unique nonzero defining form. Thus the number \(Z_A\) of zero-sum hyperplanes *within* \(A\) is exactly
\[
 Z_A=2^b-1,\qquad b=k-\operatorname{rank}\bar L,\qquad
 b\ge\max(0,k-r+1).                                                        \tag{1}
\]
If \(F(A)\) is a flat of dimension \(r\), then \(r\le k-1\): \(r=k\) would make the restriction bijective onto a \(k\)-flat, whose points sum to zero for \(k\ge2\). So any such flat image with \(T\ne0\) has at least \(2^{k-r+1}-1\ge3\) zero-sum hyperplanes.

There is also an affine description. Write \(L(\ell)=\gamma(\ell)T\) on \(K\), where \(\gamma:K\to\mathbb F_2\) is linear. Every linear functional on \(K\) extends to \(V^*\), so there is \(v_0\in V\) with \(\ell(v_0)=\gamma(\ell)\) on \(K\). Let
\[
 E=a+v_0+K^\perp,\qquad K^\perp=\{v\in V:\ell(v)=0\text{ for every }\ell\in K\}.
\]
The zero-sum hyperplanes are exactly the hyperplanes of \(A\) disjoint from \(E\): one such hyperplane for each nonzero \(\ell\in K\), with equation \(\ell(v)=1+\gamma(\ell)\). A form outside \(K\) is nonzero on \(K^\perp\), so each of its two hyperplanes meets \(E\). Equivalently the complementary nonzero-sum hyperplanes in these pairs all contain \(E\). If \(K=0\), then \(E=A\) and no hyperplane is disjoint from it.

## 4. Local attainability

For every \(k\ge3\) and \(1\le r\le k-1\) there is a map \(f:\mathbb F_2^k\to\mathbb F_2^r\) that is onto, has \(T\ne0\), and has exactly \(2^{k-r+1}-1\) zero-sum hyperplanes. Start with the projection \(P\) to the first \(r\) coordinates. Write \(u_i\) for input basis vectors and \(e_i\) for output basis vectors. Add the following changes to its values:
\[
 \delta(0)=e_r+\sum_{i=1}^{r-1}e_i,\qquad
 \delta(u_i)=e_i\ (1\le i<r),\qquad
 \delta(v)=0\text{ otherwise}.
\]
All changed input points were in distinct fibers of \(P\), each originally of size \(2^{k-r}\ge2\); at least one untouched preimage remains for each output. Thus \(f=P+\delta\) is onto. The total sum of \(P\) is zero, and the total change is \(e_r\), so \(T=e_r\). The moment of \(P\) against any \(\ell\) is zero: each coordinate of \(\ell(v)P(v)\) is a polynomial of degree at most two, and each monomial of degree less than \(k\) sums to zero on the binary \(k\)-cube. The changes therefore give
\[
 L(\ell)=\sum_{i=1}^{r-1}\ell(u_i)e_i,\qquad\operatorname{rank}\bar L=r-1 .
\]
This computation can use the unshifted output since all the tested hyperplanes and the full domain have even size. Formula (1) proves the exact count. In the remaining local case \(k=2,r=1\), a map with a single nonzero value has both output values and total sum one; exactly three hyperplanes avoid its nonzero point, proving attainability there.

The \(k+1\) affine-span bound under both nonzero-sum conditions is also attained locally, with output dimension \(k+1\). Give \(0\) the output \(e_0+\cdots+e_k\), give each \(u_i\) the output \(e_i\), and set all other outputs to zero. There is at least one such other point for \(k\ge2\); the outputs therefore affinely span the whole output space. This time \(T=e_0\), and \(\bar L\) is injective by the \(k\) independent output coordinates \(e_1,\dots,e_k\). These examples establish local sharpness only, and make no claim about extending a local example to global sum-freedom in larger dimension.
