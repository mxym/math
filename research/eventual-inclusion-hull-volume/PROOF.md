# Eventual inclusion monotonicity of expected random hull volume

For a convex body \(K\subset\mathbb R^d\) (compact with nonempty interior) let \(V_n(K)\) be the expected **unnormalized** \(d\)-volume of the hull of \(n\) independent samples from its normalized volume law. Write \(H_m\) for the hull of the first \(m\) points and \(|K|\) for volume. For every fixed \(d\ge1\) there are \(a_d>0\) and \(N_d<\infty\), depending only on dimension, such that for all \(n\ge N_d\) and all \(K\subset L\),
\[
             V_n(L)-V_n(K)\ \ge\ a_d (|L|-|K|).
\]
In particular proper inclusion gives strict inequality. This concerns the **dimension-only threshold** in Beermann–Reitzner, *Monotonicity of functionals of random polytopes*, end of §2, [arXiv:1706.08342](https://arxiv.org/abs/1706.08342); it does not assert a minimal threshold or monotonicity for every sample size. The two gains below measure respectively the addition of a specified exterior point and that of one more ordinary uniform point. They are different experiments.

## 1. A gain for every exterior point

First, for a convex body \(D\), any \(x\in\mathbb R^d\), and independent uniform \(Y_1,\ldots,Y_d\) in \(D\), there is the elementary bound
\[
 {\mathbb E}|\operatorname{conv}(x,Y_1,\ldots,Y_d)|
 \ \ge\ b_d|D|,\qquad b_d=\frac{(4d)^{-d^2}}{4^d d!}.
\]
Choose \(z_i\in D\) maximizing the absolute determinant \(M\) of the columns \(z_i-x\); it is positive because \(D\) has interior. In this basis all vectors \(y-x\), \(y\in D\), have coordinates in \([-1,1]^d\), by replacing one maximizing column and using Cramer's rule. Thus \(M\ge |D|/2^d\). With \(\delta=1/(4d)\), the event \(Y_i\in (1-\delta)z_i+\delta D\) for every \(i\) has probability \(\delta^{d^2}\). In basis coordinates its column matrix is \(I+E\) with all entries of \(E\) bounded in modulus by \(2\delta\). The maximum absolute row sum is at most \(1/2\), so every eigenvalue of \(I+E\) has modulus \(\ge1/2\), and its absolute determinant is at least \(2^{-d}\). Dividing absolute determinant in the original coordinates by \(d!\) proves the assertion.

Let \(m\ge2d\) and \(x\notin\operatorname{int}K\). Choose an affine height \(h\), nonconstant, with \(h(x)\le0=\min_K h\), by separation or support. Take the cap \(C=K\cap\{h\le t\}\) of volume \(|K|/m\): the cap-volume function is continuous and strictly increasing between the extreme heights. Its upper half \(D=C\cap\{h\ge t/2\}\) has \(|D|\ge2^{-d}|C|\), since it contains \((C+z)/2\) for \(h(z)=t\), \(z\in C\). Among the \(m\) samples require exactly \(d\) in \(D\) and all remaining samples outside \(C\). This has probability
\[
 {m\choose d} (|D|/|K|)^d(1-1/m)^{m-d}
 \ \ge\ p_d:=\frac{2^{-d(d+1)-2}}{d!}.
\]
Indeed \({m\choose d}\ge(m/2)^d/d!\), and \((1-1/m)^m\ge1/4\) for \(m\ge2\). Conditionally on this event, the \(d\) selected points \(Y_i\) in label order are independent uniform in \(D\). All of \(H_m\) lies at height \(\ge t/2\), whereas the half-scaled copy about \(x\) of \(\operatorname{conv}(x,Y_1,\ldots,Y_d)\) is contained in \(\operatorname{conv}(x,H_m)\) and lies at height \(\le t/2\). Thus their intersection has zero \(d\)-volume. Taking expectations, and using nonnegative gain on the rest of the probability space, gives
\[
 {\mathbb E}\big[|\operatorname{conv}(x,H_m)|-|H_m|\big]
 \ \ge\ c_d |K|/m,\qquad c_d=p_db_d 2^{-2d}.\tag{1}
\]

## 2. A smaller gain for an ordinary uniform point

Put \(u_j=\sup_K {\mathbb E}|K\setminus H_j|/|K|\). We record a self-contained uniform proof that \(u_j\to0\). By an affine change normalize a maximum-volume inscribed simplex to \(T=\operatorname{conv}(0,e_1,\ldots,e_d)\). Replacing \(e_i\) by \(y\in K\) shows that \(|y_i|\le1\). Hence \(T\subset K\subset[-1,1]^d\) and \(K\) contains a cube \(z+\rho[-1,1]^d\), \(\rho=1/(2d)\), \(z=(\rho,\ldots,\rho)\).

Partition \([-1,1]^d\) into \((2J)^d\) cells of side \(1/J\), \(J\) an integer \(>4d\). Choose one representative \(w\in K\) for each cell meeting \(K\). The cube of radius \(1/J\) about \(w\) contains \(w+(K-w)/(2J)\), of relative volume \((2J)^{-d}\). Except on an event of probability at most \((2J)^d\exp[-j/(2J)^d]\), each representative has one sample within sup-norm distance \(1/J\). Then all of \(K\) is within distance \(2/J\) of the sample. For every direction \(v\), \(h_{H_j}(v)\ge h_K(v)-2\|v\|_1/J\), where \(h_K\) denotes the support function. Since \(h_K(v)-z\cdot v\ge\rho\|v\|_1\), this implies \(H_j\supset z+(1-4d/J)(K-z)\). Bernoulli's inequality yields
\[
 u_j\le 4d^2/J+(2J)^d\exp[-j/(2J)^d].\tag{2}
\]
Taking \(J\) large then \(j\) large proves the claim.

For the ordinary add-one gain write \(n=m+1\), \(k=\lfloor n/2\rfloor\), and condition on the first \(k\) samples. Fix a test point \(y\in K\). If \(y\in H_k\) it cannot be newly covered by the last sample. If \(y\in H_n\), choose a representation of \(y\) in a simplex on at most \(d+1\) sample points, by Carathéodory. Removing any single label not in the representation cannot lose \(y\). Hence among the last \(n-k\) labels the number individually essential to covering \(y\) is at most \(d+1\), and is zero if \(y\notin H_n\) or \(y\in H_k\). Conditional exchangeability makes the probability that the last label is essential at most \((d+1)\mathbf1_{\{y\notin H_k\}}/(n-k)\). Integrating over \(y\), then taking expectations, gives
\[
 0\le V_n(K)-V_{n-1}(K)\le \frac{2(d+1)}n\,u_k\,|K|.\tag{3}
\]
No concavity in sample size or assumption of smooth boundary is needed.

## 3. From local to arbitrary inclusions

Choose \(N_d\ge 2d+1\) so that \(u_{\lfloor n/2\rfloor}\le c_d/[4(d+1)]\) whenever \(n\ge N_d\); (2) gives a computable dimension-only choice. Then (1) and (3), with \(m=n-1\), give for every \(x\notin\operatorname{int}K\)
\[
 {\mathbb E}|\operatorname{conv}(x,H_{n-1})|-V_n(K)
 \ \ge\ g\,|K|,\qquad g=\frac{c_d}{2(n-1)}.\tag{4}
\]
Fix \(n\ge N_d\). For \(K\subset L\) put \(q=1-|K|/|L|\). The number of samples from \(L\setminus K\) in an \(n\)-sample from \(L\) is binomial \((n,q)\). With no exterior points the conditional mean volume is \(V_n(K)\). With exactly one exterior point it is at least \(V_n(K)+g|K|\) by (4), since the other points are independent uniform in \(K\). With at least two exterior points the conditional mean is at least zero, while \(V_n(K)\le|K|\). A union bound over pairs gives
\[
 V_n(L)-V_n(K)\ \ge\ |K|\big[nq(1-q)^{n-1}g-\tbinom n2q^2\big].
\]
If \(0<q\le \min\{1/(2n),g/[2(n-1)]\}\), this is at least \(nqg|K|/4\), which in turn is at least \(c_d(|L|-|K|)/16\), because \(|L|-|K|=q|K|/(1-q)\le2q|K|\). For \(q=0\) the conclusion is immediate. Finally the nested Minkowski interpolation \(K_s=(1-s)K+sL\), \(0\le s\le1\), has continuous volume bounded below by \(|K|>0\). Nesting also follows from \(h_{K_s}=(1-s)h_K+s h_L\). Divide \([0,1]\) finely enough that all successive relative increments meet the small-\(q\) condition. Adding their inequalities proves the theorem with \(a_d=c_d/16\).

This proof uses elementary cap geometry, Carathéodory's theorem, and compact, full-dimensional convex bodies. Neither equal-volume normalized hull fractions nor monotonicity of expected numbers of faces as the sample size grows is asserted. Bounds on constants and thresholds are intentionally not optimized.
