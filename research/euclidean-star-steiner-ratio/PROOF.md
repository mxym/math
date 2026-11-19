# The star Steiner ratio in Euclidean dimensions at least three

For a finite set \(P=\{p_1,\ldots,p_N\}\subset\mathbb R^d\), \(N\ge2\), set
\[
 S(P)=\min_i\sum_j|p_i-p_j|,\qquad W(P)=\min_{o\in\mathbb R^d}\sum_j|p_j-o|.
\]
Write \(\sigma\) for uniform probability on \(S^{d-1}\), and
\(c_d=\int |u-e|\,d\sigma(u)\) for a fixed unit vector \(e\).
**Theorem.** For every integer \(d\ge3\), \(\sup_P S(P)/W(P)=c_d\).
In particular, the three-dimensional supremum is \(4/3\). The claim is about minimum stars, not the length of a Steiner tree; it does not determine the planar star ratio.

**Reduction to a radial kernel.** Fix a geometric median \(o\), which exists by continuity and coercivity. If \(o\in P\), then \(S=W\), sufficient since \(c_d>1\) (a random unit chord has length strictly larger on average than its projection along \(e\), which has mean 1). Otherwise let \(r_i=|p_i-o|>0\), \(u_i=(p_i-o)/r_i\), \(s_i=\log r_i\), \(t_{ij}=u_i\cdot u_j\), and \(z_{ij}=\cosh(s_i-s_j)=(r_i/r_j+r_j/r_i)/2\). In the average of star costs with center probabilities \(r_i^{-1}/\sum_h r_h^{-1}\), symmetrizing the ordered pairs yields the kernel
\[
 K(z_{ij},t_{ij})
 =\tfrac12(r_i^{-1}+r_j^{-1})|p_i-p_j|
 =\sqrt{(z_{ij}+1)(z_{ij}-t_{ij})}.
\]
Since \(\sum_{i,j}z_{ij}=(\sum_i r_i^{-1})(\sum_j r_j)\), it suffices to prove
\[
 \sum_{i,j}K(z_{ij},t_{ij})\le c_d\sum_{i,j}z_{ij}. \tag{1}
\]
The radii and directions can be arbitrarily dependent.

**A positive definite family.** Here a function \(b\) is positive definite on \(\mathbb R\) if \([b(s_i-s_j)]_{ij}\) is positive semidefinite for every finite list. For each integer \(m\ge1\),
\[
 B_m(s)=\sqrt{1+\operatorname{sech}s}\;\operatorname{sech}^{m-1}s
        =\sqrt{2}\,\frac{\cosh(s/2)}{\cosh^{m-1/2}s}
 \tag{2}
\]
is positive definite. First, for any \(c>0\), setting \(h_i=e^{2c s_i}\) gives the Gram representation
\[
 \operatorname{sech}(c(s_i-s_j))=\frac{2\sqrt{h_i h_j}}{h_i+h_j}
 =\int_0^\infty \sqrt{2h_i}e^{-h_iv}\sqrt{2h_j}e^{-h_jv}\,dv .
\]
Next the double-angle identity gives
\[
 B_1(s)=(1-\tfrac12\operatorname{sech}^2(s/2))^{-1/2}.
\]
Expand \((1-y)^{-1/2}\) in its nonnegative binomial series. Here \(0\le y\le1/2\), so the series converges at every argument, and every matrix term is positive semidefinite by the Schur product theorem (the entrywise product of two Gram matrices is again a Gram matrix, using tensor products). Passing to the limit and multiplying entrywise by \(\operatorname{sech}^{m-1}s\) proves (2). This elementary simplification was provided during internal independent review.

**Removing angular nonuniformity.** Let \(T=e\cdot U\), \(U\sim\sigma\). By the binomial series, \(\sqrt{1-y}=1-\sum_{m\ge1}a_m y^m\) where all \(a_m>0\) and \(\sum a_m=1\), so the expansion converges absolutely even at \(y=\pm1\). Consequently
\[
 K(z,t)=\sqrt{z(z+1)}-\sum_{m\ge1}a_m B_m(s)t^m,\qquad z=\cosh s.
\]
In the real Euclidean tensor power let \(v_m=\int u^{\otimes m}d\sigma(u)\). Rotational invariance gives \(\langle u^{\otimes m},v_m\rangle=\mathbb ET^m\) for every unit \(u\); integrating again gives \(\|v_m\|^2=\mathbb ET^m\). Hence \([t_{ij}^m-\mathbb ET^m]\) is a Gram matrix of the centered tensors \(u_i^{\otimes m}-v_m\). Its Schur product with \([B_m(s_i-s_j)]\) is positive semidefinite, so its sum of entries is nonnegative. Applying this termwise (there are only finitely many pairs) yields
\[
  \sum_{i,j} K(z_{ij},t_{ij})\le \sum_{i,j}\mathbb E K(z_{ij},T). \tag{3}
\]
This is a statement about the total weighted energy, not a pointwise comparison.

**The radial inequality.** With \(x=1/z\in(0,1]\) write
\[
 \mathbb E K(z,T)/z=F_d(x):=\mathbb E\sqrt{(1+x)(1-xT)}.
\]
The geometric mean is jointly concave on nonnegative arguments; composing it with two affine functions and averaging shows \(F_d\) is concave. For \(d\ge3\), its left derivative at 1 equals
\[
 F_d'(1-)=\frac{1}{2\sqrt 2}\mathbb E\frac{1-3T}{\sqrt{1-T}}\ \ge 0. \tag{4}
\]
Indeed \(T\) has density proportional to \((1-t^2)^{(d-3)/2}\) on \((-1,1)\). Differentiation under the integral as \(x\uparrow1\) follows by domination by a constant times \(1+(1-t)^{-1/2}\), integrable for \(d\ge3\). Under reweighting by \((1-T)^{-1/2}\), \((1-T)/2\) has beta parameters \((d-2)/2,(d-1)/2\); the reweighted mean of \(T\) is therefore \(1/(2d-3)\). This gives (4), including zero for \(d=3\). Concavity now gives \(F_d(x)\le F_d(1)=c_d\). Together with (3) this proves (1).

**Sharpness.** The spherical lower bound is classical. For completeness, take distinct empirical point sets on the unit sphere whose empirical laws converge weakly to \(\sigma\) (for instance almost any sequence of independent uniform samples). Their normalized distance sums converge uniformly in the chosen center on the sphere to \(c_d\): convergence on a finite epsilon-net follows by weak convergence, and all potentials are 1-Lipschitz. Thus \(S(P)/N\to c_d\), while \(W(P)/N\le1\) by choosing the origin. For \(d=3\), \(T\) is uniform on \([-1,1]\), so \(c_3=\tfrac12\int_{-1}^1\sqrt{2-2t}\,dt=4/3\). ∎

**Planar limitation.** The derivative in (4) has a nonintegrable negative singularity in dimension two. Neither the theorem nor its proof asserts the corresponding planar upper bound \(4/\pi\).
