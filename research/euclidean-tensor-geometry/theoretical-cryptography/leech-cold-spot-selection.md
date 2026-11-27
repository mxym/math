# The large-parameter cold spots of the Leech lattice select \(E_8^3\), not \(A_{24}\)

## Result and comparison

Use the standard Leech normalization, in which the shortest squared norm is \(4\) and the squared covering radius is \(2\). Let
\[
F_\alpha(x)=\sum_{v\in\Lambda_{24}}e^{-\alpha\|x-v\|^2}.
\]
As \(\alpha\to\infty\), every global minimizer, modulo lattice translation, approaches a deep hole of type \(E_8^3\). Every deep hole of that type has exactly one minimizing point sufficiently near it for all sufficiently large \(\alpha\). These points form one orbit under the affine isometry group, and none is itself the deep hole.

More precisely, if \(c\) is one of these holes, \(S_c=\{v-c:\|v-c\|^2=2\}\), and \(u_c\) minimizes the finite strictly convex function
\[
\Phi_c(u)=\sum_{s\in S_c}e^{2\langle u,s\rangle},
\]
then the cold spot approaching \(c\) is
\[
x_{\alpha,c}=c+\frac{u_c}{\alpha}
+\frac{2M\,(\nabla^2\Phi_c(u_c))^{-1}u_c}{\alpha^2}
+O(\alpha^{-3}),
\qquad
M=\frac{90}{(2^{26}3^{12}5^5)^{1/30}}=24.322395\ldots.
\tag{1}
\]
In particular \(u_c\ne0\), and
\[
e^{2\alpha}\min_x F_\alpha(x)
=M\left(1-\frac{\|u_c\|^2}{\alpha}\right)+O(\alpha^{-2}).
\tag{2}
\]

The end of Section 5 of [Bachoc, Moustrou, Vallentin, and Zimmermann, *Polarization of lattices: Stable cold spots and spherical designs*](https://doi.org/10.1017/fms.2026.10169) instead identifies \(A_{24}\) as the limiting type. A comparison at the fixed centers does not control this limit: a displacement of order \(1/\alpha\) changes the leading coefficient, not just a lower shell. The analysis here leaves intact their Theorem 1.4 that the Leech lattice has no stable cold spots, and gives a different proof of it. The argument uses the classical deep hole classification, not a computation of the Leech theta function away from its deep holes. No claim of priority beyond the compared sources is made.

## 1. Localize the global minimizers at scale \(1/\alpha\)

The localization argument works on any fixed full-rank Euclidean lattice \(L\), with covering radius \(R>0\). Modulo \(L\), there are finitely many deep holes: a compact Voronoi polytope has finitely many vertices and the strictly convex squared norm has no other maximizers on it. For each such \(c\), write
\[
S_c=\{v-c:v\in L,\ \|v-c\|=R\}.
\]
The origin lies in the interior of the convex hull of \(S_c\). Otherwise some unit vector \(w\) has \(\langle w,s\rangle\le0\) for all \(s\in S_c\). At \(c+\epsilon w\) their squared distances are at least \(R^2+\epsilon^2\), and for sufficiently small \(\epsilon>0\) every other lattice point remains at distance greater than \(R\) by the strict next-shell gap and the reverse triangle inequality. This contradicts the definition of \(R\).

It follows that \(\eta_c=\min_{\|w\|=1}\max_{s\in S_c}\langle w,s\rangle>0\). For small \(\delta=x-c\), select a nearest-shell vector maximizing \(\langle\delta,s\rangle\); then
\[
d(x,L)^2\le R^2-2\eta_c\|\delta\|+\|\delta\|^2
\le R^2-\eta_c\|\delta\|.
\tag{3}
\]
Take fixed, disjoint small neighborhoods of the finitely many holes on the torus; away from them, \(d(x,L)^2\le R^2-\eta\) for some \(\eta>0\) by compactness. At any fixed deep hole \(c\), \(e^{\alpha R^2}F_\alpha(c)\) is bounded for \(\alpha\ge1\), since every centered lattice distance is at least \(R\) and the sum at \(\alpha=1\) converges. On the other hand \(F_\alpha(x)\ge e^{-\alpha d(x,L)^2}\). Equation (3) now forces every global minimizer into a hole neighborhood, with \(\|x-c\|\le K/\alpha\) for an absolute \(K\) depending on the lattice but not on \(\alpha\). This is stronger than just convergence to the set of deep holes.

## 2. The finite log-sum-exp and its entropy

For bounded \(u=\alpha(x-c)\),
\[
G_{\alpha,c}(u):=e^{\alpha R^2}F_\alpha(c+u/\alpha)
=e^{-\|u\|^2/\alpha}\bigl(\Phi_c(u)+T_{\alpha,c}(u)\bigr),
\qquad
T_{\alpha,c}(u)=\sum_{\substack{s=v-c\\s\notin S_c}} e^{-\alpha(\|s\|^2-R^2)+2\langle u,s\rangle}.
\tag{4}
\]
If \(\Delta_c>0\) is the squared gap to the second shell, the tail and its first two \(u\)-derivatives are \(O_K(e^{-\alpha\Delta_c})\) uniformly on \(\|u\|\le K\). Indeed pull out the stated factor, bound the remaining radial exponential by its value at \(\alpha=1\), and use the convergent lattice Gaussian sum times the polynomial derivative factors and \(e^{2K\|s\|}\). The same reasoning works to every fixed derivative order.

The origin-interior property implies \(\Phi_c(u)\ge e^{2\eta_c\|u\|}\), and its Hessian is \(4\sum_{s\in S_c}e^{2\langle u,s\rangle}ss^\mathsf T\), positive definite because the shell spans. Therefore it has a unique minimizer \(u_c\) and a strictly positive minimum \(M_c\). Equation (4) converges to \(\Phi_c\) in \(C^2\) on any fixed compact ball. Take a ball large enough to contain all localized global minimizers and every \(u_c\) in its interior. For all sufficiently large \(\alpha\), \(G_{\alpha,c}\) is strictly convex on this ball, since the least eigenvalue of the Hessian of \(\Phi_c\) has a positive lower bound there. Its unique minimizing point on the ball is interior and converges to \(u_c\), by uniform convergence and a strict boundary gap for \(\Phi_c\). There are only finitely many hole representatives, so these claims hold simultaneously. The classes to which global minimizers can approach are therefore exactly among the classes with smallest \(M_c\); if one affine orbit has strictly smallest \(M_c\), its local minima are all equal by invariance and they are precisely the global minima.

For an interpretation that applies to general holes, let \(H(p)=-\sum_s p_s\log p_s\), with \(0\log0=0\). Then
\[
M_c=\exp\left(\max_{\substack{p_s\ge0,\ \sum_s p_s=1\\ \sum_s p_ss=0}} H(p)\right).
\tag{5}
\]
For any feasible \(p\), the log-sum-exp at \(u\) is at least \(H(p)+2\sum_s p_s\langle u,s\rangle=H(p)\), by nonnegativity of relative entropy with respect to the Gibbs weights. At the minimizing \(u_c\) the Gibbs weights have zero barycenter because the gradient vanishes, and give equality. In particular the number of nearest shell points is the correct leading constant **only** if their uniform weights have zero barycenter.

## 3. Evaluation for affine ADE shells

We use the Conway–Parker–Sloane classification of deep holes, in the equivalent form of [Borcherds, *The Leech lattice*, Corollary 7.2](https://math.berkeley.edu/~reb/papers/leech/leech.pdf). The squared covering radius is \(2\), and each deep hole class corresponds to one of the 23 rooted Niemeier lattices. The nearest vectors \(s=v-c\) have squared norm \(2\) and their Gram matrix is the orthogonal sum of the affine simply-laced Cartan matrices for the Niemeier root components; the ranks sum to \(24\). One can also read the Gram assertion directly in Borcherds's description: at the hole \(c\), the light-cone roots \((v,1,\|v\|^2/2-1)\) have mutual inner product \(2-\|v-v'\|^2/2=\langle v-c,v'-c\rangle\). In particular the affine \(E_8^3\) case exists and is one affine isometry orbit.

In one component the vectors span a rank-\(r\) space with a unique positive dependence \(\sum_i m_i s_i=0\), where \(m_i\) are the affine marks (the affine root has mark one and the remaining marks are the highest-root coefficients). Let \(h=\sum_i m_i\). The possible vectors \(t_i=2\langle u,s_i\rangle\) form exactly the hyperplane \(\sum_i m_i t_i=0\). Writing \(\gamma=h^{-1}\sum_i m_i\log m_i\), the unique constrained minimizer of \(\sum_i e^{t_i}\) satisfies \(t_i=\log m_i-\gamma\): it is feasible, and its exponential gradient is \(e^{-\gamma}m\), perpendicular to the hyperplane. Thus the component contributes
\[
\mathcal M=\frac{h}{\bigl(\prod_i m_i^{m_i}\bigr)^{1/h}}.
\tag{6}
\]
The overall \(M_c\) is the sum of (6) over the orthogonal components. The same conclusion follows from (5) by taking the entropy maximum on the component weights.

Here are the exact values supplied by (6):
\[
\begin{array}{c|c|c}
\text{type}&\text{affine marks as a multiset}&\mathcal M\\ \hline
A_r & 1^{r+1} & r+1\\
D_r & 1^4\,2^{r-3} & (r-1)\,2^{2/(r-1)}\\
E_6 & 1^3\,2^3\,3 & 12/(2^6 3^3)^{1/12}\\
E_7 & 1^2\,2^3\,3^2\,4 & 18/(2^{14}3^6)^{1/18}\\
E_8 & 1\,2^2\,3^2\,4^2\,5\,6 & 30/(2^{26}3^{12}5^5)^{1/30}.
\end{array}
\]
Multiplicities in the middle column are indicated by exponents. In particular, the first-shell coefficient after minimizing near \(A_{24}\) is \(25\). After optimizing near \(E_8^3\) it is \(3\mathcal M(E_8)=M<24.324\), although the *fixed* \(E_8^3\) center has 27 nearest points.

For a strict and exactly checkable comparison against every alternative, use
\[
6.447<\mathcal M(E_6)<6.448,\quad
7.279<\mathcal M(E_7)<7.280,\quad
8.107<\mathcal M(E_8)<8.108.
\tag{7}
\]
Each inequality follows by raising the positive quantities to the denominator exponent in (6) and comparing integers after multiplying by \(1000^h\); the accompanying verifier performs all six checks using exact integers. For \(D_r\), \(e^z>1+z\) gives \(\mathcal M(D_r)-r>2\log2-1>31/81>0.38\), using the first two positive terms of the atanh series for \(\log2\). Thus every non-\(E_8\) component has excess above its rank greater than \(0.279\); an \(A\) or \(D\) component has excess greater than \(0.38\), and an \(E_8\) component greater than \(0.107\).

Three \(E_8\)'s have total excess less than \(0.324\). With one or two \(E_8\)'s there must be another component to reach rank 24, and the excess exceeds \(0.107+0.279=0.386\). With no \(E_8\)'s and at least two components it exceeds \(0.558\); with a single rank-24 component it is type \(A\) or \(D\) and exceeds \(0.38\). This proves \(E_8^3\) is the unique minimizing type, without numerical comparisons of the Leech lattice itself. The finite-scale consequence now follows from section 2.

For \(E_8\) the marks are not all equal, so the minimizing \(t_i=\log m_i-\gamma\) cannot all vanish. This proves \(u_c\ne0\) for the selected hole. To make its length explicit, in each component label the eight nonaffine simple roots by the \(E_8\) Cartan matrix \(Q\) with diagonal 2 and entry \(-1\) exactly on edges \(13,24,34,45,56,67,78\). Their marks are \(m=(2,3,4,6,5,4,3,2)\). With \(b_i=\log m_i-\frac1{30}\log(2^{26}3^{12}5^5)\), the unique solution in that component is \(2\langle u_c,s_i\rangle=b_i\); the affine root equation follows from the dependence. The length in all three components is
\[
\|u_c\|^2=\frac34\, b^\mathsf T Q^{-1}b=2.61173899\ldots.
\]
The expression is independent of the choice of consistently labeled shell at an equivalent hole.

## 4. Expansion and the point at issue in the previous proof

Let \(u_{\alpha,c}\) be the unique minimizing coordinate from section 2 at an \(E_8^3\) hole. Differentiating (4) and factoring out \(e^{-\|u\|^2/\alpha}\) gives at the stationary point
\[
\nabla\Phi_c(u_{\alpha,c})
=\frac{2u_{\alpha,c}}{\alpha}\Phi_c(u_{\alpha,c})+
O(e^{-\alpha\Delta_c}).
\]
By the uniform positive Hessian of \(\Phi_c\) on the bounded ball, \(u_{\alpha,c}-u_c=O(\alpha^{-1})\). Taylor expansion now yields
\[
u_{\alpha,c}-u_c=
\frac{2}{\alpha}\,(\nabla^2\Phi_c(u_c))^{-1}u_c\,M+O(\alpha^{-2}).
\]
Substitution in (4) proves (1) and (2). Since a stable cold spot would have to be a fixed limiting deep hole, while every global minimum is displaced by a nonzero leading multiple of \(1/\alpha\), this recovers the absence of stable cold spots.

There are two logically separate points in interpreting the earlier Section 5. First, its Lemma 5.1 gives a polynomial prefactor for a fixed-radius lattice tail that cannot hold as stated. If \(r_0\) is itself a shell of positive multiplicity, \(e^{\alpha r_0^2}\) times that tail is bounded below by this multiplicity for all \(\alpha\); for dimension 24 the stated power of \(\alpha\) would instead make it tend to zero. More generally, if \(R_0\ge r_0\) is the first shell actually in the tail, \(a_0\) its multiplicity, and \(R_1\) the next shell, then the correct expansion is
\[
a_0 e^{-\alpha R_0^2}+O(e^{-\alpha R_1^2}).
\]
This follows by factoring out the first omitted-shell exponential and bounding the remaining Gaussian weight by a convergent fixed-parameter sum. It is enough to compare two **fixed** centers lexicographically. Second, and independently, a ranking of fixed centers does not identify limits of the minimizers. The \(E_8^3\) center has larger leading multiplicity than \(A_{24}\), but a position \(c+u_c/\alpha\) has a strictly smaller leading coefficient than any sequence approaching an \(A_{24}\) center can attain at the same localized scale.

## Reproduction

Run **node verify-leech-cold-spot-selection.js**. The verifier checks the affine mark relations using exact Cartan matrices, certifies the strict rational inequalities in (7) by integer exponentiation, and replays the finite \(E_8\) Gaussian coefficient optimization and the first two terms on generated affine-shell fixtures. The classical classification is a cited mathematical input, not enumerated by this program. The proof of localization and of the lattice tail is analytic, not a numerical extrapolation. The note makes no claim about the minimizing orbit at general finite \(\alpha\) outside the sufficiently large regime.
