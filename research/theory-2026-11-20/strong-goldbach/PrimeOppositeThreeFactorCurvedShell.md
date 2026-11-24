# Removing three simultaneous near-cube-root factors on a genuine rough prime cloud

Research note, 2026-11-24. This uses Guo's discrepancy for curved convex bodies on the **literal** fixed-target three-factor shell. The normalization for anisotropic factor scales is performed by an exact union of shifted cubic lattices, not by an unproved uniform extension of Guo to arbitrary stretches.

**Theorem.** Fix \(77/158<\rho\le1/2\), \(0<\alpha<\beta<1\), and \(0<\mu<\rho/4\). Put \(H=N^\rho\), \(L=\log N\), \(z=N^\mu\) for an even \(N\), and \(F_N(z)=\prod_{3\le\ell\le z,\ \ell\mid N}(\ell-1)/(\ell-2)\) over primes. There is a fixed \(\delta>0\) such that for every sufficiently large even \(N\), at least \(c F_N(z) H/L^2\) actual unit primes \(p\in(\alpha H,\beta H]\) have \(z\)-rough, squarefree complements \(N-p\) with **at most two prime factors exceeding \(N^{1/3-\delta}\)**, counting multiplicity. The same chosen rows may simultaneously satisfy the preceding near-square-root exclusion (at most one prime factor \(>N^{1/2-\delta}\)), by decreasing the fixed \(\delta\). For \(\rho=1/2\), one may also simultaneously retain the prior exclusion on the two residual factors after a prescribed-range divisor \(q\le N^\kappa\), for fixed \(\mu<\kappa<1/4\).

There is no result here saying the survivors are prime or semiprime. At a purported no-pair target this yields genuine composite factor rows none of whose rank-three factorizations have all factors in the stated angular range around the cube root.

## 1. Reduction to the thin balanced-rank-three shell

The previous fixed-\(N\) lower linear sieve supplies a rough prime-opposite cloud of size \(\ge c_0 F_N(z)H/L^2\), with real \(p\) prime, \(p\in(\alpha H,\beta H]\) and \((p,N)=1\). Its assumptions are unchanged (ordinary Bombieri–Vinogradov on scale \(H\), and a fixed sieve exponent \(s>2\) available from \(\mu<\rho/4\)). [The previous integer square-divisor argument](PrimeOppositeSquarefreeThirdFactor.md) deletes \(O(H/z+N^{1/3}+H/N^{1/3})=o(H/L^2)\), hence the complement may be made squarefree. These deletions are independent of the present upper sieve.

Take \(\delta>0\) with \(3\delta<\mu\). If a rough complement has three factors \(q,r,s>N^{1/3-\delta}\) counted with multiplicity, the remaining integer cofactor is \(<N^{3\delta}<z\), so roughness forces it to be 1. Thus \(qrs=N-p\). All three factors are in \((N^{1/3-\delta},N^{1/3+2\delta}]\). Divide the factor ranges into dyadic boxes \(q\in[Q_1,2Q_1)\), \(r\in[Q_2,2Q_2)\), \(s\in[Q_3,2Q_3)\), with all \(Q_i\) powers of two. Each \(Q_i\ge N^{1/3-\delta}/2\). For boxes that contain a true triple,
\[
 (N-\beta H)/8 < Q_1 Q_2 Q_3 < N.
\]
The first two powers \(Q_1,Q_2\) have \(O(1+\delta L)\) possibilities each, and the product bound leaves \(O(1)\) possibilities for the third given the first two. Thus there are at most \(C(1+\delta L)^2\) boxes, with absolute \(C\). Empty boxes outside the product range are irrelevant.

## 2. A fixed smooth curved convex body that contains the patch exactly

In normalized coordinates take \(f(x,y,w)=1/(xy)-w\) for \(x,y>0\), and \(g(x,y,w)=x^2+y^2+w^2-M^2\) with a sufficiently large fixed \(M\) (for example 100). Let \(\phi\) be the convolution of the absolute value with an even nonnegative smooth compactly supported probability kernel on \([-1,1]\). Then \(\phi\) is smooth and convex, \(\phi\ge|\cdot|\), agrees with \(|\cdot|\) outside \([-1,1]\), and \(|\phi'|\le1\). Define
\[
 F=\tfrac12(f+g+\phi(f-g)),\qquad
 \mathcal B=\{x,y>0,\ F(x,y,w)\le0\}.
\]
The identity for the Hessian is
\[
 D^2 F=\tfrac{1+\phi'(f-g)}2 D^2 f+
       \tfrac{1-\phi'(f-g)}2 D^2 g+
       \tfrac{\phi''(f-g)}2\,(\nabla f-\nabla g)(\nabla f-\nabla g)^T .
\]
The \(xy\) Hessian block of \(f\) has diagonals \(2/(x^3y),2/(xy^3)\), off-diagonal \(1/(x^2y^2)\), and determinant \(3/(x^4y^4)>0\); its \(w\) row/column vanish. The Hessian of \(g\) is \(2I\). Hence \(F\) is convex. Because \(F\ge\max(f,g)\), its nonpositive sublevel lies in the radius-\(M\) ball and has \(w\ge1/(xy)>0\). This places it uniformly away from \(x=0,y=0,w=0\) (e.g. \(x,y,w\ge M^{-2}\)), so it is compact. The fixed point \(a=(2,2,2)\) is interior: \(f(a)<0\), and \(g(a)\) is very negative so \(F(a)=f(a)<0\).

The boundary is a smooth regular level: a vanishing gradient of a convex \(F\) would attain a global minimum at that point, not a zero level above \(F(a)\). Wherever the coefficient of \(D^2g\) is positive, \(D^2F\) is positive definite. Where that coefficient vanishes, \(\nabla F=\nabla f\), whose \(w\)-component is \(-1\). A nonzero tangent vector then cannot be purely in the \(w\) direction, and the positive \(xy\) block makes the restriction of \(D^2F\) positive definite on that tangent plane. Thus the boundary has positive Gaussian curvature everywhere. On the patch \(f=0\) with \(x,y\in[1/3,3]\), \(w=1/(xy)\le9\), the ball equation \(g\) is sufficiently negative that \(f-g>1\) and \(F=f\) in a neighborhood of that patch. This provides the exact surface \(xyw=1\).

Write \(C=N/(Q_1Q_2Q_3)\), which lies in a fixed interval \([1,9]\) for relevant boxes for large \(N\). Normalize an actual triple by
\[
 x=q/(C^{1/3}Q_1),\quad
 y=r/(C^{1/3}Q_2),\quad
 w=s/(C^{1/3}Q_3).
\]
Its normalized product is \(1-p/N<1\); the first two coordinates are in \([1/3,3]\). It is outside \(\mathcal B\) because \(F\ge f>0\), but increasing \(w\) to \(1/(xy)\) moves by exactly \(p/(Nxy)=O(H/N)\) to the matched boundary. Let \(r_*>0\) be a fixed radius with \(a+r_*\mathbb B\subset\mathcal B\), where \(\mathbb B\) is the Euclidean unit ball. Set \(\varepsilon=K H/N\) with a sufficiently large fixed \(K\), and use the nested homothetic body
\[
 \mathcal B_\varepsilon=a+(1+\varepsilon)(\mathcal B-a).
\]
Indeed \(\mathcal B +\varepsilon r_*\mathbb B\subseteq\mathcal B_\varepsilon\), since \((\mathcal B-a)+\varepsilon(\mathcal B-a)=(1+\varepsilon)(\mathcal B-a)\) by convexity. Therefore every true triple in the box belongs to the shell \(\mathcal B_\varepsilon\setminus\mathcal B\) in these coordinates. In physical coordinates this enlarged shell has real volume
\[
 \mathcal V= C Q_1Q_2Q_3\,\operatorname{vol}(\mathcal B)
                   ((1+\varepsilon)^3-1)=O(H),
\]
with absolute dependence only on the fixed construction. The upper sieve acts on the whole enlarged shell. No asymptotic for the original sharply truncated box band is required.

## 3. Guo's discrepancy uniformly for translated cubic lattices

Use [Jingwei Guo, *On lattice points in large convex bodies*, Acta Arith. 151 (2012), 83–108](https://www.impan.pl/shop/publication/transaction/download/product/81980), [full author text](https://arxiv.org/pdf/1007.4284), Theorem 1.1, dimension 3, exponent \(\vartheta=1+73/158=231/158\), for the fixed centered body \(\mathcal B-a\). The needed translation-uniform form is
\[
 \#\{(v+\mathbb Z^3)\cap t(\mathcal B-a)\}
 =t^3\operatorname{vol}(\mathcal B)+O_{\mathcal B}(t^\vartheta)
\]
uniformly in \(v\bmod\mathbb Z^3\). The article states the unshifted version; here are the exact checks in its proof for allowing all shifts.

First take the shift \(v\) modulo the integer lattice, hence bounded. Guo's smoothing comparison (4.1) is a pointwise comparison of convolutions with the indicator of a body with a fixed interior ball; summing over the shifted lattice rather than the integer lattice does not change it or the comparison constant. In the Poisson expression in §4 the nonzero dual terms acquire \(e(\pm k\cdot v)\) and the zero term is unchanged. Guo's stationary phase formula for the Fourier transform of the fixed body is unchanged, as is its absolute error. The two oscillatory phases are \(\pm tH_0(\pm k)+k\cdot(\pm v)\), where \(H_0\) is the body's support function; the dyadic frequency cutoffs, curvature amplitudes, and Section 3 partition of unity remain the same.

In the lattice-coset coordinates in §4, write \(k/M=\sum_j\delta_{\rm G}v_j x_j+b_l/M=:y(x)\), with \(\delta_{\rm G}\) Guo's fixed partition parameter (unrelated to this note's angular \(\delta\)), \(\lVert\delta_{\rm G}v_j\rVert\asymp1\), and \(T=tM\). The replacement of the phase \(F_{\rm G}(x)=H_0(y(x))\) in the first of the leading sums is
\[
 F_{\rm G}(x)\longmapsto F_{\rm G}(x)\ \pm v\cdot y(x)/t.
\]
The second leading sum has the same change with signs. On the same convex support domain (4.3), \(y(x)\) is bounded. The new zero and first derivatives differ by \(O(1/t)\) with uniform constants; all second and higher derivatives are identical. Thus the amplitude, support margin, and amplitude derivative conditions (2.13) are identical; (2.14), including order zero and one, has the same uniform type of bounds; precisely the higher-derivative entries and determinants in (2.15)–(2.16) are unchanged. The lattice directions and perturbation parameter chosen via Lemma 3.1 are therefore independent of the shift as well. In dimension three the application uses Theorem 2.6 with \(q=2\); its initial two Weyl A differences in Lemma 2.2 annihilate the affine addition exactly, so the subsequent Poisson stationary phases and Hessian conditions do not even receive an error. Small and large frequency terms treated absolutely are independent of the unit phase. All comparisons and the \(t\) and smoothing-scale summation in §4 consequently retain the same exponent and constants for \(v\) arbitrary. This checks the translated form without assuming a uniform theorem for N-dependent body shapes.

## 4. Residue counts in the physical shell with uneven sizes

Let \(Q_{\min}=\min_i Q_i\). In any physical residue class \((q,r,s)\bmod d\), the normalization in section 2 gives steps \(d/(C^{1/3}Q_i)\) in the three coordinates. Since all \(Q_i\) are dyadic powers, \(Q_i/Q_{\min}\) is an integer. Each one-dimensional residue progression is a disjoint union of \(Q_i/Q_{\min}\) progressions of the coarsest spacing \(d/(C^{1/3}Q_{\min})\); their product is exactly
\[
 J_0=Q_1Q_2Q_3/Q_{\min}^3
\]
shifted copies of an isotropic cubic lattice. Apply the translated Guo estimate in each copy to the nested bodies \(\mathcal B\) and \(\mathcal B_\varepsilon\), both centered at the same \(a\). In the coordinates centered at \(a\) the two dilation parameters are \(t=C^{1/3}Q_{\min}/d\) and \(t(1+\varepsilon)\), while their physical cubic grid shift is the same (uniformity permits either). Subtract the counts in the two closed bodies to count precisely the enlarged shell. The total main term in each original residue class is exactly \(\mathcal V/d^3\) by the identity \(J_0t^3=CQ_1Q_2Q_3/d^3\). The error is
\[
 O(J_0t^\vartheta)=O(N Q_{\min}^{\vartheta-3}d^{-\vartheta})
    =O\bigl(N^{77/158+(3-\vartheta)\delta} d^{-\vartheta}\bigr).
\]
Use \(Q_{\min}\ge N^{1/3-\delta}/2\) and \(CQ_1Q_2Q_3=N\); \(C\) and the factor from \(1+\varepsilon\) are uniformly bounded. In the sieve \(d\le D=N^\lambda\) with fixed small \(\lambda\), so \(t\to\infty\). This step uses only the fixed geometric shape, its translations, isotropic dilations, and an exact integer lattice partition.

## 5. The four-prime sieve and the final deletion

On these enlarged-shell lattice points sieve the integer polynomial \(qrs(N-qrs)\). Every actual prime quadruple \(q,r,s,p=N-qrs\) from the original box has all four entries greater than the small sieve bound for large \(N\), and hence contributes 1 to the unsifted divisor-square upper bound. Extra lattice points of the enlarged shell may have \(N-qrs\le0\); they do not hurt because all divisor-square weights are nonnegative (even for value 0). We only need an upper count of actual quadruples.

For a prime \(\ell\), the coordinate planes \(qrs=0\) give \(\ell^3-(\ell-1)^3\) forbidden triples. If \(\ell\nmid N\), the additional nonzero solutions of \(qrs=N\) have cardinality \((\ell-1)^2\); if \(\ell\mid N\) there is no addition. Thus with \(g(\ell)\) the resulting forbidden density, for odd \(\ell\) we have
\[
 1-g(\ell)=
 \begin{cases}
  (1-1/\ell)^2(1-2/\ell),&\ell\nmid N,\\
  (1-1/\ell)^3,&\ell\mid N .
 \end{cases}
\]
At 2 it is \(1/8\), as \(N\) is even. The ratio at each odd \(\ell\mid N\) is \((\ell-1)/(\ell-2)\), exactly the factor \(F_N\) in the true rough lower sieve. The local root count is \(\le4\ell^2\); for squarefree \(l\) the CRT root count is at most \(4^{\omega(l)}l^2\). Also \((1-g(\ell))^{-1}\le8\).

Use the explicit standard Selberg divisor-square weights from [the two-factor thin-band proof](PrimeOppositeFixedAngleExclusion.md), now with this \(g\) and \(Z=N^{\lambda/2}\). The same diagonalization gives the main coefficient \(1/G(Z)\), and \(\lvert\lambda_d\rvert\le8^{\omega(d)}\). Its \(G\)-lower truncation argument works identically with \(g(\ell)\le4/\ell\): choose fixed \(y=Z^\nu\le z\) with \(\nu>0\) sufficiently small so that the weighted mean \(\sum_{\ell\le y}g(\ell)\log\ell\) is at most \(\log Z/2\), and keep the lower half of the Euler product in \(G\). The result is
\[
 1/G(Z)\ll \prod_{\ell\le y}(1-g(\ell))
          \ll F_N(y)/(\log y)^4 \ll F_N(z)/L^4 .
\]
The product bounds are by Mertens (the local product for odd \(\ell\nmid N\) differs from \((1-1/\ell)^4\) by an absolutely convergent correction). No extra target-radical factor appears.

For the total remainder, group the pair of Selberg divisors by lcm \(l\le D=Z^2\); there are at most \(3^{\omega(l)}\) pairs per \(l\), and both weights are bounded by fixed constants to the power \(\omega(l)\). Multiply the per-residue error of section 4 by the CRT root count and sum. Dropping its favorable \(l^{-\vartheta}\) factor gives the simpler adequate bound
\[
 O\left(N^{77/158+(3-\vartheta)\delta}
                     \sum_{l\le D} l^2 C_3^{\omega(l)}\right)
   =O(N^{77/158+(3-\vartheta)\delta}D^{3+o(1)}).
\]
First fix \(\delta_0,\lambda>0\) such that
\[
 77/158+(3-\vartheta)\delta_0+3\lambda<\rho.
\]
This is possible precisely with the slack assumed in the theorem; for \(\rho=1/2\), both \(\delta_0=\lambda=1/1000\) suffice for this inequality. Also fix the upper cutoffs small enough that all three factors and \(p\) exceed \(Z\), and fix \(\nu\) and the other sieve parameters independently of the final \(\delta\le\delta_0\). The error per box is then \(O(N^{\rho-\eta_0})\) for some fixed \(\eta_0>0\). Its main coefficient \(\mathcal V/G\) is \(O(HF_N(z)/L^4)\).

Sum over \(O((1+\delta L)^2)\) boxes. Every bad true rough source supplies a counted prime triple, and overcounting only helps the upper bound. The cost is
\[
 O(\delta^2 HF_N(z)/L^2)+o(HF_N(z)/L^2)
\]
for each fixed \(0<\delta\le\min(\delta_0,\mu/3)\), with the first implied constant independent of the final \(\delta\). The earlier near-square-root deletion costs \(O(\delta HF_N(z)/L^2)+o(\cdot)\), and the earlier low-first-factor rank-three deletion, if also imposed in its parameter range, has the same \(O(\delta)\) cost. Choose \(\delta\) small enough against \(c_0\) to pay all desired deletions and the integer squareful removal simultaneously. Thus the selected prime-source rows are actual, rough, squarefree, and satisfy the claimed angular restrictions.

This resolves the earlier proposed \(N^{1/2}\) Type III discrepancy obstacle for the near-balanced range, by curved-shell geometry rather than a speculative dual frequency calculation. It does not exclude every rank-three shape or imply a high successor exists. The exponent of the smallest prime in a remaining rank-three complement can lie substantially below \(1/3-\delta\); the low-first-factor result only additionally controls the balance of its other two factors when that smallest factor is below its stated quarter-power cutoff. No conclusion about an actual Goldbach representation is made.

A focused comparison with literature on almost primes in short intervals did not locate this same fixed-center, prime-filtered exclusion; no priority claim is made.
