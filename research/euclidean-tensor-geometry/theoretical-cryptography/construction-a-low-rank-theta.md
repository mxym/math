# Centered theta-ratio minima for binary codes with a low-rank orthogonal deviation

## Result and scope

Let \(C=\{(x,Ax):x\in\mathbb F_2^k\}\) be a binary self-dual code in systematic coordinates, so \(A^\mathsf TA=I\). Let \(L_C=2^{-1/2}\{z\in\mathbb Z^{2k}:z\bmod2\in C\}\), and define
\[
R(y)=\Theta_{L_C}(y)/\Theta_{\mathbb Z^{2k}}(y),\qquad
\Theta_L(y)=\sum_{v\in L} e^{-\pi y\|v\|^2}.
\]
The Belfiore–Solé question is whether \(R\) is minimized at \(y=1\); this note proves it in either of the following regimes, for a given systematic representation:
* \(\operatorname{rank}_{\mathbb F_2}(A-I)\le3\);
* for \(W=\operatorname{im}(A-I)\), every nonzero \(a\in W\) has \(\dim\{v\in W:\operatorname{supp}v\subseteq\operatorname{supp}a\}\le2\).

In these regimes the minimum is unique unless \(A\) is a permutation, in which case \(R\equiv1\). The second regime allows unbounded rank. It includes the case in which all distinct nonzero vectors in \(W\) have intersecting supports. The result only concerns the indicated lattice theta ratios in abstract mathematics, not channel security or a concrete cryptographic construction. The unrestricted conjecture is not proved.

## 1. An exact low-dimensional signed formula

Put \(E=\sum_{j\ \mathrm{even}} e^{-\pi y j^2/2}\), \(O=\sum_{j\ \mathrm{odd}} e^{-\pi y j^2/2}\), and \((\cos\theta,\sin\theta)=(E,O)/\sqrt{E^2+O^2}\). Since \(E>O>0\), \(0<\theta<\pi/4\). The identity \(\Theta_{\mathbb Z}(y)^2=E^2+O^2\) follows by sending a pair of integers \((u,v)\) to \((u+v,u-v)\), whose entries have equal parity. Entrywise reduction modulo two therefore gives
\[
R(y)=\sum_{x\in\mathbb F_2^k}
(\cos\theta)^{2k-|x|-|Ax|}(\sin\theta)^{|x|+|Ax|}.
\tag{1}
\]
Here \(|x|\) denotes Hamming weight. At \(y=1\) the two parity sums obey \((E,O)=2^{-1/2}(E+O,E-O)\) by one-dimensional Poisson summation, giving \(O/E=\sqrt2-1\) and \(\theta=\pi/8\). This occurs only there: \((E-O)/(E+O)\) is \(\vartheta_4(0,q)/\vartheta_3(0,q)\) with \(q=e^{-\pi y/2}\), strictly increasing with \(y\) by the Jacobi products, whose ratio is \(\prod_{j\ge1}[(1-q^{2j-1})/(1+q^{2j-1})]^2\). In particular \(E>O\) as used above. Write \(p=\cos^2(2\theta)\) and \(q'=1-p=\sin^2(2\theta)\); the distinguished point is \(p=q'=1/2\).

All words in \(W\) have even weight, since over \(\mathbb F_2\) self-dot-product is Hamming parity and \(A\) preserves it. Put \(T=A-I\) and \(r=\dim W\). Since \(T^\mathsf T=A^{-1}T\) in characteristic two and \(A\) preserves the image of \(T\), \(\operatorname{im}T^\mathsf T=W=(\ker T)^\perp\). For \(v,w\in W\) define \(\beta(v,w)=v\cdot x_w\), where \(T x_w=w\), independent of the chosen preimage. This is a bilinear form. Orthogonality shows
\[
\beta(v,w)+\beta(w,v)=v\cdot w
\tag{2}
\]
by expanding the dot product of \(x_w+w\) and \(x_v+v\).

Fix the change \(w=Tx\) in (1). On the flipped coordinates the multiplicative factor is \(\cos\theta\sin\theta\) and makes the corresponding \(x\) bits uniform; on the unflipped coordinates the factors give independent bits of bias \(\sin^2\theta\). To enforce \(Tx=w\), use the affine-subspace Fourier indicator
\[
\mathbf 1_{Tx=w}=2^{-r}\sum_{v\in W}(-1)^{v\cdot(x-x_w)} .
\]
The expectation of the character is zero unless \(v,w\) have disjoint supports, since a single flipped coordinate in the character is unbiased. Otherwise it is \((\cos2\theta)^{|v|}\), and the total prefactor for uniformly drawn flipped bits is \((\sin2\theta)^{|w|}\). Thus
\[
2^r R(y)=\sum_{\substack{v,w\in W\\ v\cap w=\varnothing}}
(-1)^{\beta(v,w)}p^{|v|/2}(q')^{|w|/2}.
\tag{3}
\]
In (3), disjointness makes \(\beta(v,w)=\beta(w,v)\) by (2). The number of terms is governed by the deviation space \(W\), not the ambient length.

Group (3) by \(a=v+w\). Defining \(W_a=\{v\in W:\operatorname{supp}v\subseteq\operatorname{supp}a\}\), write
\[
F_a=\sum_{v\in W_a}(-1)^{\beta(v,a+v)}p^{|v|/2}(q')^{(|a|-|v|)/2},
\qquad 2^r R(y)=\sum_{a\in W}F_a .
\tag{4}
\]
In particular \(F_0=1\). The sign exponent on \(W_a\) is a quadratic function \(v\mapsto\beta(v,a)+\beta(v,v)\), with polar form the restriction of the dot product by (2). It descends to \(W_a/\langle a\rangle\), since all words there have even weight and are supported in \(a\), so \(a\) pairs trivially with them and the quadratic function is zero at \(a\).

## 2. All shortened dimensions at most two

For nonzero \(a\) with \(\dim W_a=1\), the contribution is \(p^j+(q')^j\) with \(j=|a|/2\ge1\), minimized at \(p=q'\), constant only for \(j=1\). If \(\dim W_a=2\), there is just one proper disjoint splitting \(a=v+w\) up to swap. Put \(i=|v|/2\), \(j=|w|/2\), both positive integers. The contribution factors exactly as
\[
F_a=(p^i+\epsilon (q')^i)(p^j+\epsilon(q')^j),
\quad \epsilon=(-1)^{\beta(v,w)}.
\]
For \(\epsilon=1\) it is a product of positive functions each minimized at equality, and either constant or strictly larger off equality. For \(\epsilon=-1\) it is nonnegative by common signs of the two differences and vanishes only at equality. This proves the second regime.

For an unlimited-rank example of the intersecting case, take \(W\) to be a doubled binary simplex code: index coordinates by two copies of every nonzero column of \(\mathbb F_2^r\), and evaluate all linear forms on that list. Distinct nonzero words intersect, and doubling makes the column space orthogonal to itself. With \(G\) the \(k\times r\) matrix spanning this space as columns, take \(A=I+GG^\mathsf T\). It is orthogonal and \(A-I\) has rank \(r\), since \(G^\mathsf T G=0\) and \(G\) has full column rank. For this example (3) simply gives \(2^{-r}[1+\sum_{w\ne0}(p^{|w|/2}+(q')^{|w|/2})]\).

## 3. The remaining rank-three case

If \(r\le3\) and some \(\dim W_a=3\), then \(r=3\) and \(W_a=W\). There is at most one such nonzero \(a\), since its support is the union of all supports of \(W\). Choose \(b,c\) completing \(a\) to a basis. On the support of \(a\), partition coordinates into the four classes with a given pair \((b_i,c_i)\). Denote their lengths by \(n_1,\dots,n_4\), and put \(e_i=n_i/2\). Evenness of the three basis words forces all \(n_i\) to have the same parity. The six nonzero words other than \(a\) are the unions of two of the four cells (one for each pair). Any zero cell still leaves these words distinct, since \(a,b,c\) are independent.

Write \(P_i=p^{e_i}\), \(Q_i=(q')^{e_i}\), taking the zeroth powers as one. The three split signs in \(F_a\) are indexed by the three partitions into two pairs of cells. By the quadratic polar relation their product is \(+1\) when the lengths are even and \(-1\) when they are odd: the polar value on \(b,c\) is the parity of their common cell.

### Even cell lengths

The three signs are either all positive or exactly two negative. Choose \(\xi_i\in\{\pm1\}\), product one, so that each split sign on a pair \(ij\) is \(\xi_i\xi_j\). Such a choice follows by taking \(\xi_1=1\) and specifying the signs on its three incident pairs; complement pairs agree by product one. Then
\[
F_a=\tfrac12\left[\prod_i(Q_i+\xi_i P_i)+\prod_i(Q_i-\xi_i P_i)\right].
\]
For all positive signs choose all \(\xi_i=1\). Each \(P_i+Q_i\) is minimized at \(p=q'\) (integer \(e_i\ge0\)), and \(\prod_i(Q_i-P_i)\ge0\) since four factors have common sign. Thus \(F_a\) is minimized at equality. For exactly two negative split signs, there are two negative \(\xi_i\), so each product has exactly two difference factors and is nonnegative, vanishing at equality. A zero cell is allowed; any corresponding difference is then identically zero. In both cases, any nonconstant contribution is strictly larger off equality: positive sums with exponent at least two are strict, and a nonzero product of differences is strict off equality. The other groups in (4) all have dimension at most two and are handled by section 2.

### Odd cell lengths

All four cells now have positive odd lengths, and each union of two cells, other than the full word, has shortened dimension one. In particular the six other nonzero terms in (4) are
\[
U_{ij}=P_iP_j+Q_iQ_j=p^{e_i+e_j}+(q')^{e_i+e_j},\qquad i<j,
\]
which are in \([0,1]\) and each minimized at equality, since \(e_i+e_j\) is a positive integer.

For the full word, choose \(\xi_i\) of product one so that the split sign on \(ij\) is \(-\xi_i\xi_j\). This is possible since the product of the three split signs is \(-1\). The full contribution is \(F_a=\operatorname{Re}\prod_i(Q_i+\mathrm i\,\xi_i P_i)\).

* If all three split signs are negative, take all \(\xi_i=1\). Group cells into pairs \(12,34\). The real part is \(X_{12}X_{34}-Y_{12}Y_{34}\) with \(X_{ij}=Q_iQ_j-P_iP_j\) and \(Y_{ij}=P_iQ_j+Q_iP_j\). Both \(X\)'s have the same sign; moreover \(0\le Y_{ij}\le U_{ij}\), by \((P_i-Q_i)(P_j-Q_j)\ge0\). Therefore
  \[
  F_a+U_{12}+U_{34}\ge U_{12}+U_{34}-U_{12}U_{34}.
  \]
  The right side is nondecreasing in both variables in \([0,1]\) and equality in the displayed lower bound holds at \(p=q'\). This proves center minimality after adding the other four pair contributions.
* If one split sign is negative, take two \(\xi_i=1\), two \(-1\), with the negative partition pairing like signs. Instead group unlike signs into two pairs \(ij,kl\). Then \(F_a=U_{ij}U_{kl}-Z_{ij}Z_{kl}\), where \(Z_{ij}=\pm(P_iQ_j-Q_iP_j)\). We claim \(U_{ij}^2-Z_{ij}^2\ge U_{ij}(1/2)^2>0\). To prove it, put \(t=\tfrac12\log(p/q')\), so \(p=e^t/(2\cosh t)\), and by symmetry take \(t\ge0\). The ratio on the left to the central squared value is
  \[
  \frac{1+\sinh(n_i t)\sinh(n_j t)}{\cosh^{n_i+n_j}t}\ge1.
  \]
  Indeed \(\sinh(nt)\ge n\sinh(t)\cosh^{n-1}(t)\) for positive integers \(n\), by taking the leading odd term of \((\cosh t+\sinh t)^n\). For \(z=\cosh^2 t\ge1\) and \(h=(n_i+n_j)/2\ge1\), \(z^h-1\le h(z-1)z^{h-1}\), and \(n_i n_j\ge h\). These inequalities give the claim. Thus the reverse Cauchy inequality in the two real pairs gives \(F_a\ge\sqrt{(U_{ij}^2-Z_{ij}^2)(U_{kl}^2-Z_{kl}^2)}\ge F_a(1/2)\). The reverse inequality itself follows by squaring, with difference \((U_{ij} Z_{kl}-U_{kl} Z_{ij})^2\ge0\), and \(U_{ij}>|Z_{ij}|\), \(U_{kl}>|Z_{kl}|\).

For strictness in these odd cases, if any \(n_i>1\), one unconsumed pair term involving that cell has exponent \(>1\) and is strict; this works even in the first case which consumes only two disjoint pairs. If all \(n_i=1\), the six pairs are constant, and the full term is \(p^2+(q')^2-6pq'\) in the all-negative case, strictly minimized at equality, or \(p^2+(q')^2+2pq'=1\) in the one-negative case. This completes the first regime and the nonconstant strictness. In any regime an identically constant ratio must be one by taking \(\theta\to0\). Equation (1) is the inner product of the unit vector \(x\mapsto(\cos\theta)^{k-|x|}(\sin\theta)^{|x|}\) and its permutation by \(A\); equality at any interior \(\theta\ne\pi/4\) forces preservation of all Hamming weights by Cauchy–Schwarz. A binary linear map preserving weights sends coordinate vectors to distinct coordinate vectors and hence is a permutation. The converse is immediate.

## 4. A boundary of the formal-enumerator method

This is not a counterexample among codes. It is a counterexample to an argument using **only** nonnegative integral ordinary and shadow enumerators, with the formal MacWilliams equation. Set
\[
f=X^2+Y^2,\quad g=X^2Y^2(X^2-Y^2)^2,\quad
W_{\mathrm{formal}}=f^{12}-12 f^8 g+97 f^4g^2 .
\]
It has coefficients at \(Y^{0},Y^2,\dots,Y^{24}\) equal to
\[
(1,0,91,64,11,960,1842,960,11,64,91,0,1).
\]
Both \(f\) and \(g\) transform into \(2f,16g\) under \((X,Y)\mapsto(X+Y,X-Y)\), so the formal MacWilliams equation holds. The shadow polynomial \(2^{-12}W_{\mathrm{formal}}(X+Y,\mathrm i(X-Y))\) has nonzero coefficients \(97,380,3142,380,97\) at weights \(4,8,12,16,20\), all nonnegative integers. This substitution is the usual Type-I shadow formula, obtained by projecting onto weight divisible by four, applying MacWilliams, and subtracting the original enumerator. On the unit circle the ratio polynomial is \(1-12z+97z^2\), \(z=(\sin4\theta)^2/16\). Since the polynomial derivative at \(z=1/16\) is \(1/8>0\), the center is a strict local **maximum** of the ratio. Thus these formal constraints alone are insufficient. The polynomial cannot come from an actual self-dual length-24 code: its 91 weight-four words would give \(48+16\cdot91=1504\) roots of squared norm two in the integral Construction-A lattice, beyond the 1104 upper bound for simply-laced root systems of rank at most 24. The latter follows from the \(A,D,E\) root counts, each at most 46 times the rank for ranks at most 24.

## Sources and replay

[Belfiore and Solé](https://arxiv.org/abs/1007.0449) introduced the theta-ratio extremum. [Pinchak and Sethuraman's account of the Ernvall-Hytönen verification technique](https://www.csun.edu/~asethura/papers/ITA_2014Mod.pdf) treats particular theta polynomials. [Majorization and Gaussian-mass maximality for binary Construction A](https://arxiv.org/abs/2606.03482) establishes \(R(y)\le1\), not localization of its minimum on the positive axis. The signed deformation formula (3) and the bounded-rank argument are a different restricted approach; there is no claim of exhaustive priority.

Run **node verify-construction-a-low-rank-theta.js** for finite binary matrix fixtures, sign cases and the exact formal polynomial check. The proofs cover unbounded ambient sizes in the stated regimes, and no enumeration of codes is used in the general argument.
