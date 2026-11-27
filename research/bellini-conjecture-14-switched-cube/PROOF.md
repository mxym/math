# Subspaces and zero-space projections for the switched cube family

Let \(m\ge5\) be odd, \(q=2^m\), \(K=\mathbb F_q\), \(E=\mathbb F_{q^2}\), and \(C=(E^\times)^3\). Let \(\operatorname{tr}\) and \(\operatorname{tr}_K\) denote the absolute traces from \(E,K\) respectively; use \(\langle x,y\rangle=\operatorname{tr}(xy)\) for orthogonality in \(E\). Fix \(a\in E^\times\), define
\[
 F_a(x)=x^3+a^{-1}\operatorname{tr}(a^3x^9),
\]
and let \(N_a\) be the set of nonzero components \(b\in E\) for which \(x\mapsto \operatorname{tr}(bF_a(x))\) is not bent. The spread lines in question are \(cK\) for \(c\in E^\times\), each an \(m\)-dimensional \(\mathbb F_2\)-space.

**Theorem.** Every \(\mathbb F_2\)-subspace of \(N_a\cup\{0\}\) has dimension at most \(m\). Those of dimension \(m\) are exactly
\[
       cK\quad\text{with}\quad c/a\in\mathbb F_4^\times,\quad c\in C .
\]
No such line is the second-coordinate projection of a Walsh-zero space of \(F_a\). Consequently \(F_a\) is not CCZ-equivalent to a permutation. This proves Bellini's [Conjecture 14](https://arxiv.org/html/2611.10269v1#S7) in its stated range. If \(3\nmid m\), the displayed list has one line for every \(a\); it is \(aK\) exactly when \(a\in C\). If \(3\mid m\), the list is three lines when \(a\in C\) and empty otherwise. Neither the Big APN Problem nor the general triplicate-family permutation problem is addressed.

## 1. Common spread and trace facts

Since \(m\) is odd, \(3\nmid(q-1)\), and \(K^\times\subset C\). The norm-one cubic label \(\chi(z)=z^{(q^2-1)/3}\) on \(E^\times\) takes the three values of \(\mathbb F_4^\times\). Each cubic coset has \((q+1)/3\) spread directions, because each direction contains \(q-1\) nonzero points and has constant label. An affine \(K\)-line not passing through zero has no two different points in the same spread direction: if \(z_1,z_2\) were distinct points on both that affine line and a direction through 0, the two affine lines would coincide. An affine \(K\)-line of direction \(L\) therefore hits exactly one point in each of the \(q\) spread directions other than \(L\). Its intersection with a fixed cubic coset has size \((q+1)/3\) or \((q-2)/3\), according as \(L\) is outside or inside that coset. Also, \(K^\perp=K\), by nondegeneracy and \(\operatorname{tr}(K)=0\), so \((cK)^\perp=c^{-1}K\).

## 2. Rigidity at dimensions \(m\) and \(m-1\) in a cubic coset

**Lemma 1.** If \(V\) has \(\mathbb F_2\)-dimension \(d\in\{m-1,m\}\) and all its nonzero elements belong to a single cubic coset of \(E^\times\), then \(V\subseteq cK\) for some \(c\ne0\).

### A Frobenius-stable exterior product

Write \(m=2k+1\), and fix a binary basis \(v_1,\ldots,v_d\) of \(V\). Set \(f_i=(v_1^{2^i},\ldots,v_d^{2^i})\in E^d\). The first \(d\) vectors \(f_0,\ldots,f_{d-1}\) form an \(E\)-basis: any dependence would give a nonzero linearized polynomial of degree at most \(2^{d-1}\) vanishing at all \(2^d\) points of \(V\). For \(e=(q+1)/3=1+2+2^3+\cdots+2^{2k-1}\), we have \((x^e)^q=\xi x^e\) for all \(x\in V\), where \(\xi\) is the constant cubic label (the equality also holds at zero). Express \(x\) in its binary coordinates in the basis and expand \(x^e=\prod_{i\in I}x^{2^i}\) with \(I=\{0,1,3,\ldots,2k-1\}\). In the unique multilinear polynomial on the binary coordinates, the highest-degree coefficients are precisely the coordinates of \(\bigwedge_{i\in I}f_i\). Indeed only distinct chosen coordinates produce degree \(|I|\), and the coefficient sums over permutations are determinants in characteristic two. The wedge is nonzero by independence, and its \(q\)-power is \(\xi\) times itself. Its wedge annihilator is its span
\[
        U=\langle f_0,f_1,f_3,\ldots,f_{2k-1}\rangle_E .
\]
Thus \(U\) is stable under entrywise \(q\)-Frobenius. In particular \(f_m=f_0^q\) and \(f_{m+1}=f_1^q\) belong to \(U\).

### Dimension \(m\)

Write \(f_m=\sum_{i\in I}A_i f_i\). Squaring gives \(f_{m+1}\). The terms from odd \(i\in I\) fall on distinct even-index basis vectors \(f_2,f_4,\ldots,f_{2k}\), all outside \(U\), while \(f_0^2=f_1\) is inside. Hence all \(A_i\) for odd \(i\) vanish. Then \(x^q=A_0x\) for every \(x\in V\); dividing by one nonzero solution shows \(V\) lies in a \(K\)-line.

### Dimension \(m-1\), with vanishing top coefficient

Here \(d=2k\). Write
\[
    f_{2k}=\sum_{i=0}^{2k-1}\ell_i f_i,\qquad \ell_0\ne0.
\]
The relation is the normalized subspace polynomial on \(V\); if \(\ell_0=0\), taking square roots gives a nonzero linearized polynomial of degree \(2^{d-1}\) vanishing on \(V\), impossible. Suppose \(\ell_{2k-1}=0\). Squaring once, \(f_m\in U\) forces \(\ell_i=0\) at every remaining odd index. Squaring again gives \(f_{m+1}=\sum_{j}\ell_{2j}^{4} f_{2j+2}\). Replacing \(f_{2k}\) by its even-index expansion, all coordinates of \(f_{m+1}\) are even-index. The intersection of that span and \(U\) is the line spanned by \(f_0\); therefore \(x^{2^{m+1}}=\eta x\) throughout \(V\) for some nonzero \(\eta\). Ratios of nonzero solutions belong to the fixed field \(\mathbb F_{2^{\gcd(m+1,2m)}}=\mathbb F_4\). That would give binary dimension at most two, contradicting \(d=m-1\ge4\).

### Dimension \(m-1\), with nonzero top coefficient

Scale \(V\) to make \(\ell_{2k-1}=1\): scaling by \(s\ne0\) multiplies this coefficient by \(s^{2^{2k-1}}\), a bijective power. The hypothesis stays true up to changing its cubic coset. For \(1\le j\le k-1\), \(f_m\in U\) kills the even coordinate \(2j\), giving \(\ell_{2j}=\ell_{2j-1}^2\). In the expansion of \(f_m\) its odd coefficient \(A_{2j-1}\) is \(\ell_{2j-2}^2+\ell_{2j-1}\), and \(A_{2k-1}=1+\ell_{2k-2}^2\). The even coordinate \(2j\) in \(f_{m+1}\in U\) is \(A_{2j-1}^2+A_{2k-1}^2\ell_{2j}=0\). Taking square roots and putting \(\lambda=\ell_{2k-2}\) yields
\[
    \ell_{2j-2}^2=\lambda^2\ell_{2j-1},
    \qquad \ell_{2j}=\lambda^{-4}\ell_{2j-2}^4 .
\]
In particular \(\lambda\ne0\) by the \(j=1\) equation and \(\ell_0\ne0\).

Set \(A(X)=\sum_{j=0}^{k-1}\ell_{2j}X^{4^j}\). The subspace polynomial is \(X^{4^k}+A(X)+\lambda^{-2}A(X)^2\), including its top odd coefficient \(1\). The last recurrence gives the polynomial identity
\[
    A(X)^4=\lambda^4\big(A(X)+\ell_0X+X^{4^k}\big)
\]
because the highest coefficient of \(A\) is \(\lambda\). For \(x\in V\) put \(u=A(x)/\lambda\). Substituting the vanishing of the subspace polynomial gives
\[
    x^{4^k}=\lambda u+u^2,\qquad
    \ell_0x=u^4+u^2,\qquad
    (u^q)^2+u^q=\gamma(u^2+\lambda u),\quad
    \gamma=\ell_0^{4^k}\ne0.
\]
The first two come by substitution; the last is the second raised to \(4^k\), using the first and \(2\cdot 4^k=q\). Distinct \(x\)'s produce distinct \(u\)'s by the second identity.

If \(\lambda=1\), put \(v=u^2+u\); then \(v^q=\gamma v\) and \(x=v^2/\ell_0\). The \(v\)'s are in a single \(K\)-line since ratios of nonzero solutions are in \(K\); their squares divided by \(\ell_0\) are again in a \(K\)-line. If \(\lambda\ne1\), conjugate the last identity by \(q\) and eliminate \((u^q)^2\). Because \(\gamma^q(1+\lambda^q)\ne0\), this writes \(u^q=A_2u^2+A_1u\) with coefficients independent of \(u\). Substitution into the same identity yields
\[
   A_2^2u^4+(A_1^2+A_2+\gamma)u^2+(A_1+\gamma\lambda)u=0.
\]
This has \(q/2\ge16\) distinct roots, so all coefficients vanish. In particular \(A_2=0\), \(\gamma=\lambda^{-2}\) and \(A_1=\lambda^{-1}\). The \(u\)'s therefore lie in a line \(\zeta K\) with \(\zeta\notin K\), since \(u^q=\lambda^{-1}u\) and \(\lambda\ne1\). Writing \(u=\zeta t\),
\[
    x=(\zeta^2/\ell_0)t^2(1+\zeta^2t^2).
\]
For nonzero \(t\in K\) its squared factor \(t^2\) has cubic label 1. Since \(\zeta^2\notin K\), the points \(1+\zeta^2t^2\) lie on an affine \(K\)-line not through zero. The \(q/2-1\) such points that arise would all have a single cubic label, while §1 gives at most \((q+1)/3\) such points. This is impossible already at \(q=32\), and for all larger \(q\), since \(q/2-1>(q+1)/3\) for \(q>8\). This proves Lemma 1.

## 3. Maximal component subspaces are exactly the claimed lines

Let \(H(z)=z+\operatorname{tr}(z^3)\). Since \(\operatorname{tr}(z^2+z+1)=0\) in the even extension \(E\), \(H(z+1)=H(z)+1\) and \(H^2(z)=z\). Direct substitution gives
\[
    F_a(x)=a^{-1}H(ax^3),\qquad
    a\,\operatorname{Im}F_a=H(aC\cup\{0\}).
\]
Thus the map has one preimage above 0 and exactly three above each other image element. The family is quadratic APN by the [Budaghyan–Carlet–Leander construction](https://doi.org/10.1016/j.ffa.2008.10.001); alternatively it follows from Theorem 1 of [Triplicate functions](https://doi.org/10.1007/s12095-022-00587-2) because the displayed map is quadratic and 3-to-1, with the canonical triples \(\mathbb F_4^\times x\).

**Lemma 2.** Every binary subspace \(B\subseteq N_a\cup\{0\}\) has dimension at most \(m\); for any \(m\)-dimensional \(B\), the same inclusion holds if and only if \(B^\perp\subseteq\operatorname{Im}F_a\).

Use the known Gold-like signed spectrum at first coordinate zero: \(W_{F_a}(0,0)=q^2\), \(W_{F_a}(0,b)=2q\) for \(b\in N_a\), and \(W_{F_a}(0,b)=-q\) for other \(b\ne0\). These values are [Triplicate functions](https://doi.org/10.1007/s12095-022-00587-2), Theorem 2 and Corollary 12, applied with odd \(m\). The double sum below is the same starting identity as in their Theorem 7 for even \(m\). If \(r=|B|\) and \(B\subseteq N_a\cup\{0\}\), character orthogonality gives
\[
  q^2+(r-1)2q
    =\sum_{b\in B}W_{F_a}(0,b)
    =r\,|\{x:F_a(x)\in B^\perp\}|
    \le r\,(3q^2/r-2).
\]
In the last step \(B^\perp\) has \(q^2/r\) points, one of which is 0, and every nonzero value is hit at most three times. Rearranging yields \(r\le q\), with equality if and only if every nonzero point of \(B^\perp\) is hit. Conversely, for \(r=q\) and \(B^\perp\subseteq\operatorname{Im}F_a\), the sum reaches \(q^2+(q-1)2q\). Since \(2q\) is the maximum possible term at each nonzero \(b\), all such \(b\) belong to \(N_a\). This proves Lemma 2.

Now assume \(B\subseteq N_a\cup\{0\}\) has dimension \(m\), and let \(H_a=\{b:\operatorname{tr}(b/a)=0\}\), \(V=B\cap H_a\). Each nonzero component in \(V\) is the Gold cube component \(x\mapsto\operatorname{tr}(bx^3)\). Its polar operator has a nonzero root \(u\) if and only if \(bu^3=1\), by squaring the equation \(bu^2+(bu)^{1/2}=0\). Equivalently that component is non-bent if and only if \(b\in C\). Thus \(V\setminus\{0\}\subset C\). If \(\dim V=m\), Lemma 1 already proves \(B=V=cK\). Otherwise \(\dim V=m-1\) and \(V\subset cK\) for some \(c\in C\) by Lemma 1.

Put \(L=(a/c)K=\lambda K\) and \(D=aB^\perp\). Lemma 2 implies \(H(D)\subset aC\cup\{0\}\). We have \(D\subset aV^\perp\), and \(1\notin D\) because \(B\not\subseteq H_a\). The latter ambient space contains \(L\) and \(1\).

* If \(1\in L\), then \(L=K\) and \(D\ne L\). Both \(D,L\) are \(m\)-spaces in the \((m+1)\)-space \(aV^\perp\). Hence \(D\) meets an affine coset of \(K\) outside \(K\) in \(q/2\) points. The bijection \(H\) preserves each affine \(K\)-coset because it adds 0 or 1. The corresponding \(q/2\) distinct points of \(H(D)\) cannot fit into \(aC\) on that affine line by §1 and \(q/2>(q+1)/3\). Thus this branch is impossible.
* If \(1\notin L\), then \(aV^\perp=L\oplus\langle1\rangle_{\mathbb F_2}\). The \(m\)-space \(D\) omits 1, so it is a graph \(\{\lambda t+\ell(t):t\in K\}\) for some binary linear functional \(\ell\). By \(H(z+1)=H(z)+1\), its switched set is
  \[
      H(D)=\{\lambda t+h(t)+\ell(t):t\in K\},\qquad
      h(t)=\operatorname{tr}_K\big((\lambda^3+(\lambda^3)^q)t^3\big).
  \]
  All nonzero points of \(L\) already belong to \(aC\), since \(\lambda=a/c\) and \(c\in C\). For \(t\ne0\), a nonzero toggle \(h(t)+\ell(t)=1\) can land in \(aC\) at only \((q-2)/3\) places: \(\lambda t+1\in aC\) iff \(t+\lambda^{-1}\in C\), and that affine line has cubic direction \(K\). The toggle is zero at \(t=0\). If \(h\ne0\), it is a nonzero odd-dimensional Gold quadratic of rank \(m-1\). For clarity, for its nonzero coefficient \(\delta=\lambda^3+(\lambda^3)^q\), the polar root equation over \(K\) is \(\delta u^3=1\) for \(u\ne0\); cubing is bijective on \(K\), so the radical has one nonzero point. Thus \(|W_{h+\ell}(0)|\le2^{(m+1)/2}\) and its weight is at least \(q/2-\sqrt{q/2}>(q-2)/3\). The strict inequality holds even at \(q=32\) (12>10), and follows in general from \((q+4)^2-18q=(q-2)(q-8)>0\). This contradicts the possible toggle positions. Consequently \(h=0\); a nonzero \(\ell\) would have weight \(q/2\), so \(\ell=0\). Thus \(D=L\), \(B=cK\).

We have proved every \(m\)-dimensional component space is a spread line. To classify all spread lines, first note that \(cK\subseteq N_a\cup\{0\}\) implies \(c\in C\): its intersection with \(H_a\) has dimension at least \(m-1\) and the Gold test applies there. For any \(c\in C\), Lemma 2 says \(cK\) is a component space iff \(H(\lambda K)\subset aC\cup\{0\}\) for \(\lambda=a/c\). If \(\lambda\in K\), \(H\) fixes the line. If \(\lambda\notin K\), the same toggle counting with \(\ell=0\) shows \(H(\lambda K)\subset aC\cup\{0\}\) iff \(h=0\). Indeed a nonzero \(h\) is balanced (cubing on \(K\) is bijective), so it cannot toggle at only \((q-2)/3\) places; the converse is immediate. Hence the necessary and sufficient condition is \(\lambda^3\in K\). This holds iff \(\lambda\in\mathbb F_4^\times K^\times\): choose the unique cube root of \(\lambda^3\) in \(K\) and divide by it. Allowing a change of representative \(c\) within its \(K\)-line, this is the stated list.

Finally \(\mathbb F_4^\times\) maps bijectively to the three cubic classes if \(3\nmid m\), and lies inside \(C\) if \(3\mid m\). This follows from \(9\mid(4^m-1)\) iff \(3\mid m\). The multiplicities and the criterion for the line \(aK\) now follow.

## 4. No line lifts: an alternating-minor obstruction

Fix an allowed \(B=cK\) with \(c/a\in\mathbb F_4^\times\) and \(c\in C\). Scale inputs by \(\beta\) with \(\beta^3=c^{-1}\) and reparametrize the components \(b=ct\) by \(t\in K\). The components in these coordinates are
\[
   Q_t(x)=\operatorname{tr}\big(t x^3+s(t)x^9\big),
   \qquad s(t)=\operatorname{tr}((c/a)t)\in\mathbb F_2 .
\]
The Walsh-zero projection property is preserved by such invertible reparametrizations in the input and component spaces. Let \(\alpha\in\mathbb F_4\setminus\mathbb F_2\), and denote the binary polar form of \(Q_t\) by \(D_t(x,y)\). Since \(Q_t\) vanishes on \(K\), \(D_t\) is zero on \(K\times K\). On \(K\), define \(A_t(x,y)=D_t(x,\alpha y)\). Expanding and using the relative traces of \(\alpha\) and \(\alpha^2\), both 1, gives
\[
   A_t(x,y)=\operatorname{tr}_K\big(t(x^2y+xy^2)+s(t)(x^8y+xy^8)\big).
\]
This is alternating and linear in \(t\). Because \(m\) is odd, every \(A_t\) is singular (alternating forms have even rank). For \(t\ne0\), a nonzero vector \(u\in\ker A_t\) lies in the radical \(R_t\) of \(D_t\) over \(E=K+\alpha K\), by vanishing against both summands. Since \(Q_t(\alpha x)=Q_t(x)\), \(R_t\) contains \(\mathbb F_4 u\). For each such non-bent component the signed Walsh spectrum used in Lemma 2 has nonzero amplitude \(2q\), so its radical has binary dimension two. This is the usual quadratic polar-rank rule \(2^{(2m+\dim R_t)/2}\), obtained by squaring the signed Walsh sum and summing over the polar differences. Therefore \(R_t=\mathbb F_4 u\), and \(A_t\) has precisely one nonzero radical vector \(u_t\in K\). Moreover \(Q_t\) vanishes on \(R_t\) by its \(\mathbb F_4^\times\) symmetry and its vanishing on \(K\), so its Walsh support is exactly \(R_t^\perp\). Orthogonality outside that subspace follows by translating along the radical; inside it the same Walsh-square rule gives a nonzero amplitude.

Different \(t\ne0\) cannot have the same \(u_t\): for a quadratic APN map the linear polar derivative at a nonzero input direction has a kernel of size two, hence an image of binary codimension one and a unique nonzero annihilating component. There are \(q-1\) such \(t\)'s and \(q-1\) nonzero vectors in \(K\), so the \(u_t\)'s run through \(K^\times\) exactly once. The \(q-1\) lines \(\mathbb F_4 u_t\) are distinct because \(\mathbb F_4\cap K=\mathbb F_2\).

Apply [Bellini, Theorem 8](https://arxiv.org/html/2611.10269v1#S6) (part 3): a Walsh-zero space projecting onto \(B\) requires an \(m\)-dimensional \(P\subset E\) and a binary bilinear \(\Psi\) on \(B\times P\) such that for each \(t\ne0\) there exists \(y\in P\cap R_t\) with \(\Psi(t,y)=1\). The right side is 1 because the respective support is the unshifted space \(R_t^\perp\). The condition can also be read directly from projecting a linear \(2m\)-dimensional zero space: its fiber above \(t\) is an affine translate of \(P^\perp\), and disjointness from \(R_t^\perp\) is tested on \(P\cap R_t\).

Such \(P\) must meet all \(q-1\) distinct radical lines, so uses exactly one nonzero point from each. In particular \(P\) lies in the union of \(K,\alpha K,\alpha^2 K\). If points \(\mu x,\nu y\) of \(P\) come from different such lines with \(x,y\in K^\times\), their sum must lie on the third line \((\mu+\nu)K\), requiring \(x=y\) by \(K\)-linear independence of \(\mu,\nu\). If \(P\) meets two lines, each intersected line can therefore contribute at most one nonzero point, including the third one if met. This contradicts \(q-1>3\). Thus \(P=\lambda K\) for some \(\lambda\in\mathbb F_4^\times\). The required condition is then
\[
       \Psi(t,\lambda u_t)=1\quad(t\in K^\times).
\]

To rule this out, express \(A_t\) as an \(m\times m\) alternating matrix in a binary basis of \(K\). Its rank is \(m-1\) for \(t\ne0\), so the symmetric adjugate is \(u_tu_t^{\mathsf T}\): it is nonzero, each row and column belongs to the one-dimensional kernel, and the only nonzero binary scalar is \(1\). Each coordinate of \(u_t\) equals the corresponding diagonal minor, since its square is itself over \(\mathbb F_2\). The determinant of an even alternating matrix is the square of its Pfaffian: in characteristic two the determinant permutation terms with cycles of length at least three cancel in reversal pairs, diagonal terms vanish, and the remaining products are squares of the matching monomials. Evaluating over \(\mathbb F_2\), the square does not change values. Each coordinate of \(u_t\), with \(u_0=0\), therefore has Boolean degree at most \((m-1)/2\) in \(t\), because each matching covers \(m-1\) indices in \((m-1)/2\) pairs and the matrix entries are linear in \(t\).

The function \(t\mapsto\Psi(t,\lambda u_t)\) has degree at most \((m+1)/2<m\), so its parity sum over \(K\) is zero: every coordinate monomial of degree less than \(m\) assumes 1 an even number of times. Requiring the function to take 1 on all \(q-1\) nonzero points and 0 at the origin gives parity one. This contradiction proves the no-lift assertion.

By [Bellini, Proposition 7](https://arxiv.org/html/2611.10269v1#S6), two complementary Walsh-zero spaces would have projections spanning \(E\), each in \(N_a\cup\{0\}\). Both dimensions are at most \(m\), so both would have dimension \(m\). Neither can exist by the no-lift proof. This completes Conjecture 14. The older even-\(m\) result and the small even dimensions outside the stated range are as cited by Bellini's Corollary 12; they are not part of the new argument.
