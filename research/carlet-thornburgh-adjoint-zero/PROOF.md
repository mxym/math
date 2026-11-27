# A zero of the exclude parity adjoint and the near-bent degree correction

This note uses the definitions of Carlet and Thornburgh, [arXiv:2608.23888v2](https://arxiv.org/html/2608.23888v2). The example below is a counterexample to the statement of Proposition 6.4, not just to its argument.

## 1. Definitions and the universal nonvanishing counterexample

Write \(V=\mathbb F_2^n\), with a fixed nondegenerate symmetric pairing \(\langle\ ,\ \rangle\). It is the trace pairing in §1.1 and the bit dot product in §1.2. For quadratic \(F:V\to V\), define the alternating bilinear map
\[
\beta(x,y)=F(0)+F(x)+F(y)+F(x+y).
\]
APN (almost perfect nonlinear) means that for each nonzero \(x\), the derivative \(y\mapsto F(x+y)+F(y)\) has fibers of size \(0\) or \(2\). Equivalently, \(\ker\beta(x,-)=\{0,x\}\). In particular a quadratic APN is crooked.

For \(u\ne0\) let \(H=u^\perp\), and for \(v\ne0\) let \(m_u(v)\) count the two-dimensional linear subspaces \(L\le H\) with \(\sum_{x\in L}F(x)=v\). For any basis \(x,y\) of \(L\), this sum is \(\beta(x,y)\). Write \(f_v(u)=m_u(v)\bmod2\). The cited Definition 5.1 and Theorem 5.5 give
\[
\langle v,\varepsilon_F(u)\rangle=1+f_v(u)\quad(u,v\ne0),\qquad
\varepsilon_F(0)=0.
\]
The \(+\) on the right is in \(\mathbb F_2\). In particular, for fixed \(u\ne0\), \(\varepsilon_F(u)=0\) precisely when **every** \(m_u(v)\) for \(v\ne0\) is odd.

**Theorem 1.** There are quadratic APN maps with \(\varepsilon_F(u)=0\) at nonzero \(u\), in both even and odd dimensions. The examples below have dimensions 10 and 7, respectively. In either example the set of nonzero \(v\) with even \(m_u(v)\) is empty at the specified \(u\).

### 1.1 Dimension ten: a self-generated field example

Use \(K=\mathbb F_2[t]/(t^{10}+t^3+1)\), \(a=t\), \(u=1\), and \(\langle x,y\rangle=\operatorname{Tr}(xy)\), with the absolute field trace. Let
\[
F(x)=x^3+a^{-1}\operatorname{Tr}(a^3x^9).
\]
Field elements are encoded by their integer coefficient bits, low degree first. The class of \(t\) satisfies \(t^{1023}=1\); its three powers with exponents \(1023/3,1023/11,1023/31\) have encodings \(237,713,620\), respectively. Hence it has order 1023 in the quotient ring's unit group. There are exactly 1023 nonzero residue classes, so all are units and the quotient is a field. The second verifier also tests irreducibility by the Frobenius/gcd criterion.

The map has degree at most two because \(3=2+1\), \(9=8+1\), and trace is linear. It is APN by a direct argument. Fix \(x\ne0\), put \(y=xw\), \(z=w^2+w\), \(d=a^{-1}x^{-3}\), and \(s=a^3x^9=d^{-3}\). Using \(z+z^2+z^4=w+w^8\), one gets
\[
x^{-3}\beta(x,xw)=z+d\operatorname{Tr}\bigl(s(z+z^2+z^4)\bigr).
\]
As \(w\) varies, \(z\) ranges over the trace-zero hyperplane: the image of \(w\mapsto w^2+w\) is contained in it and both sets have 512 elements. A nonzero \(z\) in the kernel of the displayed map would have to be \(d\), hence \(\operatorname{Tr}(d)=0\). But
\[
\operatorname{Tr}\bigl(s(d+d^2+d^4)\bigr)
 =\operatorname{Tr}(d^{-2}+d^{-1}+d)=\operatorname{Tr}(d),
\]
so \(z=d\ne0\) cannot vanish under the displayed map. Thus \(\ker\beta(x,-)=\{0,x\}\), as required. In particular \(F\) is not affine.

The certificate in [verify.py](verify.py) computes \(F\), checks all derivative counts and counts planes of \(H=\ker\operatorname{Tr}\). It visits \(x<y\) among nonzero points of \(H\) and keeps the pair iff \(x+y>y\) in the integer encoding. Every plane has three nonzero points and exactly one kept pair: its two smallest points. The plane multiplicities, with 1023 targets and \(43435=511\cdot510/6\) planes, are:

| \(m\) | 29 | 31 | 33 | 35 | 37 | 39 | 41 | 43 | 45 | 47 | 49 | 51 | 53 | 55 | 57 |
|-----:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| number of nonzero \(v\) with \(m_1(v)=m\) | 1 | 5 | 17 | 37 | 101 | 129 | 208 | 174 | 136 | 95 | 66 | 37 | 13 | 3 | 1 |

No plane has value zero. The table gives \(\varepsilon_F(1)=0\) from the definition. As a negative control, \(u=2\) in the same encoding has 511 odd and 512 even multiplicities at nonzero \(v\).

The independent [verify_independent.py](verify_independent.py) uses a different multiplication routine and does not count planes. It constructs the ortho-derivative normal
\[
\pi_F(x)=x^{-3}
\begin{cases}
1,&\operatorname{Tr}(d)=0,\\
s+s^{2^9}+s^{2^8},&\operatorname{Tr}(d)=1
\end{cases}
\quad(x\ne0),\qquad \pi_F(0)=0.
\]
In fact, writing \(c=s+s^{2^9}+s^{2^8}\), one has \(\operatorname{Tr}(s(z+z^2+z^4))=\operatorname{Tr}(cz)\) and \(\operatorname{Tr}(cd)=\operatorname{Tr}(d)\). A normal to the image of \(z\mapsto z+d\operatorname{Tr}(cz)\) on the trace-zero hyperplane is \(1\) when \(\operatorname{Tr}(d)=0\); when the trace is one, \(c\ne0\) is a normal since \(\operatorname{Tr}(cz)+\operatorname{Tr}(cd)\operatorname{Tr}(cz)=0\). Multiplication of the image by \(x^3\) then divides its trace normal by \(x^3\). The program independently checks the formula against all basis polarizations and ranks. It computes the adjoint using the identity from the proof of the cited Lemma 5.2:
\[
\langle v,\varepsilon_F(u)\rangle\equiv
 \frac{W_{v\cdot\pi_F}(u)-W_{v\cdot\pi_F}(0)}{8}\pmod2 .
\]
Here \(v\cdot\pi_F\) is its paired scalar component; evaluating the identity at a basis of output covectors suffices. The independent zero set, in decimal encodings, is
\[
\{0,1,118,166,211,226,236,237,270,290,388,492,516,612,626,695\}.
\]

### 1.2 Dimension seven: a smaller counterexample

Use the standard bit basis, the dot product, and the following ANF with no constant or linear terms. Each row lists the hex coefficient vectors of \(x_i x_j\) for \(j=i+1,\ldots,6\), encoded as seven-bit integers.

~~~text
i=0: 01 02 04 08 10 40
i=1:    04 06 10 18 2c
i=2:       08 20 40 35
i=3:          40 61 45
i=4:             2a 6e
i=5:                6f
~~~

This is from row 4 (one-based) of the [QAPN-7-7 authors' dataset](https://doi.org/10.5281/zenodo.22010376). The verifier reconstructs it from the printed coefficients without a download, and can optionally compare all 128 outputs to the original data. See [SOURCES.md](SOURCES.md) for attribution and checksums.

The direct verifier checks the APN definition for all 127 directions, enumerates 651 planes for each \(u\ne0\), and obtains the complete adjoint zero set \(\{0,77,111\}\) (decimal). For \(u=77\), for example, the multiplicities for the 127 nonzero \(v\) are \(3,5,7,9\), at respectively \(24,75,24,4\) targets. The independent verifier computes rank-six derivatives, takes the unique nonzero dot-product normal, and uses the Walsh-difference identity to reproduce the zero set. It also checks that the degree-three coefficient vectors of the inverse ortho-derivative span all seven output coordinates. Thus this seven-dimensional example does **not** refute Open Problem 5.7 about inverse-component degrees.

### 1.3 Which implication fails

The statements in the cited preprint's introduction and §5 that the parity-even set is always an affine hyperplane for a quadratic APN fail, and the inference given after Theorem 5.5 is invalid. The fact that a fixed nonzero \(u\) has \(f_v(u)=1\) for all nonzero \(v\) does not imply that some nonzero \(v\) has \(f_v\) identically one. Corollary 4.9's component-degree result for \(\pi_F\), combined with the preceding equivalence of degrees in the preprint, rules out identically one \(f_v\) for each fixed \(v\ne0\), not an input at which they all equal one. The existence and quadraticity of \(\varepsilon_F\) are not contradicted.

## 2. Exact replacement for the top-degree assertion in Proposition 6.4

**Theorem 2.** Let \(n\ge4\) be even, \(F\) quadratic APN, \(u\ne0\), \(H=u^\perp\), and \(g_u(b)\) the indicator that the component \(x\mapsto\langle b,F(x)\rangle\) on \(H\) is near-bent. Then
\[
\operatorname{wt}(g_u)\equiv2\pmod4,\qquad
\sum_{b\in V}g_u(b)b=\varepsilon_F(u)\quad\text{in }V.
\]
Consequently \(\deg g_u\le n-1\), with equality if and only if \(\varepsilon_F(u)\ne0\). In §1.1 with \(u=1\), the degree is exactly \(8\), not \(n-1=9\) as in the cited Proposition 6.4.

*Proof.* For \(b\in V\), let \(r_b\) be the rank of the scalar alternating form \((x,y)\mapsto\langle b,\beta(x,y)\rangle\) on \(H\). A quadratic form in \(h\) variables of polar rank \(r\) has Walsh amplitude \(2^{h-r/2}\): squaring a Walsh coefficient and putting \(y=x+a\) makes the inner sum over \(x\) zero off the radical and \(2^h\) times a sign on the radical. On the radical the phase, including the Walsh character, is linear after subtracting the value at zero; thus each squared coefficient is \(0\) or \(2^{2h-r}\). At least one is nonzero by Parseval. In \(h=n-1\) odd variables, near-bent means amplitude \(2^{n/2}\), equivalently \(r_b=n-2\). All other possible \(r_b\) are at most \(n-4\) because alternating ranks are even.

Define the integer Fourier transform \(\widehat g_u(v)=\sum_b(-1)^{\langle v,b\rangle}g_u(b)\). For each \(b\), the sum over \(x,y\in H\) of \((-1)^{\langle b,\beta(x,y)\rangle}\) is \(2^{2n-2-r_b}\) by summing first in \(y\) and counting the radical. Fourier orthogonality on \(V\) gives, for every \(v\),
\[
\begin{aligned}
\sum_b(-1)^{\langle v,b\rangle}2^{n-2-r_b}
&=2^{-n}\sum_b\sum_{x,y\in H}(-1)^{\langle b,\beta(x,y)+v\rangle}\\
&=\#\{(x,y)\in H^2:\beta(x,y)=v\}.
\end{aligned}
\]
The left hand side is \(\widehat g_u(v)\) modulo four: the multiplier \(2^{n-2-r_b}\) is one for rank \(n-2\), a multiple of four otherwise. At \(v=0\), the right hand side counts \(|H|\) pairs with \(x=0\), and two choices \(y=0,x\) for each of the \(|H|-1\) nonzero \(x\), by APN. Thus \(\widehat g_u(0)\equiv 3\cdot2^{n-1}-2\equiv2\pmod4\). At \(v\ne0\), a qualifying pair is an ordered basis of a two-plane with value \(v\), and each such plane has six ordered bases. Therefore \(\widehat g_u(v)\equiv6m_u(v)\equiv2m_u(v)\pmod4\). It follows that
\[
\sum_{\langle b,v\rangle=1}g_u(b)
=\frac{\widehat g_u(0)-\widehat g_u(v)}{2}
\equiv1+m_u(v)=\langle v,\varepsilon_F(u)\rangle\pmod2 .
\]
Nondegeneracy of the pairing proves the vector identity.

The weight of a Boolean function modulo two is its top ANF coefficient, so the even weight gives \(\deg g_u\le n-1\). Its degree-\((n-1)\) coefficients are the parities on coordinate hyperplanes \(b_j=0\), the same as on \(b_j=1\) since the total weight is even. The latter take the values of \(\langle v,\varepsilon_F(u)\rangle\) at the corresponding coordinate covectors \(v\). Hence a degree-\((n-1)\) coefficient occurs exactly when \(\varepsilon_F(u)\ne0\).

For §1.1 at \(u=1\), the first verifier evaluates all component Walsh spectra on \(H\): 938 masks are near-bent, and the transformed ANF has degree \(8\). The independent verifier gets the same indicator from ranks: one rank-zero mask, 85 rank-six masks, and 938 rank-eight masks. All coordinate hyperplane weights are even, while the coordinate 8-flat with the two highest bits zero has indicator weight 233, odd. Thus the lower bound \(8\) does not depend on the Möbius-transform implementation. The \(u=2\) negative control in [verify.py](verify.py) gives degree \(9\) and nonzero adjoint, as predicted.

## 3. A localized repair of the Gold proof

The disputed implication is used in the last step of Gold Proposition 5.17 in v2 (Proposition 5.12 in v1). The result need not be withdrawn. For \(F(x)=x^{2^i+1}\) with \(\gcd(i,n)=1\), let \(d=2^i+1\). The simultaneous changes \(L\mapsto aL\), \(v\mapsto a^dv\) in plane counts give \(\varepsilon_F(x)=c x^d\); squaring all points and using trace invariance gives \(c^2=c\). These are the valid symmetry steps in the cited proof. The remaining possibility \(c=0\) makes \(\varepsilon_F\) **identically** zero, so each \(f_v\) with \(v\ne0\) equals one at every nonzero \(u\) by Definition 5.1. It also equals one at \(u=0\) by the cited Proposition 2.1 on the full graph multiplicity. Thus each such \(f_v\) would be identically one. This does contradict the component-degree result and the degree equivalence already proved for quadratic APN. Hence \(c=1\); no universal nonvanishing assertion is needed.
