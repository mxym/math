# A non-Gold crooked function with a fourth-order sum-free ortho-derivative

## Statement and scope

Let \(K=\mathbb F_2[t]/(t^6+t+1)\) and \(a=t\), and use the trace pairing. The known switched-cube map
\[
 F(x)=x^3+a^{-1}\operatorname{Tr}(a^3 x^9)
\]
is not CCZ-equivalent (in particular not EA-equivalent) to any Gold APN map in dimension six. Its exclude parity adjoint is the explicit polynomial
\[
 \varepsilon_F(x)=x^3+(\mathtt{0x1e})\,x^9+(\mathtt{0x2c})\,x^{18},
\]
where the hex coefficients are polynomial-basis elements, least significant bit first. Both maps are quadratic APN. Its ortho-derivative is fourth-order sum-free: the sum over **every** affine four-flat is nonzero. This provides a non-Gold example in the direction of Open Problem 5.10 of [Carlet–Thornburgh](https://arxiv.org/html/2608.23888v2). The literal problem already has Gold examples from their Theorem 5.9 and Gold Proposition 5.17. The claim here is an explicit non-Gold example, not priority over Gold, a new APN class, or a self-adjoint example.

## 1. The field and the ortho-derivative

Arithmetic uses coefficients in ascending degree. The element \(a\) satisfies \(a^{63}=1\), \(a^{21}\ne1\), and \(a^9\ne1\) in the indicated quotient ring. Therefore its multiplicative order is 63, and its 63 powers exhaust the nonzero residues of the quotient. This certifies that the quotient is a field. One verifier checks the powers by modular multiplication, and the other builds the table of all powers using the linear feedback formula; neither needs a field database.

An APN map has every nonzero derivative \(F(x+y)+F(y)\), as a function of \(y\), exactly two-to-one on its image. For a quadratic \(F\), this is equivalent to \(\ker\beta_F(x,-)=\{0,x\}\) for each \(x\ne0\), where \(\beta_F(x,y)=F(x)+F(y)+F(x+y)+F(0)\). In this case the derivative images are affine hyperplanes (crookedness). The ortho-derivative \(\pi_F(x)\) is the unique nonzero trace normal to \(\operatorname{im}\beta_F(x,-)\) for \(x\ne0\), with \(\pi_F(0)=0\).

To prove APN directly for the field example, fix \(x\ne0\) and put \(y=xw,\ z=w+w^2,\ d=a^{-1}x^{-3}\), and \(s=d^{-3}\). The terms of \(F\) have Boolean degree at most two, and
\[
 x^{-3}\beta_F(x,xw)=z+d\operatorname{Tr}\big(s(z+z^2+z^4)\big)
\]
because \(z+z^2+z^4=w+w^8\). The \(z\)'s range over the trace-zero hyperplane. A nonzero \(z\) in the kernel must equal \(d\) and have trace zero. Yet
\[
 \operatorname{Tr}\big(s(d+d^2+d^4)\big)
 =\operatorname{Tr}(d^{-2}+d^{-1}+d)=\operatorname{Tr}(d).
\]
So \(z=d\ne0\) cannot vanish in that formula. This leaves only \(z=0\), equivalently \(w=0\) or \(1\), proving APN.

Put \(c=s+s^{2^4}+s^{2^5}\). The trace term in this formula is \(\operatorname{Tr}(cz)\), and \(\operatorname{Tr}(cd)=\operatorname{Tr}(d)\). When the trace of \(d\) is zero, \(1\) annihilates the displayed normalized image; when it is one, \(c\ne0\) annihilates that image. Rescaling back gives
\[
 \pi_F(x)=x^{-3}\big(1+\operatorname{Tr}(d)(1+c)\big),\qquad x\ne0 .
\]

## 2. Extracting the adjoint polynomial

Let \(m_u(v)\) count two-dimensional linear subspaces \(L\subset u^\perp\) whose \(F\)-sum is \(v\). The defining equation is \(\operatorname{Tr}(v\varepsilon_F(u))=1+m_u(v)\pmod2\) for \(v,u\ne0\), with \(\varepsilon_F(0)=0\) (Definition 5.1). The cited Proposition 4.2 and Theorem 5.9 give \(\deg\pi_F\le4\), \(\deg\varepsilon_F\le2\), and
\[
 \beta_{\varepsilon_F}(u,v)=\sum_{x\in\langle u,v\rangle^\perp}\pi_F(x)
\]
for independent \(u,v\). The identity extends to dependent \(u,v\) as well: the left side vanishes and the right side is a sum over a space of dimension at least five, so vanishes by the degree bound.

For any \(K\)-valued function its unique univariate representative with exponents \(0,\ldots,63\) is of Boolean degree at most \(k\) exactly when all present exponents have binary weight at most \(k\). In one direction \(x^j\) is a product of the Frobenius maps at the one-bits of \(j\). For the other direction these linearly independent monomials, taken for \(\operatorname{wt}_2(j)\le k\), are as numerous as the multilinear Boolean monomials of degree at most \(k\), and hence span the same \(K\)-space.

Write \(\pi_F(x)=\sum_r p_r x^r\). Multiplying \(\pi_F(x)\) by
\((1+\operatorname{Tr}(ux))(1+\operatorname{Tr}(vx))\) and summing over \(K\) computes the stated polar sum. The constant and linear trace terms contribute zero: after expanding the traces, no nonzero polynomial exponent is a multiple of 63, by the binary weight bound and \(\pi_F(0)=0\). In the product of trace terms the contributions from equal Frobenius indices also vanish, since \(2^i+2^i\bmod63\) is a single bit. The remaining terms use \(\sum_{x\in K} x^m=1\) when \(m>0\) is a multiple of 63 and \(0\) otherwise. Thus the coefficient of \(x^{2^i+2^j}\) in the **quadratic** part of \(\varepsilon_F(x)\) is
\[
 p_{63-2^i-2^j}\qquad(0\le i<j<6).
\]
This follows by obtaining the same polarization on all \(u,v\), which fixes the quadratic part.

There is no additive part in this example. For the nontrivial cube root of unity \(\omega=a^{21}\), the equality \(F(\omega x)=F(x)\) gives \(m_{\omega u}(v)=m_u(v)\), by applying \(\omega^{-1}\) to the input planes. Hence \(\varepsilon_F(\omega u)=\varepsilon_F(u)\). None of the linearized exponents \(1,2,4,8,16,32\) is divisible by three, so its coefficient must vanish by uniqueness of univariate representation. The constant is also zero.

To reproduce the small symbolic computation of the coefficients, expand
\[
 \pi_F(x)=x^{-3}+\sum_{i=0}^{5} a^{-2^i}x^{-3-3\cdot2^i}
 \left(1+\sum_{r\in\{0,4,5\}} a^{3\cdot2^r}x^{9\cdot2^r}\right)
 \quad(x\ne0).
\]
Each term is tracked modulo 63 in the multiplicative group. The following are exactly the retained pairs \((j,e)\): a term \(a^e x^{-j}\) whose \(j\bmod63\) has binary weight two.

| \(i\) | retained pairs \((j,e)\) |
|---:|:---|
| initial term | \((3,0)\) |
| 0 | \((6,62),(33,32)\) |
| 1 | \((9,61),(36,31)\) |
| 2 | \((6,62)\) |
| 3 | \((18,58),(9,40)\) |
| 4 | \((33,32)\) |
| 5 | \((36,31),(18,16)\) |

After cancellation the coefficients for \(3,9,18\) are \(1,a^{61}+a^{40},a^{58}+a^{16}\), evaluating to \(1,30,44\) in this basis. This derives the polynomial, and both programs also reconstruct the full adjoint directly without using this derivation (from the parity definition and from Walsh differences, respectively).

## 3. Exact finite certificates and non-Gold separation

For \(F\) and its reconstructed adjoint, [verify.py](verify.py) checks all 63 nonzero derivative rows, including their maximum multiplicity. Because pairs \(y,y+x\) always give equal derivatives, maximum multiplicity \(2\) gives APN. [verify_independent.py](verify_independent.py) independently checks quadraticity and rank five of each of the 63 polar maps of each function. For the ortho-derivative, the first verifier enumerates the 651 dual two-spaces by pairs of smallest nonzero representatives. The four possible trace fibers for each pair give the four affine four-flats, hence all \(651\cdot4=2604\). The second enumerates four-dimensional row-reduced echelon bases and shifts them by the four representatives supported in the nonpivot coordinates. Every sum in both enumerations is nonzero. This also follows abstractly from Theorem 5.9 once the adjoint is APN, but the direct verification does not rely on that implication.

For non-Gold separation let \(G_F=\{(x,F(x)):x\in V\}\subset V\times V\). The graph-translation code is the binary span of the incidence vectors of all \(G_F+z\), \(z\in V\times V\). Its dimension is the standard \(\Gamma\)-rank. An affine bijection \(T(w)=Mw+b\) carrying \(G_F\) to \(G_G\) sends \(G_F+z\) exactly to \(G_G+Mz\). Therefore it permutes the coordinate points and sends the entire spanning family to that of \(G_G\), so its rank is a CCZ invariant. An EA change \(G(x)=A_2(F(A_1(x)))+A_3(x)\), with \(A_1,A_2\) affine bijections and \(A_3\) affine, is realized on graphs by
\[
 (x,y)\longmapsto\big(A_1^{-1}(x),\,A_2(y)+A_3(A_1^{-1}(x))\big).
\]
This is an affine bijection, so the rank also applies directly to EA classes.

In dimension six the Gold exponents reduce to \(2^1+1=3\) and \(2^5+1=33\), because \(\gcd(i,6)=1\). They are linearly equivalent by the output Frobenius \(y\mapsto y^{32}\) since \(3\cdot32\equiv33\pmod{63}\). Hence comparing with the cube covers every Gold APN class here. The rank of the cube is 1102 and that of our switched cube is 1146. The first verifier obtains these by eliminating the incidence vectors of all 4096 translated graphs.

The independent program uses the group algebra. In the basis \(X^z\) the graph incidence polynomial is \(P=\sum_x X^{(x,F(x))}\) and the translation code is the ideal generated by \(P\). For the 12 bit generators \(X_i\) one has \(X_i^2=1\). Use \(Y_i=1+X_i\), so \(Y_i^2=0\) and the monomials \(Y^z\) form a basis by the inverse substitution \(X_i=1+Y_i\). Thus the ideal dimension is the rank of the elements \(Y^zP\), computed after a superset parity transform and only retaining disjoint supports in multiplication. This uses different vector representations and elimination pivots, and produces the same ranks.

## 4. Optional dimension-six classification cross-check

As a second representation, the scripts build the quadratic with coefficients in lexicographic pair order \(x_i x_j,\,0\le i<j<6\),
\[
 (1,2,4,8,16,\ 4,6,16,24,\ 8,5,37,\ 32,5,\ 3),
\]
using the standard bit dot product. This is the second row (one-based) of the authors' [QAPN-6-6 catalogue](https://doi.org/10.5281/zenodo.22010376). Both programs certify the same APN, adjoint APN, fourth-order sum-free, and rank properties for this representative. The optional downloaded-table comparison checks all 64 entries in this row.

Using the cited catalogue's completeness in dimension six, the optional check also gives the exact EA-class count there. Under EA change with linear parts \(L_1,L_2\) as above one has \(\pi_G=(L_2^{-1})^*\pi_F L_1\), because translating derivative images does not change their underlying normal hyperplanes. Thus permuting inputs by \(L_1\) and outputs by \((L_2^{-1})^*\) preserves fourth-order sum-freeness. The optional verifier checks the count of zero sums on all 651 **linear** four-spaces for all 13 rows. Only rows 2 and 3 have zero such spaces; they pass the affine case because \(\deg\pi_F\le4\) and the sum over a four-flat equals a fourth derivative, independent of its basepoint. The ranks of these two classes are 1146 and 1102; the catalogue has only one row of each rank, so they are the switched-cube class and the Gold class respectively. This classification statement is restricted to dimension six and depends on the cited catalogue; the primary explicit non-Gold example does not.
