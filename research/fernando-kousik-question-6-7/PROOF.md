# Complete answer to Question 6.7

For \(e\geq4\) put
\[
n=1+3\cdot 4+3\cdot 4^2+2\cdot4^3+4^e+4^{e+1},\qquad
S_j(X)=\sum_{i=0}^{j-1}X^{4^i},\qquad S_0=0.
\]
Write \(K=\mathbb F_{4^e}\), \(Q=|K|\) and \(\tau=\operatorname{Tr}_{K/\mathbb F_4}\). The polynomial \(g=g_{n,4}\) is defined by Fernando–Kousik (1.1): after substituting \(X=Y^4+Y\), its value is \(\sum_{a\in\mathbb F_4}(Y+a)^n\).

**Theorem.** The mapping induced by \(g\) on \(K\) is bijective exactly when \(e=4\).

## 1. Exact derivation and the target-field representative

Set \(U=S_2(X), V=S_3(X), E=S_e(X), F=S_{e+1}(X)\). Over an algebraic closure of \(\mathbb F_4(X)\), the four roots \(T\) of \(T^4+T=X\) are \(Y+a\), where \(Y\) is any root. For every \(j\geq0\),
\[
T^{4^j}=T+S_j(X)
\]
by induction. The base-4 digits of \(n\) therefore give
\[
g(X)=\sum_T P(T)\bigl(T^2+(E+F)T+EF\bigr),\qquad
P(T)=T(T+X)^3(T+U)^3(T+V)^2.
\]
Let \(p_j=\sum_T T^j\). Then \((p_0,p_1,p_2,p_3)=(0,0,0,1)\), since expansion in \(a\in\mathbb F_4\) gives only the third moment nonzero among degrees 0 through 3. For \(j\geq4\), \(p_j=p_{j-3}+Xp_{j-4}\). In order from \(j=0\) to \(11\), the list is \((0,0,0,1,0,0,1,X,0,1,0,X^2)\).

For transparency, if \(c_j=[T^j]P(T)\), the sets of exponents of \(X\) with coefficient 1 in each \(c_j\) are
\[
\begin{array}{c|l}
 j & \text{exponents}\\\hline
0&\varnothing\\
1&8,11,20,23,38,41,44,47\\
2&10,22,40,46\\
3&9,21,36,45\\
4&8,20,44\\
5&7,16,34,37,40\\
6&6,36\\
7&5,32\\
8&4\\
9&0
\end{array}
\]
by multiplication of the four short factors defining \(P\). Thus \(\sum_j c_j p_j=D\), \(\sum_j c_jp_{j+1}=A\), and \(\sum_j c_jp_{j+2}=V^2+XA\), where
\[
D=1+X^9+X^{21}+X^{33}+X^{45},\qquad
A=X^4+X^{10}+X^{16}+X^{22}+X^{34}+X^{46}.
\]
This proves the formal identity
\[
g(X)=V^2+EF D+(X^{4^e}+X)A. \tag{1}
\]

For comparison, denote the printed right-hand side of Question 6.7 by \(\widetilde g\). Its coefficient of \(EF\) is
\[
1+(1+X^3)U^3+V^2\big((1+X^3)U+X^5 U^2\big)=D
\]
by expansion. For its terms independent of \(EF\), use \(U^4+X=V\) and \(U=X(1+X^3)\). They are
\[
V^2\big(1+(1+X^3)U^3+X(1+X^3)U^2+X^3 U^3\big)=V^2,
\]
because \((1+X^3)+X^3=1\) and \(X(1+X^3)U^2=U^3\). Therefore \(g-\widetilde g=(X^{4^e}+X)A\) as a polynomial, and the two expressions agree as functions on \(K\) without any modification to the question. In particular, on \(K\),
\[
g(x)=S_3(x)^2+\tau(x)(\tau(x)+x)D(x). \tag{2}
\]

## 2. Trace layers and the infinite negative cases

For all \(x\in K\), \(\tau(S_3(x))=\tau(x)\) since each of the three summands has trace \(\tau(x)\), so \(\tau(S_3(x)^2)=\tau(x)^2\). Also \(S_3(x)^4+S_3(x)=x^{64}+x\).

If \(3\mid e\), the subfield \(\mathbb F_{64}\subseteq K\) contains a nonzero element \(z\) with \(\operatorname{Tr}_{\mathbb F_{64}/\mathbb F_4}(z)=S_3(z)=0\) (this trace is a nonzero map on a three-dimensional space). By trace transitivity \(\tau(z)=0\). Equation (2) then gives \(g(z)=g(0)=0\).

If \(3\nmid e\), every element in the kernel of \(S_3\) belongs to \(K\cap\mathbb F_{64}=\mathbb F_4\), where \(S_3\) is the identity. Thus \(x\mapsto S_3(x)^2\) is a bijection on \(K\). It maps the trace-zero layer into itself and hence onto itself. On this layer it agrees with \(g\). Put
\[
H(X)=(1+X)D(X)=1+X+X^9+X^{10}+X^{21}+X^{22}+X^{33}+X^{34}+X^{45}+X^{46}.
\]
If \(x\) satisfies \(\tau(x)=\tau(H(x))=1\), then (2) gives \(\tau(g(x))=1+1=0\). The unique trace-zero \(w\) with \(S_3(w)^2=g(x)\) satisfies \(g(w)=g(x)\), with \(w\ne x\).

For \(e\geq10\), such an \(x\) always exists. Let \(\lambda(z)=(-1)^{\operatorname{Tr}_{K/\mathbb F_2}(z)}\), a nontrivial additive character. Character orthogonality in \(\mathbb F_4\) and trace transitivity give an exact count
\[
N=\frac1{16}\sum_{a,b\in\mathbb F_4}
 (-1)^{\operatorname{Tr}_{\mathbb F_4/\mathbb F_2}(a+b)}
 \sum_{x\in K}\lambda(ax+bH(x)).
\]
The pair \((0,0)\) contributes \(Q\), and the three terms with \(b=0, a\ne0\) give zero. For \(b\ne0\), use \(\operatorname{Tr}_{K/\mathbb F_2}(c x^{2j})=\operatorname{Tr}_{K/\mathbb F_2}(c^{2^{2e-1}}x^j)\) to replace the terms of exponents \(10,22,34,46\) by odd exponents \(5,11,17,23\). The leading term remains \(bX^{45}\), with no cancellation. The polynomial inside \(\lambda\) has reduced odd degree 45 and is not of the form \(R^2+R+\text{constant}\) for a rational function \(R\) over the algebraic closure: any finite pole of \(R\) would give a finite pole of \(R^2+R\), so \(R\) would have to be polynomial, and a nonconstant such \(R\) produces even degree. The additive Weil bound therefore gives modulus at most \(44\sqrt Q\) for each of the 12 remaining character sums. Consequently
\[
16N\geq Q-528\sqrt Q>0\qquad(e\geq10),
\]
since \(\sqrt Q=2^e\). This rules out all \(e\geq10\) not divisible by 3.

## 3. Small cases

The cases not yet covered are \(e=4,5,7,8\). The integers in the following exact certificates are binary coefficient masks in \(\mathbb F_2[Z]/(M(Z))\), where the table encodes \(M\) by the same convention. For each listed modulus the nonzero cycle starting at 1 under multiplication by \(Z\) visits all \(4^e-1\) nonzero masks. Every nonzero element is then a unit, so the quotient is a field.

For each negative case, the table supplies \(\tau(x)=1, \tau(w)=0, g(x)=g(w)=v\), in two field presentations. A row suffices to disprove bijectivity.

| \(e\) | \(M\) | \(x\) | \(w\) | \(v\) |
|---:|---:|---:|---:|---:|
| 5 | 1033 | 86 | 771 | 366 |
| 5 | 1051 | 10 | 305 | 972 |
| 7 | 16427 | 9 | 4147 | 14067 |
| 7 | 16441 | 7 | 2633 | 10911 |
| 8 | 65581 | 14 | 14512 | 17878 |
| 8 | 65593 | 9 | 11760 | 20972 |

For \(e=4\) the two moduli are 285 and 299. In input-mask order, the complete 256-output look-up table for modulus 285 (two hex digits per output) is

```
000161d8b8838786f9de929315145f5e3a1681800607c06813121c1d092d9495
a92953ecfcd42fcaf77bed326b526438fb6dcdf4a2e1eb39b1f889b56977a430
f6978d8c0a0bbd901f1e7473254198990c0d6a6685848b8a4c4d9e9f19188ea8
219ae3b6e7d36c3fe8f2b9e4a78f76dfd5fae5ae2635b2c7ab63f09b28ef0f23
5c5d31544727dbdaa1b4cecf494858629d9cdddc5a5b11104f4e20a6cc65c8c9
bb33f1fed2f3e279c6bf6f883ce97c407ecb91aa6078a5c14a75702a6eaf243d
0203d1d05657be7d43422ef51ba3c4c5505136e6fdadd7d60e2bc2c345440405
b74b370822bc2c3e4672d9a096b082675571e05934ffee7fb3ea1a7aba3b17ac
```

Concatenate the lines before decoding; each mask occurs exactly once. The exact check uses (2), all inputs, and power tables for each modulus. The independent check builds \(\mathbb F_{4^e}[T]/(T^4+T+x)\) separately for each input \(x\), evaluates the original four \((T+a)^n\) by repeated squaring using carryless field arithmetic, and checks that the sum is constant as a polynomial of degree at most 3 in \(T\). It checks all 256 inputs for both moduli and every collision above against the original definition. A separate symbolic replay checks (1), and off-target evaluation tests that the formal difference need not vanish away from \(K\). This completes the classification.
