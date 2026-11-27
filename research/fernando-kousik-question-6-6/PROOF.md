# Trace-fiber classification

Fix \(e\ge2\), \(a\ge0\), and \(n=n_{e,a}=1+2\cdot4^a+2\cdot4^{e-1}+4^e+2\cdot4^{e+a}\). Write \(S_r(X)=\sum_{j=0}^{r-1}X^{4^j}\), including \(S_0=0\).

## 1. Literal derivation of \(g_{n,4}\)

The defining identity is
\[
 g_{n,4}(Z^4-Z)=\sum_{u\in\mathbb F_4}(Z+u)^n.
\]
For \(X\) in an algebraic closure of \(\mathbb F_4\), choose \(Z\) such that \(Z^4+Z=X\). Every \(T=Z+u\), \(u\in\mathbb F_4\), satisfies \(T^{4^r}=T+S_r(X)\) by iterating \(T^4=T+X\). Write
\[
 A=S_a(X),\quad B=S_{e-1}(X),\quad t=S_e(X),\quad C=S_{e+a}(X).
\]
By the definition of \(n\), the summand is the polynomial in \(T\)
\[
 T(T+A)^2(T+B)^2(T+t)(T+C)^2
   =(T^2+tT)(T^2+A^2)(T^2+B^2)(T^2+C^2).
\]
This factorization uses the displayed integer expression for the exponent, so it remains valid when some powers of 4 coincide.

For \(0\le j\le8\) the power sums of the four \(T=Z+u\) vanish except
\[
 \sum T^3=\sum T^6=1,\qquad \sum T^7=X .
\]
Indeed, in the binomial expansion, \(\sum_{u\in\mathbb F_4}u^i\) is zero for \(i=0\) or for \(i>0\) not divisible by 3; it is 1 for positive multiples of 3. For \(j\le8\) only \(i=3,6\) can contribute and their binomial coefficients modulo two give exactly the values above (for \(j=7\) the contribution is \(Z^4+Z\)).

Let \(s_1=A^2+B^2+C^2\) and \(s_2=A^2B^2+A^2C^2+B^2C^2\). The coefficients on \(T^3,T^6,T^7\) in the summand are \(t s_2,s_1,t\), respectively. Thus, as a polynomial identity,
\[
 g_{n,4}(X)=A^2+B^2+C^2+t(A^2B^2+A^2C^2+B^2C^2)+tX.        \tag{1}
\]
Equality on the entire algebraic closure gives equality as polynomials.

For the source's \(a=e/2-1\), put \(h=e/2\). Then \(C=S_{3h-1}\) and the two copies of \(t C\) shown in the question cancel. The formal identities
\[
 C=t+A^{4^e},\qquad t=B+X^{4^{e-1}},\qquad
 S_h^{4^{e-1}}=X^{4^{e-1}}+A^{4^e}
\]
give \(A^2+B^2+C^2=A^2+S_h^{2\cdot4^{e-1}}\). Thus (1) exactly recovers the printed expression after the cancellation, without using it as an assumption.

## 2. The trace layers

Now evaluate at \(x\in K=\mathbb F_{4^e}\), and write \(p=x^{4^{e-1}}\). Thus \(t=S_e(x)=\operatorname{Tr}_{K/\mathbb F_4}(x)\), \(B=t+p\), and \(C=t+A\) since \(A^{4^e}=A\) on \(K\). In (1) the first three squares give \(p^2\). Expanding the three products gives \(A^4+t^2(A^2+B^2)\). Therefore
\[
 g_{n,4}(x)=p^2+tx+tA^4+t^3(A^2+B^2).                         \tag{2}
\]
For \(t=0\), this is the Frobenius map \(x\mapsto p^2\), a bijection on the zero-trace layer because it is a field automorphism commuting with the trace.

For \(t\ne0\), \(t^3=1\), so the \(p^2\) cancels the \(p^2\) term from \(B^2=(t+p)^2\). With \(y=x/t\), \(A=t S_a(y)\), the homogeneity over \(\mathbb F_4\) yields
\[
 \frac{g_{n,4}(t y)}{t^2}
    =1+y+S_a(y)^2+S_a(y)^4
    =1+L(y),\qquad L(Y)=\sum_{j=0}^{2a}Y^{2^j}.                \tag{3}
\]
Here \(\operatorname{Tr}_{K/\mathbb F_4}(y)=1\). In the last equality the exponents in \(S_a(y)^2\) have binary Frobenius indices \(1,3,\ldots,2a-1\), in \(S_a(y)^4\) they are \(2,4,\ldots,2a\), and the term \(y\) has index 0. The trace commutes with binary Frobenius; thus \(\operatorname{Tr}(L(y))=1\) since there are \(2a+1\) terms. This makes the output trace 0 if \(e\) is odd and \(t^2\) if \(e\) is even. The trace onto \(\mathbb F_4\) is surjective: it is \(\mathbb F_4\)-linear and its defining nonzero polynomial of degree \(4^{e-1}<4^e\) cannot vanish identically on \(K\).

If \(e\) is odd, every output lies in the zero-trace layer, which is a proper subset of \(K\). The zero-trace input layer already maps onto it by Frobenius, so the image size is exactly \(4^{e-1}\).

## 3. The binary kernel for even \(e\)

Suppose \(e\) is even, so the input layer \(t\) maps into the output layer \(t^2\) and these four targets are distinct. Let \(d=\gcd(2a+1,e)=\gcd(2a+1,2e)\), the equality holding because \(2a+1\) is odd. For \(L\) in (3),
\[
 L(y)^2+L(y)=y^{2^{2a+1}}+y.
\]
Thus an element of \(\ker L\) belongs to the fixed subfield \(\mathbb F_{2^d}\) inside \(K=\mathbb F_{2^{2e}}\). On that subfield the terms of \(L\) run through \((2a+1)/d\) complete rounds of the binary Frobenius, an odd number, so \(L(y)=\operatorname{Tr}_{\mathbb F_{2^d}/\mathbb F_2}(y)\). Therefore
\[
 \ker L=\{y\in\mathbb F_{2^d}:\operatorname{Tr}_{\mathbb F_{2^d}/\mathbb F_2}(y)=0\},
 \qquad |\ker L|=2^{d-1}.
\]
The last count follows because the binary trace is surjective (it sends 1 to 1 since \(d\) is odd). As \(d\mid e\) is odd, \(e/d\) is even. The relative trace \(S_e\) is identically zero on \(\mathbb F_{2^d}\): the fourth-power Frobenius on that subfield has order \(d\) and the sum repeats \(e/d\) full rounds. In particular \(\ker L\) is contained in the zero-trace layer. An affine layer in (3) maps with precisely \(2^{d-1}\) preimages per attained value, by binary linearity. It is bijective onto its target layer if and only if \(d=1\). If \(d>1\), any nonzero vector of the kernel can be added within such an input layer to exhibit a collision.

This proves the stated criterion. It also gives the exact image size for even \(e\): \(4^{e-1}(1+3/2^{d-1})\). Substituting \(a=e/2-1\) gives \(2a+1=e-1\), hence \(d=1\) for the entire domain of Question 6.6. Substituting \(a=2\) recovers the source's positive range \(e\) even and \(10\nmid e\); in particular \(10\mid e\) gives collisions as well.
