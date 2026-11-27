# Permutation-polynomial classifications for Fernando–Kousik Questions 6.1 and 6.3

This answers Questions 6.1 and 6.3 of N. Fernando and B. Kousik, [*A further study of
polynomial \(g_{n,q}\) over finite fields*, arXiv:2606.01037v1, §6](https://arxiv.org/html/2606.01037v1#S6).

**Question 6.1.** For a power of two \(q>2\) and a positive even integer \(e\), the
polynomial of Question 6.1 permutes \(\mathbb F_{q^e}\) if and only if
\[
  (q=4\text{ and }4\mid e)
  \qquad\text{or}\qquad
  (e=4\text{ and }q\not\equiv 3\pmod5).
\]
The second restriction for \(e=4\) is equivalently
\(\log_2 q\not\equiv 3\pmod4\).

**Question 6.3.** Its polynomial permutes \(\mathbb F_{q^e}\) if and only if
\(q=4\) and \(4\mid e\).

## 1. Common reduction

Write \(q=2^s\), \(e=2m\), \(K=\mathbb F_{q^{2m}}\), \(F=\mathbb F_{q^m}\),
\(\sigma(z)=z^{q^m}\), \(\tau(z)=z+\sigma(z)\), and
\(T=\operatorname{Tr}_{F/\mathbb F_q}\).
For \(S_j(z)=\sum_{i=0}^{j-1}z^{q^i}\) put \(S=S_m\). For an input \(x\in K\)
write
\[
 u=S(x),\qquad t=S_{2m}(x)=\tau(u),\qquad w=u^q+u=\tau(x).
\]
The last identity follows by telescoping. Denote the polynomials in Questions
6.1 and 6.3, respectively, by \(f_1,f_3\). On \(K\), the source formulas give
\[
 f_1(x)=x+u+t+t u^{q-1},\qquad f_3(x)=x+u+t(u+t)^{q-1}.
\]
In the second identity, \(S_{m+1}(x)^{q^m}=\sigma(u)+x\).
Write the corresponding maps as \(x+h_i(u)\).

The kernel of \(S\) is the kernel of \(T\) inside \(F\): \(S(x)=0\) gives
\(\tau(x)=0\), so \(x\in F\), where \(S=T\). Since \(T\) is onto, \(|\ker S|=q^{m-1}\).
The image of \(S\) is
\[
 H=\{u\in K:\tau(u)\in\mathbb F_q\},
\]
by containment and equality of cardinalities \(q^{m+1}\). For each \(u\in H\),
translation by \(h_i(u)\) is a bijection from the \(S\)-fiber over \(u\) to
the \(S\)-fiber over
\[
 \xi_i(u)=u+S(h_i(u)).
\]
Thus \(f_i\) is a permutation of \(K\) if and only if \(\xi_i\) is a
permutation of \(H\). Both maps \(\xi_i\) are homogeneous under multiplication
by \(\mathbb F_q^*\).

For \(t=0\), both \(\xi_i\) restrict on \(F\) to \(u\mapsto u+T(u)\). If
\(m\) is odd, any nonzero \(x\in\mathbb F_q\) has \(u=x\), \(t=0\), and
\(f_1(x)=f_3(x)=0\): neither polynomial is a permutation. If \(m\) is
even, \(T(a)=0\) for \(a\in\mathbb F_q\) and \(u\mapsto u+T(u)\) is an
involution. In this case a single \(u\notin F\) mapping into \(F\) under
\(\xi_i\) proves nonpermutation.

For \(t\ne0\) one can normalize \(u=tU\), with \(\tau(U)=1\).
Write \(v=U^2+U\in F\) and \(A(V)=\sum_{j=0}^{s-1}V^{2^j}\).
The normalized inputs \(U\) correspond in pairs \(\{U,U+1\}\) to the \(v\)
whose absolute trace on \(F\) is 1: this is the standard Artin–Schreier
criterion, since the image of \(z\mapsto z^2+z\) on \(F\) is exactly its
absolute-trace-zero subspace. Then
\[
 W_0=U^q+U=A(v),\qquad T(W_0)=1.
\]
The second identity telescopes to \(U^{q^m}+U=1\). Moreover,
\[
 h_1(U)=U+\frac{W_0}{U},\qquad h_3(U)=h_1(U+1),\qquad
 \xi_3(U)=\sigma(\xi_1(U))+1 .
\]
The last formula uses that \(S\) and \(h_1\) commute with \(\sigma\) and that
\(U+1=\sigma(U)\). Upon restoring scale \(t\) it reads
\(\xi_3(u)=\sigma(\xi_1(u))+t\).

Hereafter assume \(m\) even. On either input \(U\) or \(U+1\),
\(\tau(h_1)=\tau(h_3)=1+W_0/v\). Consequently, for \(x\) with \(S(x)=tU\),
\[
 \begin{split}
 \tau(f_i(x))&=t\left(W_0+1+W_0/v\right),\\
 \tau(\xi_i(tU))&=T(\tau(f_i(x)))=t\left(1+T(A(v)/v)\right).
 \end{split} \tag{1}
\]
The intermediate identity follows from
\(T(\tau(z))=S_{2m}(z)=\tau(S(z))\) for all \(z\in K\).

## 2. Exclusion of \(q\ge8\), even \(m\ge4\)

Let \(P(V)=\sum_{j=0}^{s-1}V^{2^j-1}\), a polynomial (with constant term
1) equal to \(A(V)/V\) away from zero. Its degree is the odd number
\(D=q/2-1\ge3\). Count \(v\in F\) such that the absolute trace of \(v\)
is 1 and \(T(P(v))=1\). Character orthogonality, over \(\mathbb F_2\) and
\(\mathbb F_q\) respectively, expresses this count as \(1/(2q)\) times a
signed sum of sums
\[
  \sum_{v\in F}
   (-1)^{\operatorname{Tr}_{F/\mathbb F_2}(cP(v)+\epsilon v)},
   \qquad c\in\mathbb F_q,\quad \epsilon\in\mathbb F_2 .
\]
The trivial term is \(q^m\), and the term \(c=0,\epsilon=1\) is zero.
Every term with \(c\ne0\) has absolute value at most
\((D-1)q^{m/2}\) by the additive character-sum bound for an odd-degree
polynomial in characteristic two ([Weil, 1948](https://doi.org/10.1073/pnas.34.5.204)).
The leading coefficient is nonzero and \(D>1\), so the linear perturbation
does not change the degree. The count is therefore at least
\[
 \frac{q^m-2(q-1)(D-1)q^{m/2}}{2q}>0,
\]
where \(q^{m/2}\ge q^2>(q-1)(q-4)=2(q-1)(D-1)\).
Such a \(v\) is nonzero, so (1) supplies an input \(u\notin F\) mapping into
\(F\) for both \(\xi_i\). This excludes the stated range for both questions.

## 3. Both maps permute when \(q=4\) and \(m\) is even

Now \(W_0=v+v^2\), so (1) simplifies to \(\tau(f_i(x))=t v^2\) at \(t\ne0\).
Let \(W=\xi_i(u)^4+\xi_i(u)=\tau(f_i(x))\). Any output with \(t\ne0\) has
\(T(W)=t T(v)^2\ne0\), because
\(T(v)\in\{\omega,\omega^2\}\) for either choice of
\(\omega\in\mathbb F_4\setminus\mathbb F_2\).
Outputs from \(t=0\) are in \(F\), hence have \(T(W)=0\); they are already
distinct by the involution of §1.

Fix an output \(W\) with \(T(W)\ne0\). For \(t\ne0\) the constraints
\(W=t v^2\), \(T(v)\in\{\omega,\omega^2\}\) give exactly two possibilities
for \(t\), then one \(v\) for each \(t\); both \(v\) have absolute trace 1.
Each of the two candidate pairs \(\{tU,t(U+1)\}\) for \(\xi_1\) has output
difference \(t(1+T(v))=T(W)\). Indeed, \(h_1(U)=1+v+vU\) follows from
\(U^2+U=v\) and \(h_1=U+1+U^3\), so
\(h_1(U)+h_1(U+1)=v\). The four outputs at this \(W\) therefore have to
occupy the two cosets of \(\{0,T(W)\}\) in the affine \(\mathbb F_4\)-line
\(\{Y:Y^4+Y=W\}\), if the two pairs are disjoint.

By homogeneity rescale to \(t_1=1\), with \(W=v^2\) and \(a=T(v)\).
Then \(T(W)=a^2\); the other pair has \(t_2=a\), \(v_2=a v\).
Choose \(B\in F\) with \(B^2+B=a^2v\): this exists because the absolute trace
of \(a^2v\) is the trace of \(a^2T(v)=1\) from \(\mathbb F_4\) to \(\mathbb F_2\),
which is zero. For the latter pair one may take \(U_2=U+B\).
With \(Y_1=\xi_1(U)\) and \(Y_2=\xi_1(a(U+B))\), the formula for \(h_1\) and
\(S(1)=0\) give
\[
 Y_1=U+a+S(vU),\qquad
 Y_2=aU+aB+1+a^2S(vU)+a^2 T(vB).
\]
In particular \(\Delta=(Y_1+Y_2)/a^2\in\mathbb F_4\), and explicitly
\[
 \Delta=U+a^2 B+1+a^2S(vU)+T(vB).
\]
We show that \(\Delta^2+\Delta=1\), which excludes \(\Delta\in\{0,1\}\).
Expanding, using \(U^2+U=v\) and \(B^2+B=a^2v\), gives
\[
 \Delta^2+\Delta
   =B+S((B^4+B)U+a v^3)+T(vB+v^2B^2).
\]
To check this expansion, \(a+a^2=1,\ a^3=1\), and
\(B^4+B=a^2v+a v^2\). Next
\(S((BU)^4+BU)=B\) by telescoping and \(U^4+U=v+v^2\). Replace
\((B^4+B)U\) by \((BU)^4+BU+B^4(U^4+U)\). The result becomes
\[
 T\big(B^4(v+v^2)+a v^3+vB+v^2 B^2\big)
 =T(a^2v^2+a v^4)=a+a^2=1 .
\]
This gives the disjointness for \(\xi_1\). The relation in §1 maps the
\(\xi_1\) output pair for scale \(t\) to the same pair translated by \(t\)
for \(\xi_3\), since \(\sigma\) exchanges the inputs of a pair.
In the normalization just used, the two translations differ by
\(1+a=a^2=T(W)\), so the two cosets remain distinct. This establishes
permutation for both maps.

## 4. Complete answer for \(\xi_1\) at \(e=4\)

Here \(m=2\), \(\xi_1|_F(u)=u^q\) and \(S(z)=z+z^q\). On the normalized
line \(\tau(U)=1\), write \(Y=\xi_1(U)\). Using \(W_0=U^q+U\) and
\(W_0^q=W_0+1\),
\[
 Y=U^q+\frac{W_0^2+U}{U U^q}
  =\frac{(U+1)(U^{2q}+U)}{U U^q}.
\]
In this expression \(U^{2q}+U\) is fixed by \(\sigma\). Define
\(R=U/(U+1)\), which bijects this line with
\(\mu_{q^2+1}\setminus\{1\}\) (the indicated roots of unity in \(K\));
the inverse is \(U=R/(R+1)\). Whenever \(Y\ne0\),
\[
  \frac{\sigma(Y)}Y=R^{q+2}.
\]
The equality \(Y=0\) is equivalent to \(R^{2q-1}=1\). In one direction,
\(U^{2q}=U\) implies \((U+1)^{2q}=U+1\); in the other direction
\(R^{2q-1}=1\) gives equality of \(U^{2q}/U\) and
\((U+1)^{2q}/(U+1)\), whose common value must be 1 by adding the two
corresponding numerator identities.

On \(\mu_{q^2+1}\), raising to \(2q-1\) is equivalent to raising to
\(q(q+2)\). Moreover \(\gcd(q+2,q^2+1)=\gcd(q+2,5)\).
If \(q\not\equiv3\pmod5\), all the normalized outputs \(Y\) are
nonzero, their conjugate ratios are distinct and no such ratio is 1.
For an arbitrary input \(u=tU\) with \(t\ne0\), output is \(tY\) with
the same ratio. Thus the output determines \(U\) and then \(t\).
All these outputs are outside \(F\) and the already bijective \(t=0\)
case is separate. If \(q\equiv3\pmod5\), take any nontrivial fifth root
of unity for \(R\); it gives \(Y=0\). Then \(\xi_1(U)=0\) and
\(\xi_3(U)=1\), both in \(F\). Both maps fail in this case by §1.
These cases and §§1–3 give the complete classification for Question 6.1.

## 5. A moment obstruction for Question 6.3 at \(e=4\)

It remains to rule out \(e=4\) with \(q=2^s\ge8\) and \(s\not\equiv3\pmod4\).
In this range \(s\ge4\), and §4 gives the bijective map \(\xi_1\).
For a normalized \(U\), set \(Y=\xi_1(U)\), \(b=\tau(Y)\ne0\),
\(a=1/b\), and \(y=Y/b\). Then \(\tau(y)=1\).
The scaling \(U\mapsto aU\) gives
\[
 \xi_1(aU)=y,\qquad \xi_3(aU)=y+1+a .
\]
The \(q^2\) points \(U\) in the normalized line yield the \(q^2\) distinct
\(y\) in the output line \(\tau(y)=1\): distinctness follows from the
conjugate ratio in §4. The conjugate pair \(\{U,U+1\}\) gives
\(\{y,y+1\}\) with the same \(a\). Write \(Z=y^q+y\), which is fixed
by the translation \(y\mapsto y+1+a\). For each fixed \(Z\), the points
\(y\) form one affine \(\mathbb F_q\)-line. Its pairs modulo translation by
1 form a torsor over \(\mathbb F_q/\mathbb F_2\).
If \(\xi_3\) were bijective, translation by the class of \(a\) on each
pair would permute this torsor. After identifying its translation group
with the image of \(d\mapsto d^2+d\) on \(\mathbb F_q\), summing over
the torsor gives \(\sum(a^2+a)=0\) for every \(Z\). (Any choice of origin
works, since the multiset of outputs equals the multiset of inputs.)
In particular, for every \(j\ge0\) it would give
\[
 \mathcal M_j=\sum_{\{U,U+1\}} Z^j(a^2+a)=0. \tag{2}
\]

We compute one \(\mathcal M_j\) explicitly in each of the three residue
classes of \(s\). The details below give finite coefficient recurrences
over \(\mathbb F_4\), rather than an evaluation in a field of size
\(q^4\).

### 5.1. Two successive linearized root sums

As before \(v=U^2+U\), and now write \(w=A(v)=U^q+U\); then \(w^q+w=1\).
For each such \(w\), the \(v\)'s belonging to it are precisely the roots
of \(A(v)=w\): every root satisfies \(v^q+v=w^2+w\), so \(v^{q^2}=v\),
and has absolute trace \(A(v)+A(v)^q=1\). Thus each root denotes one
pair in (2). Put \(d=w^2+w\), \(D=d+1\), and \(V=v+w^2\).
By (1) with \(T(z)=z+z^q\),
\[
 b=1+\frac wv+\frac{w+1}{v+d}
   =\frac{(v+w^2)(v+w+1)}{v(v+d)},\qquad
 Z=\frac{w+1+w/v}{b}.
\]
For \(E=V(V+D)\), \(N_t=(V+w)(V+w^2)\), and
\(N_z=(V+w)((w+1)(V+w^2)+w)\), we have
\(a=N_t/E\), \(Z=N_z/E\). Consequently the summand is
\[
 Z^j(a^2+a)=\frac{N(V,w)}{V^{J}(V+D)^{J}},
 \qquad N=N_z^j(N_t^2+N_tE),\qquad J=j+2. \tag{3}
\]
The degree of \(N\) in \(V\) is strictly below \(2J\), since
\(N_t^2+N_tE\) has degree at most three in \(V\).

The \(w\)'s themselves split into the two root sets \(A(w)=c\), for
\(c\in\{\omega,\omega^2\}=\mathbb F_4\setminus\mathbb F_2\), since
\(A(w)^2+A(w)=w^q+w=1\).
For fixed \(A(w)=c\), the roots in \(V\) satisfy
\(A(V)=w+c^2\). If \(\epsilon=s\bmod 2\), the translated roots \(V+D\)
satisfy \(A(V+D)=w+c+\epsilon\).

Write
\[
 M_k(C)=[z^{k-1}]\frac{1}{C+A(z)}
       =\sum_{n=0}^{k-1}\frac{[z^{k-1}]A(z)^n}{C^{n+1}}
 \qquad(C\ne0,\ k\ge1). \tag{4}
\]
This equals the sum of the negative \(k\)th powers of the roots of
\(A(X)=C\), by logarithmic differentiation of \(C+A(z)\), whose
derivative is 1. The same logarithmic derivative at infinity shows
that the sum of any polynomial of degree strictly below \(q/2-1\)
over any root set of \(A(X)=C\) is zero.

For \(D\ne0\), (3) is proper as a rational function of \(V\), with poles
at \(0,D\). For the pole \(u=0\) or \(u=D\), let
\(P_{u,l}(w)=[z^l]N(u+z,w)\).
The coefficient of \((V+u)^{-k}\) in its principal part is
\[
 C_{u,k}(w)=
  \sum_{l+r=J-k}
   \binom{J+r-1}{r}\frac{P_{u,l}(w)}{D^{J+r}}
  \qquad (1\le k\le J), \tag{5}
\]
as follows by expanding \((D+z)^{-J}\).
The inner root sum of (3), as a rational function of \(w\) for the
fixed value \(c\), therefore equals
\[
 {\cal R}_c(w)=
 \sum_{k=1}^{J}
 \left(C_{0,k}(w)M_k(w+c^2)+C_{D,k}(w)M_k(w+c+\epsilon)\right). \tag{6}
\]
Its only possible finite poles are \(w=c,c^2\), each of order at most
\(2J\) by (4)–(5).

The polynomial part of (6) has degree at most \(2j\).
Indeed, after either substitution \(V=z\) or \(V=D+z\), \(N_t,E,N_z\)
have total degrees in \((z,w)\) at most \(3,3,4\), respectively:
\(E=z(z+D)\), and the two factors \(V+w,V+w^2\) have degrees at most
\(1,2\) in one order or the other. Thus \(\deg_w P_{u,l}\le4j+6-l\).
A summand in (5) has growth at infinity at most \(w^{2j+2-l-2r}\).
For \(k\ge2\), \(M_k(w+\text{constant})=O(w^{-2})\) by (4), so the
product has growth at most \(w^{2j}\). For \(k=1\),
\(M_1(w+\text{constant})=O(w^{-1})\) but \(l+r=J-1\ge1\),
giving the same bound. Here growth means the difference of the numerator
and denominator degrees. For the three classes used below, \(2j<q/2-1\).
It follows from (4) at infinity that the polynomial part makes no
contribution when summing (6) over a full \(w\)-root set.

### 5.2. Evaluating the outer root sums

Write \(L_k=[x^{-k}]{\cal R}_c(c+x)\) and
\(B_k=[x^{-k}]{\cal R}_c(c^2+x)\). For even \(s\), neither \(c\) nor
\(c^2\) belongs to \(A(w)=c\), because \(A(c)=A(c^2)=0\) if
\(s\equiv0\pmod4\), and \(A(c)=A(c^2)=1\) if \(s\equiv2\pmod4\).
Thus the contribution of this root set to \(\mathcal M_j\) is
\[
 \sum_{k=1}^{2J}(L_k+B_k)M_k(A(c)+c). \tag{7}
\]

For \(s\equiv1\pmod4\), the only exceptional point of this root set is
\(w=c\), with \(D=0\); here \(A(c)=c,\ A(c^2)=c^2\).
For the nonexceptional points the contribution of (6) is
\[
 L_0+\sum_{k=1}^{2J}\left(L_k I_k+B_kM_k(1)\right),
 \qquad I_k=[z^k]\frac{z}{A(z)}. \tag{8}
\]
To see this, for the pole \(c\), \(I_k\) is the negative \(k\)th-power
sum over the nonzero roots of \(A(X)=0\). The logarithmic derivative of
\(A(z)/z\) is \(1/A(z)+1/z\), proving this formula for \(I_k\).
For the other pole \(c^2\), excluding \(w=c\) changes \(M_k(1)\) by 1,
since \(c+c^2=1\). The polynomial part over the truncated root set
contributes its value at \(c\) (in characteristic two), which equals
\(L_0+\sum_{k\ge1}B_k\) by the Laurent expansion there. The two
corrections \(\sum B_k\) cancel, proving (8).
Finally the exceptional point itself uses (3) with denominator
\(V^{2J}\), and its contribution is
\[
 \sum_{l=0}^{2J-1}[V^l]N(V,c)\,M_{2J-l}(1); \tag{9}
\]
indeed \(A(V)=1\) at this point.

### 5.3. Coefficient certificate

Take \(j=3,5,5\) in the classes \(s\equiv0,1,2\pmod4\), respectively.
The needed truncation of \(A(z)\) in (4), (8) and (9) is
\(z+z^2+z^4+z^8\). In particular (4) needs degrees through \(2J-1\le13\),
and \(A(z)/z\) in (8) needs degrees through \(2J\le14\).
All these truncations agree with the displayed polynomial for every
\(s\ge4\) (after dividing by \(z\) in (8)).

Here is the coefficient calculation for \(c=\omega\); write
\(0,1,2,3\) for \(0,1,c,c^2\), with addition by bitwise XOR and
\(c^2+c+1=0\). The lists start with \(k=1\); all omitted coefficients
are zero. The last column is (7) or the sum of (8) and (9).

| \(s\bmod4\) | \(j\) | \(L_0\) | \(L_1,L_2,\ldots\) | \(B_1,B_2,\ldots\) | Contribution |
|---:|---:|---:|:---|:---|---:|
| 0 | 3 | 0 | 3,0,0,2,0,3,2 | 2,2,3,3,0,1,2 | 2 |
| 1 | 5 | 2 | 3,1,3,0,0,1,1 | 0,2,1,1,2,2,1 | 3 |
| 2 | 5 | 0 | 3,2,3,0,0,2,1,3 | 0,0,1,1,2,0,1,2 | 2 |

For reproducibility, the table can be computed directly using (3)–(6):
for a pole \(p=c\) or \(p=c^2\) put \(w=p+x\), so \(D=x(1+x)\).
Each summand for \(L_k\) or \(B_k\) becomes a polynomial in \(x\) times
\(x^{-d}(1+x)^{-d}(C_0+x)^{-f}\), with \(d=J+r\) from (5),
\(f=n+1\) from (4), and \(C_0=p+c^2\) or \(p+c+\epsilon\).
If \(C_0=0\), the last factor is \(x^{-f}\); otherwise the coefficient
of \(x^h\) in it is
\(\binom{f+h-1}{h}C_0^{-f-h}\).
The coefficient of \(x^h\) in \((1+x)^{-d}\) is
\(\binom{d+h-1}{h}\) in characteristic two. These formulas independently
specify every entry and the companion script evaluates them using only
\(\mathbb F_4\) arithmetic. In the row \(s\equiv1\pmod4\), (9) is zero:
one can substitute \(N(V,c)=cV^5(V+c)^5(V^3+1)\) into (9) and use (4).

For \(c=\omega^2\), every table entry's field value is the square of the
corresponding value for \(\omega\), since all coefficient formulas are
defined over \(\mathbb F_2\). In each row the contribution for the two
root sets sums to \(c+c^2=1\). Hence \(\mathcal M_j=1\), contrary to (2).
This completes the classification for Question 6.3 as well.

## 6. Exact checks

Run the companion script with Node.js. It verifies the defining digit
identities on small fields, the trace-pair and conjugate-ratio formulas,
the entire coefficient table above, and the nonzero moments directly
in fields with \(s=4,5,6,8,9,10\). The general proof does not extrapolate
from these finite-field samples: equations (3)–(9) and the fixed
\(\mathbb F_4\) coefficient certificate evaluate the moments uniformly.
