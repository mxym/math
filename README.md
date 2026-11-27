# The Li–Li–Helleseth–Qu conjectured bent family is Maiorana–McFarland

**Theorem.** Conjecture 2 of Kangquan Li, Chunlei Li, Tor Helleseth and
Longjiang Qu (2023) holds for every positive integer \(k\). More precisely,
each function in that conjecture belongs to the completed
Maiorana–McFarland class \(\mathcal M^\#\): an explicit involutory
linear shear takes it to ordinary Maiorana–McFarland form.

The core step is an exact identity in the absolute trace. The underlying
permutation is a special case of a theorem of Ding and Zieve; its
permutation property is not claimed as new. A short, independent
proof of that ingredient is included.

## 1. Statement and notation

The conjecture appears in Section IV, p. 34 of the
[author-posted manuscript](https://www.researchgate.net/publication/374351274_Further_investigations_on_permutation_based_constructions_of_bent_functions),
with class membership left undetermined in its Table I. Its version
of record is [JCTA 199 (2023), Article 105779](https://doi.org/10.1016/j.jcta.2023.105779).

Write \(m=6k\), \(q=2^k\), \(E=\mathbb F_{2^m}=\mathbb F_{q^6}\), and
\(\operatorname{Tr}=\operatorname{Tr}_{E/\mathbb F_2}\). The function
in the conjecture, on \(E\times E\), is
\[
 f(x,y)=\operatorname{Tr}\!\left(
 y^{2^{2k}+2^k+1}+
 (x^{2^k+1}+x^{2^{3k}+2^k}+x^{2^{4k}+2^{3k}})y\right).
\]
Thus, with
\[
 \psi(X)=X^{q+1}+X^{q^3+q}+X^{q^4+q^3},
\]
it is exactly \(f(x,y)=\operatorname{Tr}(y^{1+q+q^2}+y\psi(x))\).
All assertions below are for \(k\ge1\), including \(k=1\).

## 2. The trace shear identity

Set \(z=x+y^{q^4}\), an invertible change \((x,y)\mapsto(z,y)\)
that is its own inverse and is linear even over \(\mathbb F_q\).
Put \(u=y^{q^4}\), so that \(x=z+u\) and
\[
 u^q=y^{q^5},\qquad u^{q^3}=y^q,\qquad u^{q^4}=y^{q^2}.
\]
Here and below, Frobenius indices on \(E\) are taken modulo 6. Expanding
the three products in \(y\psi(z+u)\) gives \(y\psi(z)\) and nine
other terms. The following table lists every one of them, together
with the original \(y\)-only term. A pair on one row contributes
zero under the absolute trace, which is invariant under every
\(q\)-Frobenius power.

| First term | Second term | Second term equals the first raised to |
|---|---|---:|
| \(y z y^{q^5}\) | \(y y^{q}z^{q}\) | \(q\) |
| \(y y^{q^4}z^{q}\) | \(y z^{q^3}y^{q^2}\) | \(q^2\) |
| \(y z^{q^3}y^{q^5}\) | \(y y^{q} z^{q^4}\) | \(q\) |
| \(y y^{q^4}y^{q^5}\) | \(y y^{q}y^{q^5}\) | \(q\) |
| \(y y^{q}y^{q^2}\) from \(y\psi(u)\) | original \(y^{1+q+q^2}\) | \(1\) |

Consequently the exact relation, in the original coordinates, is
\[
 f(x,y)=\operatorname{Tr}\bigl(y\psi(x+y^{q^4})\bigr).
 \tag{1}
\]
This identity does not rely on \(\psi\) being a permutation.

## 3. The known permutation ingredient

Ding and Zieve's [Theorem 1.1](https://doi.org/10.1112/plms.12540)
(giving necessary and sufficient coefficient conditions; see also
[their preprint](https://arxiv.org/abs/2203.04216)) already
implies that \(\psi\) permutes \(E\). To disambiguate their variables
from ours, the substitution is:

| Ding–Zieve notation | Value here |
|---|---|
| base size in their quadratic extension | \(Q_0=q^3=2^{3k}\) |
| their smaller prescribed Frobenius power | \(Q=q=2^k\) |
| their leading power \(r\) | \(Q+1=q+1\) |
| their polynomial \(A\) | \(A(S)=S^{Q+1}+S+1\) |
| their coefficient tuple \((a,b,c,d)\) | \((1,0,1,1)\) |

Indeed \(X^{q+1}A(X^{q^3-1})=\psi(X)\) exactly. Their
condition (1) holds because \(\gcd(q+1,q^3-1)=1\), and (2)
is characteristic two. Their norm sum \(e\) in (3) equals 1;
both sides in (4) equal 1. For (5) let \(d_0=2^{v_2(k)}\).
The left side is the relative trace of \(1\) from
\(\mathbb F_{2^{3k}}\) to \(\mathbb F_{2^{d_0}}\), namely
\(3k/d_0\) interpreted in characteristic two; the right side is
\(\operatorname{lcm}(3k,k)/d_0=3k/d_0\), interpreted the same way.
This is a proof from the earlier classification, not a novelty
claim for this trinomial.

### A direct proof that does not invoke the classification

Write \(K=\mathbb F_{q^3}\), \(\bar x=x^{q^3}\) on \(E\), and
\(U=\{s\in E^\times:s\bar s=1\}\). For \(x\ne0\) put \(s=\bar x/x\).
Then
\[
 \psi(x)=x^{q+1}D(s),\qquad
 D(s)=1+s+s^{q+1},\qquad N(s)=1+s^q+s^{q+1}.
\]
On \(U\), \(N(s)=s^{q+1}\overline{D(s)}\).
If \(D(s)=0\), then also \(N(s)=0\), so \(s^q=s\). But
\(U\cap\mathbb F_q^\times=\{1\}\), since any such element satisfies
\(s^2=1\); and \(D(1)=1\). Thus \(\psi(x)\ne0\) on \(E^\times\),
and the induced map on \(U\) is the well-defined
\[
 G(s)=\frac{\overline{\psi(x)}}{\psi(x)}
      =\frac{N(s)}{D(s)}\in U.
 \tag{2}
\]

Choose \(\omega\in\mathbb F_{q^2}\subset E\) with
\(\omega+\omega^q=1\), by rescaling any element outside
\(\mathbb F_q\) by its nonzero relative trace. Since 3 is odd,
\(\bar\omega=\omega^q=\omega+1\);
\(K\cap\mathbb F_{q^2}=\mathbb F_q\). Write
\(c=\omega\bar\omega\in\mathbb F_q\), so
\(X^2+X+c\) is the minimal polynomial of \(\omega\) over \(\mathbb F_q\).
The fractional linear map
\[
 L(t)=\frac{t+\omega}{t+\bar\omega},\quad L(\infty)=1
\]
sends \(\mathbb P^1(K)\) bijectively to \(U\): its denominators
for finite \(t\in K\) are nonzero, its determinant is
\(\omega+\bar\omega=1\), and each image has relative norm one.
Both sets have \(q^3+1\) elements. The inverse for \(s\ne1\)
is \((\omega+\bar\omega s)/(1+s)\).

For finite \(t\in K\), set \(u_0=t+\omega\), \(v_0=t+\bar\omega\).
Multiplying \(D(L(t))\) and \(N(L(t))\) by \(v_0v_0^q\) gives,
respectively,
\[
 D'=v_0^q+u_0u_0^q,\qquad N'=v_0+u_0u_0^q,
\]
because \(u_0+v_0=u_0^q+v_0^q=1\).
Hence \(D'+N'=t+t^q+1\) and
\(\omega D'+\bar\omega N'=t^{q+1}+c+1\).
The denominator \(t+t^q+1\) has trace \(1\) to \(\mathbb F_q\),
so it never vanishes. In particular a finite \(t\) cannot be
mapped to \(\infty\) under the conjugate of \(G\). At \(\infty\),
\(L(\infty)=1\) and \(G(1)=1\). In the finite chart, (2)
therefore conjugates to
\[
 \Phi_b(t)=\frac{t^{q+1}+b}{t+t^q+1},\qquad b=c+1\in\mathbb F_q.
 \tag{3}
\]

We show (3) permutes \(K\); the argument works for every
\(b\in\mathbb F_q\). For \(w\in K\), the equation \(\Phi_b(t)=w\)
is exactly
\[
 (t+w)(t^q+w)=w^2+w+b.
 \tag{4}
\]
If \(\delta=w^2+w+b=0\), then \(w\in\mathbb F_{q^2}\cap K=\mathbb F_q\)
because it is a root of a polynomial of degree 2 over \(\mathbb F_q\).
Equation (4) then has the unique solution \(t=w\), for which (3)
has no pole.

If \(\delta\ne0\), put
\[
 A=\begin{pmatrix}1&1\\0&1\end{pmatrix},\quad
 B=\begin{pmatrix}0&b\\1&0\end{pmatrix},\quad
 M_w=wA+B=\begin{pmatrix} w&w+b\\1&w\end{pmatrix}.
\]
The determinant is \(\delta\), and \(M_w^2=\delta I\). In projective
notation with \(\sigma(t)=t^q\) on \(\mathbb P^1(K)\), equation (4)
on the non-pole chart is \(t^q=M_w\cdot t\). Thus the desired points
are fixed points of \(\eta=M_w^{-1}\circ\sigma\). As a projective
map \(M_w^{-1}\) is represented by \(M_w\). Since \(\sigma^3=I\)
on \(K\), the third iterate \(\eta\circ\eta\circ\eta\) is represented
by the **Frobenius-twisted** matrix product
\[
 S=M_w\,M_w^{(q)}\,M_w^{(q^2)},
\]
where superscripts in parentheses apply Frobenius to each entry.
This is not the ordinary cube of \(M_w\).

One checks \(A^2=I\), \(B^2=bI\), \(AB+BA=I\). In particular
\(ABA=A+B\) and \(BAB=bA+B\); every word of length three in
\(A,B\) is in their linear span. Thus \(S\) is in that span.
It is invertible and has trace zero. Moreover the span contains
no nonzero scalar matrix: in \(uA+vB\) the lower-left entry is
\(v\), and if \(v=0\) the upper-right entry is \(u\).
A nonscalar invertible \(2\times2\) matrix of trace zero over \(K\)
has characteristic polynomial \(X^2+\det(S)\), with a single
root in the finite field \(K\). Its eigenspace is one-dimensional
(otherwise \(S\) would be scalar), and its line is the unique
projective fixed point of \(S\) on \(\mathbb P^1(K)\).
The map \(\eta\) commutes with its third iterate, so it fixes that
unique point. Conversely, any point fixed by \(\eta\) is fixed by
the third iterate. This unique point is neither \(\infty\), since
\(\sigma(\infty)=\infty\) and \(M_w\cdot\infty=w\), nor \(w\), since
\(M_w\cdot w=\infty\) but \(w^q\) is finite. It therefore gives exactly
one finite solution of (4), without gaining or losing a pole solution.

Thus \(G\) permutes \(U\). The homomorphism \(x\mapsto\bar x/x\)
from \(E^\times\) has kernel \(K^\times\) and image \(U\) by the
group sizes. On each fiber, multiplication by \(\lambda\in K^\times\)
changes the value of \(\psi\) by \(\lambda^{q+1}\).
The power \(q+1\) is invertible modulo \(q^3-1\):
\(q^3-1\equiv-2\pmod{q+1}\) and \(q+1\) is odd. It follows that
\(\psi\) is a bijection between the individual source fiber and the
target fiber specified by (2). Finally \(\psi(0)=0\), proving the
permutation assertion on all of \(E\). The proof makes no exclusions
at \(q=2\) or \(q=4\).

## 4. Maiorana–McFarland class and exact Walsh signs

The bilinear pairing \(\operatorname{Tr}(yz)\) is the ordinary binary
dot product in dual \(\mathbb F_2\)-bases; it is nondegenerate because
the absolute trace is a nonzero linear functional, and multiplication
by any nonzero element of \(E\) is bijective. In the coordinates
\((z,y)\), the function in (1) is exactly a dot product of \(y\)
with the permutation \(\psi(z)\), i.e. a Maiorana–McFarland function
(without an extra offset). In the original coordinates it is linearly
equivalent to this form, hence is in the completed class
\(\mathcal M^\#\).

The argument also gives the signed Walsh spectrum in the original
variables. For \(a,d\in E\), use the character
\((-1)^{\operatorname{Tr}(ax+dy)}\). The change of coordinates has
\(\operatorname{Tr}(a y^{q^4})=\operatorname{Tr}(a^{q^2}y)\);
the sum over \(y\) is zero unless
\(\psi(z)=d+a^{q^2}\), in which case it is \(q^6\). Hence
\[
 W_f(a,d)=q^6\,(-1)^{\,\operatorname{Tr}
                  (a\psi^{-1}(d+a^{q^2}))}.
 \tag{5}
\]
This verifies bentness directly and supplies its dual Boolean function
in the original trace coordinates. It also resolves the
\(\mathcal M^\#\) column for Conjecture 2 in Table I of the source:
the family is inside, rather than a candidate for new functions
outside \(\mathcal M^\#\).

## Reproduction and prior scope

    python3 verify_symbolic.py
    g++ -O3 -std=c++17 -Wall -Wextra verify_finite.cpp -o /tmp/llhq-verify
    /tmp/llhq-verify

The symbolic script expands all formal six-cycle Frobenius translates
of the original and sheared polynomials, checks the matrix products,
and rejects a changed shear and changed exponent. The independent C++
script checks irreducibility of its binary field moduli, exhausts
\(\psi\) for \(k=1,2,3\), directly verifies (3) for all \(b\) in the
base field in those examples, and checks the original truth table and
every signed Walsh coefficient for \(k=1,2\), including 16,777,216
entries at \(k=2\). It also tests a changed \(y\)-exponent and the
vanishing denominator caused by removing the constant \(1\).
These are checks, not restrictions on the analytic proof.

The original Conjecture 2 cites finite confirmation through \(m=12\);
the theorem above is uniform in \(k\). Kaimin Cheng's
[arXiv:2603.28491](https://arxiv.org/abs/2603.28491) concerns
Conjecture **1** of the same 2023 paper, a different family built
from the inverse of a permutation on a quadratic extension.
[Daniele Bartoli and Marco Timpanella, DCC (2026)](https://doi.org/10.1007/s10623-026-01815-z)
study a different relative-trace composition family from the 2023 paper,
not this two-variable trace cubic. Ding–Zieve gives the permutation
ingredient as explained above; it does not identify (1), which joins
that ingredient to the specific bentness conjecture. Searches through
2026-11-27 by the JCTA title/DOI, conjecture number, sparse exponents,
and the completed Maiorana–McFarland class did not locate an earlier
source proving (1) or answering Conjecture 2. This is a literature
search result, not an absolute priority guarantee.
