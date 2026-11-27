# Cubic restrictions with quadratic degree or high second-derivative entropy

All vector spaces in this note are over \(\mathbb F_2\); all logarithms
have base two. For a finite set \(A\), \(U_A\) is uniform on \(A\).
A direction pair \((a,b)\) is independent if \(a,b\) are linearly
independent; in characteristic two this means \(a,b\ne0\) and \(a\ne b\).

## 1. Precise statement

For \(m\ge16\), define the integers and density parameters
\[
 \begin{split}
 \delta&=2^{-2m-3},\quad \alpha_0=\delta/2=2^{-2m-4},\quad
 j_m=\left\lfloor(\log m)/4\right\rfloor,\quad \theta=2^{-j_m},\\
 h&=2+2\left\lceil\frac{2m+5}{2j_m}\right\rceil,\qquad
 B_0=2\cdot 2^{2j_m}(2m+4),\\
 L_m&=(2m+4)+m(B_0+1)+h(m-1)\binom m2.
 \end{split}
\]
Here \(h\) is even and \(j_m\ge1\). Since
\(j_m=\Theta(\log m)\) and \(2^{2j_m}\le\sqrt m\), we have
\(h=O(m/\log m)\), \(B_0=O(m^{3/2})\), and
\(L_m=O(m^4/\log m)\). For an explicit upper bound, for \(m\ge16\)
we have \(j_m\ge(\log m)/8\) and \(\log m\le m/4\). Hence
\(h\le4+(2m+5)/j_m\le20m/\log m\) and
\(B_0\le(9/2)m^{3/2}\). Bounding the three terms of \(L_m\)
by \(m^4/\log m\), \(5m^4/\log m\), and \(10m^4/\log m\),
respectively, gives \(L_m\le16m^4/\log m\).
Let \(f:\mathbb F_2^s\to\mathbb F_2^n\) have total degree at most
three in squarefree algebraic normal form.

**Structural theorem.** If \(s\ge L_m\), every chosen linear subspace
of dimension \(L_m\) in the domain contains an \(m\)-dimensional
linear subspace \(W\) with one of these two properties, simultaneous
over every coset \(u+W\) in the entire domain:

1. The map \(g_u(w)=f(u+w)\) on \(W\) has degree at most two.
2. For every linearly independent \(a,b\in W\),
   \(H_\infty(\Delta_a\Delta_b g_u(U_W))\ge\lfloor m/2\rfloor\).

If \(f\) is injective, its distribution on uniform input is
exactly the mixture over all cosets of such a \(W\). In that mixture
every restriction is injective with output min-entropy \(m\).
More generally, let \(k=H_\infty(f(U_{\mathbb F_2^s}))\) (a lower
bound on this entropy also suffices) and \(0<\epsilon<1\).
If \(k\ge L_m+m+\log(1/\epsilon)\), one can choose \(W\) so that
a fraction at least \(1-\epsilon\) of its cosets have injective
restrictions. The uniform-input source is hence \(\epsilon\)-close
in total variation to the convex combination over these good cosets,
all of the same alternative and each of output min-entropy \(m\).
These statements are independent of the output length.

For clarity, this is a decomposition into affine restrictions in the
original generating variables. It does not require giving a procedure
to find those restrictions efficiently from a polynomial description,
and it does not assert that every restriction of a noninjective map
will be injective. The approximate part is not claimed exact for
arbitrary noninjective sources.

## 2. Polarisation and compression of rare bad pairs

Write \(\Delta_a f(x)=f(x+a)+f(x)\).
The third derivative \(T(a,b,c)=\Delta_a\Delta_b\Delta_c f(x)\)
is independent of \(x\) and is trilinear, symmetric and alternating.
Indeed, for a squarefree cubic monomial indexed by \(i,j,k\) it is
the sum of the six products using \(a,b,c\) once each on \(i,j,k\);
monomials of lower degree give zero. Alternatively, two equal
directions give zero because \(\Delta_a^2=0\) over \(\mathbb F_2\).
For any linear \(V\) and any shift \(u\), the second derivative on
\(u+V\) is affine in its argument with linear part
\(x\mapsto T(a,b,x)\) for \(a,b,x\in V\).
An affine image of a uniform point is uniform on an affine space
of size \(2^{\operatorname{rank}}\), so second-derivative min-entropy
equals this linear rank. The restriction \(f|_{u+W}\) has degree at
most two exactly when \(T\) vanishes on \(W^3\); the coefficient of
a squarefree cubic in coordinates for a basis of \(W\) is the value
of \(T\) on the corresponding triple of basis vectors.

**Rare-pair lemma.** Let \(\dim V=n_V\ge 2m+4\), \(m\ge16\).
Assume
\[
 \Pr_{a,b\ \mathrm{i.i.d.}\ U_V}
       [\operatorname{rank}(T(a,b,\cdot)|_V)<m]\le\delta.
 \tag{1}
\]
Then an \(m\)-dimensional \(W\subseteq V\) satisfies
\(\operatorname{rank}(T(a,b,\cdot)|_W)\ge s_*=\lfloor m/2\rfloor\)
for every independent \(a,b\in W\).

To prove it, choose a random linear map \(\phi:\mathbb F_2^m\to V\)
by taking independent uniform images of the basis. The probability
it is not injective is at most \((2^m-1)2^{-n_V}<2^{-m-4}\).
For each fixed ordered independent pair \(a,b\) in its domain,
\((\phi a,\phi b)\) is an independent sample of two uniform points
(in the statistical sense; linear dependence is allowed before
the injection check). The chance its ambient contraction has rank
less than \(m\) is at most \(\delta\), by (1).
Condition on any good pair of images. Complete \(a,b\) to a basis
of the domain. The other \(m-2\) images remain uniform and mutually
independent, also independent of the conditioned pair. Their
contractions are independent uniform vectors of an image space of
dimension \(r\ge m\). The first two contracted images are zero
by alternation.

If those \(m-2\) vectors span a space of dimension below \(s_*\),
some set of \(s_*-1\) indices spans all the vectors (pad a smaller
spanning set if needed). For each such set, conditional on the
vectors on those indices, the probability that the remaining
\(m-s_*-1\) independent uniform vectors fall in their span is at most
\(2^{-(r-s_*+1)(m-s_*-1)}\).
A union bound over choices gives probability at most
\[
 2^{m-2}\,2^{-(m-s_*+1)(m-s_*-1)}
 \le 2^{m-2-(4m-1)}=2^{-3m-1}.
\]
This uses \((m-s_*+1)(m-s_*-1)\ge m^2/4-1\ge 4m-1\).
There are fewer than \(2^{2m}\) independent domain pairs. Thus the
total excluded probability is at most
\(2^{-m-4}+1/8+2^{-m-1}<1\), proving the lemma.

## 3. An iterated-sum lemma and dense rows

**Iterated-sum lemma.** In any finite binary vector space \(V\),
let \(S\) have density \(\alpha>0\). Take \(0<\theta<1\) and an
even integer \(h\ge2\) with \(\theta^{h-2}<\alpha\). Then \(hS\)
(the sums of \(h\) elements, repetition allowed) contains a linear
subspace of codimension at most \(2\theta^{-2}\log(1/\alpha)\).

Here is the elementary Fourier proof, including the spectrum
estimate. Put \(G=1_S/\alpha\) and use expectation-normalised
Fourier coefficients \(\widehat G(\xi)=\mathbb E_{x\in V}G(x)(-1)^{\xi(x)}\).
If \(d\) linearly independent characters have coefficient magnitude
at least \(\theta\), their joint evaluation on \(U_S\) has
min-entropy at least \(d-\log(1/\alpha)\), since a fiber of the
surjective linear evaluation map has size \(|V|2^{-d}\).
Its Shannon entropy is at least its min-entropy, and subadditivity
bounds it above by \(d\,h_2((1+\theta)/2)\); here \(h_2\) is the
binary entropy. The entropy deficit
\(1-h_2((1+\theta)/2)\) is at least \(\theta^2/2\):
its derivative at \(\theta=u\) is \(\operatorname{artanh}(u)/\ln2\ge u\).
Thus \(d\le2\theta^{-2}\log(1/\alpha)\). This is the standard
entropic proof of Chang's large-spectrum bound.

Let \(V'\) be the common kernel of all large characters.
All of them are \(+1\) in the character representation at
\(v\in V'\); the zero character contributes \(1\) to
\(G^{*h}(v)\), with convolution also expectation-normalised.
The other large characters contribute nonnegatively since \(h\)
is even. By Parseval the absolute contribution of the small
characters is at most
\(\theta^{h-2}\sum_\xi|\widehat G(\xi)|^2
=\theta^{h-2}/\alpha<1\).
Therefore \(G^{*h}(v)>0\) on \(V'\), implying \(V'\subset hS\).
For \(\alpha\ge\alpha_0\) and the chosen \(\theta,h\),
\(\theta^{h-2}\le 2^{-2m-5}=\alpha_0/2\), and the codimension
is at most \(B_0\).

### Dense-row induction

Work inside the chosen \(L_m\)-dimensional input space \(V_0\).
Maintain a subspace \(A_j\) with basis \(a_1,\ldots,a_j\) and a
residual subspace \(V_j\), with \(A_j\cap V_j=0\), such that
\[
 T(A_j,A_j,A_j)=0,\qquad T(A_j,A_j,V_j)=0,\qquad
 \operatorname{rank}(T(a_i,b,\cdot)|_{V_j})\le h(m-1)
 \quad (b\in V_j,\ i\le j).
 \tag{2}
\]
Start with \(A_0=0\). All residual spaces will have dimension at
least \(2m+4\). At stage \(j<m\), test (1) on \(V_j\).
If it holds, the rare-pair lemma gives the promised high-derivative
space immediately. Otherwise let
\(S_a=\{b\in V_j:\operatorname{rank}(T(a,b,\cdot)|_{V_j})<m\}\).
The average density of \(S_a\) over \(a\in V_j\) is \(>\delta\).
The zero row \(a=0\) contributes \(2^{-\dim V_j}\le\delta/2\)
to this average. Hence there is a nonzero \(a\in V_j\) with
\(|S_a|/|V_j|\ge\delta/2\).

Choose \(V'\subseteq hS_a\) with codimension at most
\(B_0\) in \(V_j\). For any \(b\in V'\), write \(b\) as the
sum of \(h\) elements of \(S_a\). Linearity of \(T\) and rank
subadditivity give
\(\operatorname{rank}(T(a,b,\cdot)|_{V_j})\le h(m-1)\).
Now intersect \(V'\) with the kernels of \(T(a_i,a,\cdot)|_{V_j}\)
for all \(i\le j\), and with a hyperplane of \(V_j\) not containing
\(a\). Each kernel costs codimension at most \(h(m-1)\) by (2)
with the **old** residual \(V_j\). Call the intersection \(V_{j+1}\);
put \(a_{j+1}=a\) and \(A_{j+1}=A_j+\langle a\rangle\).
The sum is direct since \(a\in V_j\) and \(A_j\cap V_j=0\).
Further \(A_{j+1}\cap V_{j+1}=0\) because \(V_{j+1}\subset V_j\)
and excludes \(a\). The old pair identities on \(V_{j+1}\) hold by
restriction and the new old/new identities hold by the kernel
cuts. The identities on \(A_{j+1}^3\) follow from the previous
identities on \(A_j^3\), \(T(A_j,A_j,V_j)=0\) as \(a\in V_j\),
and alternation for repeated \(a\). Old and new rank bounds hold
by restriction and the \(hS_a\) property, respectively. This
proves (2) inductively.

The codimension cost at step \(j\) is at most
\(B_0+h(m-1)j+1\). Therefore the chosen \(L_m\) leaves
dimension at least \(2m+4\) even after all \(m\) steps, justifying
all prior tests. If the process has not stopped by then,
\(W=A_m\) has dimension \(m\) and \(T(W,W,W)=0\), furnishing
the degree-at-most-two alternative. The argument uses \(T\) only,
so \(W\) works for every affine translate and depends neither on the
lower-degree coefficients nor on the choice of the translate.

There is also a spectator-variable form: if \(f(y,z)\) has total
degree at most three and the above construction is performed only in
the \(y\)-space, the restricted third derivative in the \(y\)
directions is independent of both \(y\) and \(z\). Thus one \(W\) in
the \(y\)-space satisfies the same structural alternative for all
fixed \(z\) and \(y\)-cosets. This statement does not claim a bound
on min-entropy of restrictions with arbitrary correlated spectator
variables left random.

## 4. Input collision isolation and the resulting mixture

For injective \(f\), all cosets are immediately good. For general \(f\),
entropy \(k\) implies that every output fiber has size at most
\(2^{s-k}\) and that \(s\ge k\). Under the theorem's assumption one
can choose a uniform \(L_m\)-dimensional subspace \(V_0\).
For each domain point \(x\), the probability (over \(V_0\)) that
\(x\) shares its output with another point of \(x+V_0\) is at most
\[
 (2^{s-k}-1)\frac{2^{L_m}-1}{2^s-1}\;\le\; 2^{L_m-k}.
 \tag{3}
\]
Here each nonzero difference has inclusion probability
\((2^{L_m}-1)/(2^s-1)\) by transitivity and the number of nonzero
vectors in \(V_0\); the last inequality follows from \(L_m\le s\).
By averaging, some single \(V_0\) has at most a \(2^{L_m-k}\)
fraction of such bad points over the full domain.
Choose \(W\subset V_0\) from §3. Each \(W\)-coset on which \(f\)
is not injective contains at least one of those bad points because
it is contained in a \(V_0\)-coset. Since all \(W\)-cosets have
size \(2^m\), the fraction of noninjective cosets is at most
\(2^{L_m+m-k}\le\epsilon\).
Condition the uniform input on the remaining cosets. The input total
variation distance is the discarded mass, and applying \(f\) cannot
increase it. Each retained restriction is injective, so each
output law is uniform on \(2^m\) outputs, although supports for
different cosets may overlap.

For fixed \(\epsilon\), the admissible \(m\) grows as
\(\Omega((k\log k)^{1/4})\), by \(L_m=O(m^4/\log m)\).
The same order holds whenever \(\log(1/\epsilon)\) is bounded by a
fixed fraction below one of \(k\). In particular the dependence on
the chosen approximation error is additive in the entropy
hypothesis. No step requires a rank-combiner construction or shows
that the problem for degree four and higher is solved.
