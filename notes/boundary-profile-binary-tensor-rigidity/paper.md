# Boundary profiles and a stronger asymptotic lower bound for binary tensor rigidity

Research note, 7 October 2026. This is an additive continuation of
notes/sharp-binary-tensor-rigidity. It proves a general boundary-profile
limit theorem and uses one explicit three-term profile to improve the known
lower bound for the sharp binary rigidity constants. Numerical optimization
was used only to discover the displayed rational coefficients; the stated
constant is certified by exact rational arithmetic.

## 1. Setting and result

For a real fully symmetric order-\(p\) tensor \(T\) on \(\mathbb R^2\), write
\(t_k\) for an entry with exactly \(k\) indices equal to \(2\), and use

\[
 \|T\|_F^2=\sum_{k=0}^p\binom pk t_k^2,\qquad
 f_T(x,y)=\sum_{k=0}^p\binom pk t_kx^{p-k}y^k.
\]

Let \(\mathcal D_{2,p}\) be the real orthogonally decomposable class
\(a u^{\otimes p}+b v^{\otimes p}\), where \((u,v)\) is orthonormal, and put

\[
 d_p(T)=\operatorname{dist}_F(T,\mathcal D_{2,p}).
\]

For every ordered \((p-2)\)-tuple \(\alpha\in\{1,2\}^{p-2}\), let
\(X_\alpha=(T_{\alpha,i,j})_{i,j=1}^2\), and define

\[
 R_p(T)^2=\sum_{\alpha,\beta}\|[X_\alpha,X_\beta]\|_F^2.
\]

The best constant in

\[
 d_p(T)\le C_p\sqrt{R_p(T)}
\]

is denoted \(C_p\). The preceding note proved

\[
 2^{-3/4}\le \liminf_{p\to\infty}\frac{C_p}{p^{1/4}}
 \le \limsup_{p\to\infty}\frac{C_p}{p^{1/4}}\le2^{-1/2}.
\]

The new result is the following.

**Theorem A (finite boundary-profile limit).**
Fix \(m\ge1\) and real \(a_0,\ldots,a_m\). Put

\[
 S=\sum_{k=0}^m a_k^2,\qquad
 M_1=\sum_{k=1}^m k\,a_k^2,
\qquad
 A(x)=\sum_{k=0}^m\frac{a_k}{\sqrt{k!}}x^k.
\]

Assume \(S>0\) and \(M_1>0\). For \(p>2m+2\), define a symmetric binary
tensor \(T_p(a)\) by

\[
 t_k=t_{p-k}=\frac{a_k}{\sqrt{\binom pk}}\quad(0\le k\le m),
 \qquad t_j=0\quad(m<j<p-m).
\]

Then

\[
 \|T_p(a)\|_F^2=2S,
\]

\[
 \sqrt p\,R_p(T_p(a))\longrightarrow4\sqrt{SM_1},
\]

and

\[
 d_p(T_p(a))^2\longrightarrow
 2S-\mathcal M(a),
\]

where

\[
 \mathcal M(a)=
 \sup_{x\in\mathbb R}e^{-x^2}\bigl(A(x)^2+A(-x)^2\bigr).
\]

Consequently

\[
 \boxed{\displaystyle
 \liminf_{p\to\infty}\frac{C_p^2}{\sqrt p}\ge
 \frac{2S-\mathcal M(a)}{4\sqrt{SM_1}} }
 \tag{1}
\]

whenever \(2S>\mathcal M(a)\).

Thus every finite vector \(a\) gives a rigorous variational lower bound.
The former two-boundary-coefficient family is the special case \(m=1\).

**Corollary B (explicit improvement).**
Take

\[
 a_0=1,\qquad
 a_1=\frac{4627}{3125},\qquad
 a_2=-\frac{58\sqrt2}{125}.
\]

Then

\[
 \boxed{\displaystyle
 \liminf_{p\to\infty}\frac{C_p}{p^{1/4}}>0.623586.}
 \tag{2}
\]

This strictly improves the previous \(2^{-3/4}=0.59460\ldots\) lower
constant. The upper constant \(2^{-1/2}\) is unchanged, so (2) does not
determine the sharp asymptotic constant.

## 2. The residual for a reflected boundary profile

For any binary tensor define

\[
 z_k=\binom{t_k-t_{k+2}}{2t_{k+1}},\qquad
 G(T)=\sum_{k=0}^{p-2}\binom{p-2}{k}z_kz_k^\top.
\]

The preceding note proved the exact identity

\[
 R_p(T)^2=\det G(T).
 \tag{3}
\]

Our profile satisfies \(t_k=t_{p-k}\). Pairing the \(k\)-term of the
off-diagonal entry of \(G\) with the \((p-2-k)\)-term gives

\[
 (t_{p-2-k}-t_{p-k})t_{p-1-k}
 =-(t_k-t_{k+2})t_{k+1}.
\]

The binomial weights agree. A possible central term has
\(t_k=t_{k+2}\). Hence

\[
 G_{12}(T_p(a))=0
 \tag{4}
\]

exactly.

For the second diagonal entry, put \(j=k+1\) and use

\[
 \frac{\binom{p-2}{j-1}}{\binom pj}
 =\frac{j(p-j)}{p(p-1)}.
\]

The two reflected boundary blocks therefore give the exact formula

\[
 G_{22}(T_p(a))
 =8\sum_{j=1}^m
 \frac{j(p-j)}{p(p-1)}a_j^2,
 \tag{5}
\]

so

\[
 pG_{22}(T_p(a))\longrightarrow8M_1.
 \tag{6}
\]

Because \(p>2m+2\), the two boundary blocks do not interact. Pairing the
first diagonal entry in the same way gives

\[
 G_{11}(T_p(a))
 =2\sum_{k=0}^m\binom{p-2}{k}
 \left(
 \frac{a_k}{\sqrt{\binom pk}}
 -\mathbf 1_{k+2\le m}
 \frac{a_{k+2}}{\sqrt{\binom p{k+2}}}
 \right)^2.
 \tag{7}
\]

For fixed \(k\),

\[
 \frac{\binom{p-2}{k}}{\binom pk}
 =\frac{(p-k)(p-k-1)}{p(p-1)}\to1,
\]

whereas the cross term in (7) is \(O(p^{-1})\) and the
\(a_{k+2}^2\)-term is \(O(p^{-2})\). Since \(m\) is fixed,

\[
 G_{11}(T_p(a))\longrightarrow2S.
 \tag{8}
\]

Equations (3), (4), (6) and (8) prove

\[
 \sqrt p\,R_p(T_p(a))\longrightarrow4\sqrt{SM_1}.
 \tag{9}
\]

Finally the supports \(0,\ldots,m\) and \(p-m,\ldots,p\) are disjoint, so

\[
 \|T_p(a)\|_F^2=2\sum_{k=0}^m a_k^2=2S.
 \tag{10}
\]

## 3. Projection energy and the Gaussian boundary scale

For \(c=\cos\theta\), \(s=\sin\theta\),

\[
 f_{T_p(a)}(c,s)
 =\sum_{k=0}^m a_k\sqrt{\binom pk}
 \bigl(c^{p-k}s^k+c^ks^{p-k}\bigr).
 \tag{11}
\]

The exact projection formula from the preceding note is

\[
 d_p(T)^2=\|T\|_F^2-
 \max_\theta
 \{f_T(\cos\theta,\sin\theta)^2+
 f_T(-\sin\theta,\cos\theta)^2\}.
 \tag{12}
\]

For every tensor, the expression in braces is \(\pi/2\)-periodic:
shifting \(\theta\) by \(\pi/2\) only swaps the two basis vectors, up to
signs that disappear after squaring. It is therefore enough to maximize over
\(-\pi/4\le\theta\le\pi/4\). This reduction uses no additional reflection
symmetry of the tensor.

Set \(\theta=x/\sqrt p\) with \(x\in\mathbb R\) fixed. For each fixed \(k\),

\[
 \sqrt{\binom pk}\,
 (\cos(x/\sqrt p))^{p-k}
 (\sin(x/\sqrt p))^k
 \longrightarrow
 e^{-x^2/2}\frac{x^k}{\sqrt{k!}}.
 \tag{13}
\]

The reflected term containing
\((\sin(x/\sqrt p))^{p-k}\) tends to zero. Replacing the first coordinate
by \(-\sin\theta\) multiplies the surviving \(k\)-th boundary term by
\((-1)^k\). Hence the projection energy at \(\theta=x/\sqrt p\) tends to

\[
 e^{-x^2}\bigl(A(x)^2+A(-x)^2\bigr).
 \tag{14}
\]

It remains to justify passage of the maximum through the limit. Let
\(\theta_p\in[0,\pi/4]\) be any sequence and put
\(x_p=\sqrt p\,\theta_p\).

If \(x_p\) is bounded, every convergent subsequence is covered by the
uniform-on-compact version of (13), so its limiting projection energy is
bounded by \(\mathcal M(a)\).

If \(|x_p|\to\infty\), use

\[
 \sqrt{\binom pk}\le\frac{p^{k/2}}{\sqrt{k!}},
 \qquad |\sin\theta|\le|\theta|,\qquad
 \cos\theta\le e^{-\theta^2/2}
 \quad (|\theta|\le\pi/4).
\]

For \(p\ge2m\), every boundary term containing
\(\cos^{p-k}\theta\,\sin^k\theta\) in absolute value is bounded by

\[
 \frac{|x_p|^k}{\sqrt{k!}}e^{-x_p^2/4},
\]

which tends to zero. Every companion term containing
\(|\sin\theta|^{p-k}\cos^k\theta\) is at most a fixed polynomial in
\(p\) times \(2^{-(p-m)/2}\), hence also tends to zero. These two
estimates apply to both members of the orthonormal basis. Therefore the
projection energy tends to zero.

For the reverse inequality, evaluating at \(\theta=x/\sqrt p\) for any
fixed \(x\) and then taking the supremum gives the corresponding
\(\liminf\) bound. Together with the preceding subsequence argument this
proves

\[
 \max_\theta P_p(\theta)\longrightarrow\mathcal M(a).
 \tag{15}
\]

Combining (10), (12), and (15) proves the distance assertion in Theorem A.
Dividing by (9), and using
\(C_p^2\ge d_p(T_p(a))^2/R_p(T_p(a))\), proves (1).

## 4. Exact three-term certificate

Write

\[
 b=\frac{4627}{3125},\qquad d=-\frac{58}{125}.
\]

For the corollary,

\[
 A(x)=1+bx+dx^2.
\]

Put \(y=x^2\). Then

\[
 A(x)^2+A(-x)^2
 =2\bigl(1+By+Cy^2\bigr),
\]

with the rational constants

\[
 B=2d+b^2=\frac{12346629}{9765625},\qquad
 C=d^2=\frac{3364}{15625}.
\]

Thus

\[
 \mathcal M(a)=
 \max_{y\ge0}2e^{-y}(1+By+Cy^2).
 \tag{16}
\]

The derivative has the sign of

\[
 q(y)=(B-1)+(2C-B)y-Cy^2.
 \tag{17}
\]

Here \(B>1\), \(C>0\), and \(2C-B<0\), so \(q\) is strictly decreasing
on \([0,\infty)\) and has exactly one positive zero \(y_*\). Exact
fraction arithmetic gives

\[
 \frac{1473}{5000}<y_*<
 \frac{29461}{100000}.
 \tag{18}
\]

Since \(1+By+Cy^2\) is increasing,

\[
 \mathcal M(a)
 <2e^{-1473/5000}
 \left(
 1+B\frac{29461}{100000}
 +C\left(\frac{29461}{100000}\right)^2
 \right).
 \tag{19}
\]

For \(0<L<1\), the degree-ten alternating Taylor polynomial is an upper
bound for \(e^{-L}\). Substituting \(L=1473/5000\) in (19) gives a fully
rational upper bound.

For this profile

\[
 S=1+b^2+2d^2=\frac{35379754}{9765625},
\qquad
 M_1=b^2+4d^2=\frac{29819129}{9765625}.
 \tag{20}
\]

The checker verifies exactly, after inserting the rational upper bound
from (19), that

\[
 \left(
 \frac{2S-\mathcal M_{\rm upper}}{4\sqrt{SM_1}}
 \right)^{1/2}
 >
 \frac{311793}{500000}=0.623586.
\]

It removes the remaining square roots by squaring positive quantities;
no floating-point comparison is used. Equations (1) and (20) prove
Corollary B.

## 5. Scope and next question

Theorem A is a reusable asymptotic lower-bound mechanism, not merely one
numerical witness. It converts any finite boundary coefficient profile
into a one-variable Gaussian/Fock-type extremal problem. The explicit
three-term profile captures a stronger obstruction than the former
two-term family.

This note does not prove that finite boundary profiles contain all
asymptotic extremizers, does not determine the supremum of the profile
variational problem, and does not improve the existing upper constant
\(2^{-1/2}\). A natural next problem is to analyze

\[
 \sup_a
 \frac{2S-\sup_x e^{-x^2}(A(x)^2+A(-x)^2)}
      {4\sqrt{SM_1}}
\]

over finite or square-summable profiles and to prove whether every
near-extremal tensor concentrates on this boundary scale.

No priority or first-discovery claim is made. The qualitative ODeCo
literature and the literature comparison of the parent note remain the
relevant background.
