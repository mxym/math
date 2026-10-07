# An improved two-band lower family for binary tensor rigidity

**Research note, 7 October 2026.**

This note gives a closed-form strengthening of the lower bound in the binary
complete-commutator rigidity problem.  The proof is self-contained at the
level needed for the new result.  The notation agrees with the companion
paper on sharp binary tensor rigidity.

## 1. Setup and statement

Let \(T\) be a real fully symmetric order-\(p\) tensor on \(\mathbb R^2\).
Write \(t_k\) for an entry with exactly \(k\) indices equal to \(2\), and put

\[
 \|T\|_F^2=\sum_{k=0}^p\binom pk t_k^2,\qquad
 f_T(x,y)=\sum_{k=0}^p\binom pk t_k x^{p-k}y^k .
\]

Let \(\mathcal D_{2,p}\) be the set of tensors
\(a u^{\otimes p}+b v^{\otimes p}\), where \((u,v)\) is an orthonormal basis
and \(a,b\in\mathbb R\), and write

\[
 d_p(T)=\operatorname{dist}_F(T,\mathcal D_{2,p}).
\]

For each ordered \((p-2)\)-tuple \(\alpha\in\{1,2\}^{p-2}\), let
\((X_\alpha)_{ij}=T_{\alpha,i,j}\), and define the complete commutator
residual by

\[
 R_p(T)^2=
 \sum_{\alpha,\beta\in\{1,2\}^{p-2}}
       \|[X_\alpha,X_\beta]\|_F^2.
\]

Thus \(R_p\) is homogeneous of degree two in \(T\).  Let \(C_p\) denote the
best constant in

\[
 d_p(T)\le C_p\sqrt{R_p(T)}
\]

over all real symmetric order-\(p\) binary tensors.

Set \(s=\sqrt2\).  For every \(p\ge10\), define \(U_p\) by

\[
 t_0=t_p=1,\qquad
 t_1=t_{p-1}=\frac{\sqrt{p+s(p-1)}}{p},\qquad
 t_2=t_{p-2}=-\frac{s}{p},
\]
with every remaining \(t_k=0\).

Define

\[
 \begin{aligned}
 M_p&=(2+s)p-(1+s),\\
 P_p&=(3+s)p^2-(7+s)p+(8+2s),\\
 Q_p&=(3+s)p-(4+s).
 \end{aligned}
\]

**Theorem 1 (exact two-band witness).**  For every integer \(p\ge10\),

\[
 \max_{x^2+y^2=1}
 \left(f_{U_p}(x,y)^2+f_{U_p}(-y,x)^2\right)=2,
\]

and consequently

\[
 d_p(U_p)^2=\frac{2M_p}{p}.
\]

For the complete ordered contraction residual,

\[
 R_p(U_p)^2=A_pB_p,
\qquad
 A_p=\frac{2P_p}{p^2},\qquad
 B_p=\frac{8Q_p}{p^2}.
\]

In particular,

\[
 \boxed{\quad
 C_p^2\ge
 \frac{pM_p}{2\sqrt{P_pQ_p}}
 \quad}\qquad(p\ge10).
\]

**Corollary 2 (improved asymptotic lower constant).**

\[
 \boxed{\quad
 \liminf_{p\to\infty}\frac{C_p}{p^{1/4}}
 \ge
 \kappa:=
 \sqrt{\frac{2+\sqrt2}{2(3+\sqrt2)}}
 =
 \sqrt{\frac27+\frac{\sqrt2}{14}}
 \quad}.
\]

Moreover \(\kappa>2^{-3/4}\).  Combining this with the previously proved
binary upper bound gives

\[
 \kappa
 \le \liminf_{p\to\infty}\frac{C_p}{p^{1/4}}
 \le \limsup_{p\to\infty}\frac{C_p}{p^{1/4}}
 \le 2^{-1/2}.
\]

The existence of the limit and its exact value remain open in this note.

## 2. Two elementary identities

We record the two identities used below.

**Lemma 3 (projection distance).**  For every real symmetric binary tensor,

\[
 d_p(T)^2=\|T\|_F^2-
 \max_{x^2+y^2=1}
 \left(f_T(x,y)^2+f_T(-y,x)^2\right).
\]

**Proof.**
For a fixed orthonormal basis \(u=(x,y)\), \(v=(-y,x)\), the tensors
\(u^{\otimes p}\) and \(v^{\otimes p}\) are orthonormal in Frobenius norm.
Orthogonal projection onto their span therefore has squared norm
\(f_T(u)^2+f_T(v)^2\).  Minimizing over the two scalar weights and then over
the compact set of orthonormal bases proves the formula. \(\square\)

For \(0\le k\le p-2\), put \(w_k=\binom{p-2}k\) and

\[
 z_k=(t_k-t_{k+2},\,2t_{k+1})^\top,\qquad
 G(T)=\sum_{k=0}^{p-2}w_k z_kz_k^\top .
\]

**Lemma 4 (binary Gram determinant).**

\[
 R_p(T)^2=\det G(T).
\]

**Proof.**
A contraction with \(k\) entries equal to \(2\) is

\[
 X_k=\begin{pmatrix}t_k&t_{k+1}\\t_{k+1}&t_{k+2}\end{pmatrix}
\]

and occurs \(w_k\) times among ordered contractions.  The off-diagonal
entry of \([X_k,X_l]\) is

\[
 c_{kl}
 =(t_k-t_{k+2})t_{l+1}
 -(t_l-t_{l+2})t_{k+1}
 =\frac12\det(z_k,z_l).
\]

Hence

\[
 R_p(T)^2
 =2\sum_{k,l}w_kw_lc_{kl}^2
 =\frac12\sum_{k,l}w_kw_l\det(z_k,z_l)^2
 =\det G(T),
\]

where the last identity is the two-dimensional Binet--Cauchy expansion.
\(\square\)

## 3. Exact projection maximum

Write

\[
 r=\frac{\sqrt{p+s(p-1)}}p,\qquad
 c_1=pr=\sqrt{p+s(p-1)},\qquad
 c_2=\binom p2\left(-\frac{s}{p}\right)
     =-\frac{s(p-1)}2 .
\]

The choice of the two boundary bands is arranged so that

\[
 \boxed{\,c_1^2+2c_2=p\,}. \tag{3.1}
\]

Also

\[
 c_2^2=\frac{(p-1)^2}{2}\le\binom p2. \tag{3.2}
\]

We prove the projection maximum separately by parity.

### 3.1 Even orders

Let \(p=2n\ge10\), put \(a=x^2\), \(b=y^2\), so \(a,b\ge0\) and
\(a+b=1\).  Write

\[
 \begin{aligned}
 U&=a^n+b^n+c_2(a^{n-1}b+ab^{n-1}),\\
 V&=c_1xy(a^{n-1}+b^{n-1}).
 \end{aligned}
\]

Direct substitution gives

\[
 f_{U_p}(x,y)=U+V,\qquad
 f_{U_p}(-y,x)=U-V,
\]
and hence
\[
 \frac12\left(f_{U_p}(x,y)^2+f_{U_p}(-y,x)^2\right)
 =U^2+V^2. \tag{3.3}
\]

The right side is a homogeneous polynomial of degree \(p\) in \(a,b\).
Because \(p\ge10\), all exceptional coefficient positions below are
distinct.  Its nonzero coefficients, indexed by the exponent \(k\) of
\(b\), are

\[
\begin{array}{c|c}
k & [a^{p-k}b^k](U^2+V^2)\\ \hline
0,p & 1\\
1,p-1 & 2c_2+c_1^2=p\\
2,p-2 & c_2^2\\
n-1,n+1 & 2c_2\\
n & H_p:=2+2c_2^2+2c_1^2.
\end{array}
\]

By (3.2), the coefficients at \(2,p-2\) are at most
\(\binom p2\), and \(2c_2<0\).  For the central coefficient,

\[
 H_p=p^2+3+2s(p-1)<p^2+3p,
\]
because \(2s<3\).  Binomial coefficients increase up to the middle, so

\[
 \binom pn\ge\binom p4.
\]

For every \(p\ge10\),

\[
 \binom p4\ge p^2+3p, \tag{3.4}
\]
because after division by \(p>0\) this is
\[
 (p-1)(p-2)(p-3)\ge24(p+3).
\]
At \(p=10\) the two sides are \(504\) and \(312\), and when \(p\) is
increased by one their difference increases by
\(3(p-1)(p-2)-24>0\).

Thus every coefficient of \(U^2+V^2\) is at most the corresponding
coefficient of \((a+b)^p\).  Since \(a,b\ge0\),

\[
 U^2+V^2\le(a+b)^p=1.
\]

Equation (3.3) gives projection energy at most \(2\).

### 3.2 Odd orders

Let \(p=2n+1\ge11\).  Set

\[
 \begin{aligned}
 A&=x^p+c_2x^{p-2}y^2,&
 B&=c_1x^{p-1}y,\\
 C&=y^p+c_2x^2y^{p-2},&
 D&=c_1xy^{p-1}.
 \end{aligned}
\]

Then

\[
 f_{U_p}(x,y)=A+B+C+D,
\qquad
 f_{U_p}(-y,x)=A+D-B-C,
\]
so

\[
 \frac12\left(f_{U_p}(x,y)^2+f_{U_p}(-y,x)^2\right)
 =(A+D)^2+(B+C)^2. \tag{3.5}
\]

Writing again \(a=x^2,b=y^2\), the right side equals

\[
 \begin{aligned}
 &a^p+b^p
 +p(a^{p-1}b+ab^{p-1})
 +c_2^2(a^{p-2}b^2+a^2b^{p-2})\\
 &\qquad
 +2c_1(1+c_2)a^nb^n(a+b). \tag{3.6}
 \end{aligned}
\]

Here \(c_1>0\) and, because \(p\ge11\),

\[
 1+c_2=1-\frac{s(p-1)}2<0.
\]

The last line of (3.6) is therefore nonpositive.  By (3.2), the first line
is coefficientwise at most \((a+b)^p\).  Hence the right side of (3.5) is
at most \(1\), and again the projection energy is at most \(2\).

For either parity, the coordinate axes attain energy exactly \(2\).
This proves the first assertion of Theorem 1.

## 4. Distance and complete residual

The norm of \(U_p\) is

\[
 \begin{aligned}
 \|U_p\|_F^2
 &=2+2p r^2+2\binom p2\frac{2}{p^2}\\
 &=2+\frac{2[(2+s)p-(1+s)]}{p}
 =2+\frac{2M_p}{p}.
 \end{aligned}
\]

Lemma 3 and the exact projection maximum therefore give

\[
 d_p(U_p)^2=\frac{2M_p}{p}. \tag{4.1}
\]

We now compute the Gram matrix from Lemma 4.  Only the six boundary
coefficients are nonzero.  The off-diagonal entry cancels in four paired
terms: after factoring \(2r\), its bracket is

\[
 (1-t_2)+(p-2)t_2-(p-2)t_2+(t_2-1)=0.
\]

Thus \(G(U_p)\) is diagonal.  Its diagonal entries are

\[
 \begin{aligned}
 G_{11}
 &=2(1-t_2)^2+2(p-2)r^2
   +2\binom{p-2}{2}t_2^2\\
 &=\frac{2[(3+s)p^2-(7+s)p+(8+2s)]}{p^2}
 =\frac{2P_p}{p^2},\\[1ex]
 G_{22}
 &=8r^2+8(p-2)t_2^2\\
 &=\frac{8[(3+s)p-(4+s)]}{p^2}
 =\frac{8Q_p}{p^2}.
 \end{aligned}
\]

Both are positive.  Lemma 4 gives

\[
 R_p(U_p)=\sqrt{G_{11}G_{22}}
 =\frac{4\sqrt{P_pQ_p}}{p^2}. \tag{4.2}
\]

Since \(d_p(U_p)\le C_p\sqrt{R_p(U_p)}\), squaring and using
(4.1)--(4.2) yields

\[
 C_p^2\ge
 \frac{d_p(U_p)^2}{R_p(U_p)}
 =\frac{pM_p}{2\sqrt{P_pQ_p}},
\]
which proves Theorem 1.

## 5. Asymptotics and strict improvement

As \(p\to\infty\),

\[
 M_p\sim(2+s)p,\qquad
 P_p\sim(3+s)p^2,\qquad
 Q_p\sim(3+s)p.
\]

Therefore

\[
 \liminf_{p\to\infty}\frac{C_p^2}{\sqrt p}
 \ge\frac{2+s}{2(3+s)}
 =\frac27+\frac{s}{14}.
\]

Taking square roots proves Corollary 2.

The old one-band asymptotic lower constant is \(2^{-3/4}\), whose square
is \(1/(2s)\).  Since

\[
 \frac{2+s}{2(3+s)}>\frac1{2s}
 \quad\Longleftrightarrow\quad
 s(2+s)>3+s
 \quad\Longleftrightarrow\quad
 s>1,
\]

the improvement is strict.

For reference,

\[
 \kappa=0.6218758237538317\ldots,
 \qquad 2^{-3/4}=0.5946035575013605\ldots .
\]

The existing upper theorem gives
\(\limsup C_p/p^{1/4}\le2^{-1/2}\).  This note does not improve that upper
bound, prove convergence of the normalized constants, or classify all
asymptotic extremizing sequences.

## 6. Verification scope

The universal proof is Sections 2--5.  No finite computation is used to
deduce the theorem.

The standard-library checker in checks/check_exact.py works exactly in
\(\mathbb Q(\sqrt2)\).  It verifies the distance and Gram identities, the
boundary cancellation (3.1), all coefficient inequalities for every
\(10\le p\le120\), the base and monotonicity inequalities used in the
all-\(p\) proof, the asymptotic constant identity, its strict improvement
over the previous lower constant, and negative controls.  The finite order
loop is diagnostic; inequalities (3.2), (3.4), the parity arguments and the
closed-form algebra above establish the infinite range.

No numerical optimizer, floating-point sign decision, SAT/SMT assumption,
or unverified solver result enters the theorem.  The checker is not a
whole-paper formalization, and no external human peer review or novelty
certification is claimed.


## 7. Optimality within finite palindromic boundary-band witnesses

The two-band choice above is not merely locally convenient.  It is
asymptotically optimal in a broad class of finite-width boundary
constructions for which the coordinate axes remain locally maximizing
projection directions.

Fix \(m\ge2\).  For each sufficiently large \(p>2m+2\), let \(T^{(p)}\)
be a symmetric binary tensor satisfying

\[
 t_0=t_p=1,\qquad t_k=t_{p-k}\quad(1\le k\le m),
 \qquad t_k=0\quad(m<k<p-m),
\]
and suppose that for real numbers \(\gamma_1,\ldots,\gamma_m\),

\[
 t_k=\gamma_k\frac{\sqrt{k!}}{p^{k/2}}
      +o(p^{-k/2})
 \qquad(1\le k\le m). \tag{7.1}
\]

Assume that the coordinate axes are local maximizers of

\[
 \Phi_p(\theta)=
 f_{T^{(p)}}(\cos\theta,\sin\theta)^2+
 f_{T^{(p)}}(-\sin\theta,\cos\theta)^2
\]
for all sufficiently large \(p\).  Put

\[
 S=\sum_{k=1}^m\gamma_k^2,\qquad
 W=\sum_{k=1}^m k\gamma_k^2,
\]
and assume \(W>0\).

**Theorem 5 (finite-band mechanism is sharp).**
For every such family,

\[
 \limsup_{p\to\infty}
 p^{-1/4}\frac{d_p(T^{(p)})}{\sqrt{R_p(T^{(p)})}}
 \le
 \sqrt{\frac{2+\sqrt2}{2(3+\sqrt2)}}=\kappa. \tag{7.2}
\]

Equality in the profile optimization underlying (7.2) is possible only for

\[
 \gamma_1^2=1+\sqrt2,\qquad
 \gamma_2=-1,\qquad
 \gamma_k=0\quad(k\ge3). \tag{7.3}
\]

The tensors \(U_p\) of Theorem 1 have precisely this limiting profile and
attain (7.2).  Thus adding any fixed number of further palindromic boundary
bands cannot improve the asymptotic constant while staying in this
axis-locally-maximizing mechanism.

### 7.1 The necessary second-variation constraint

Only \(t_0,t_1,t_2\) and their palindromic partners enter the second
variation at the coordinate axes.  Write

\[
 c_1=pt_1,\qquad c_2=\binom p2t_2.
\]

At \(\theta=0\),

\[
 \begin{aligned}
 f(\cos\theta,\sin\theta)
 &=1+c_1\theta+(c_2-p/2)\theta^2+O(\theta^3),\\
 f(-\sin\theta,\cos\theta)
 &=1-c_1\theta+(c_2-p/2)\theta^2+O(\theta^3).
 \end{aligned}
\]

Therefore

\[
 \Phi_p''(0)=4(c_1^2+2c_2-p).
\]

Local maximality gives

\[
 p^2t_1^2+p(p-1)t_2\le p.
\]

Using (7.1) for \(k=1,2\) and passing to the limit yields the necessary
profile constraint

\[
 \boxed{\ \gamma_1^2+\sqrt2\,\gamma_2\le1.\ } \tag{7.4}
\]

The family \(U_p\) saturates the finite-\(p\) second-variation inequality
exactly.

### 7.2 Norm and Gram asymptotics

The fixed width in (7.1) gives, term by term,

\[
 \|T^{(p)}\|_F^2=2+2S+o(1). \tag{7.5}
\]

Because the coordinate axes always give projection energy \(2\), Lemma 3
implies

\[
 d_p(T^{(p)})^2\le2S+o(1). \tag{7.6}
\]

Palindromicity makes the off-diagonal Gram entry vanish exactly: the term
with index \(k\) cancels the term with index \(p-2-k\).  For the two diagonal
entries, the fixed-band scaling gives

\[
 G_{11}=2(1+S)+o(1),\qquad
 G_{22}=\frac{8W}{p}+o(p^{-1}). \tag{7.7}
\]

Indeed
\(\binom{p-2}{k}t_k^2\to\gamma_k^2\), while every cross term
between \(t_k\) and \(t_{k+2}\) is lower by one power of \(p\); similarly

\[
 4\binom{p-2}{k}t_{k+1}^2
 =\frac{4(k+1)\gamma_{k+1}^2}{p}+o(p^{-1})
\]
on each boundary.  Hence Lemma 4 gives

\[
 R_p(T^{(p)})
 =\frac{4\sqrt{(1+S)W}}{\sqrt p}+o(p^{-1/2}). \tag{7.8}
\]

Combining (7.6)--(7.8),

\[
 \limsup_{p\to\infty}
 p^{-1/4}\frac{d_p(T^{(p)})}{\sqrt{R_p(T^{(p)})}}
 \le
 \left(\frac{S^2}{4(1+S)W}\right)^{1/4}. \tag{7.9}
\]

It remains to optimize the elementary expression on the right under (7.4).

### 7.3 Exact profile optimization

Set \(s=\sqrt2\) and

\[
 r=\left(\frac{2+s}{3+s}\right)^2.
\]

We prove

\[
 \frac{S^2}{(1+S)W}\le r. \tag{7.10}
\]

Put

\[
 a=\gamma_1^2,\qquad x=-\gamma_2,\qquad
 H=\sum_{k=3}^m\gamma_k^2.
\]

Then (7.4) says \(a\le1+sx\), and

\[
 S=a+x^2+H,\qquad
 W\ge a+2x^2+3H. \tag{7.11}
\]

For fixed \(x,H\), replace \(W\) by the lower bound in (7.11).  The resulting
quantity
\(S^2/((1+S)W)\) is increasing in \(a\): since \(W\ge S\),

\[
 \frac{\partial}{\partial a}
 \log\frac{S^2}{(1+S)W}
 =
 \frac2S-\frac1{1+S}-\frac1W
 \ge\frac1{S(1+S)}>0
\]
whenever \(S>0\).  Thus it suffices to take \(a=1+sx\).

Define

\[
 A=1+sx+x^2,\qquad B=1+sx+2x^2
\]
and, for \(H\ge0\),

\[
 D(H)=r(1+A+H)(B+3H)-(A+H)^2.
\]

At \(H=0\) there is the exact factorization

\[
 D(0)=
 \frac{(x-1)^2\big((1+2s)x^2+2x+1+2s\big)}
      {(3+s)^2}\ge0. \tag{7.12}
\]

The quadratic in parentheses is positive for every real \(x\), since its
leading coefficient is positive and its discriminant is
\(4-4(1+2s)^2<0\).

Moreover,

\[
 D'(H)=D'(0)+2(3r-1)H,
\]
where

\[
 3r-1=\frac{5+24s}{49}>0
\]
and

\[
 D'(0)=
 \frac{2\big(4(1+s)x^2+(4+s)x+10+8s\big)}
      {(3+s)^2}>0. \tag{7.13}
\]

The numerator quadratic in (7.13) has positive leading coefficient and
discriminant \(-398-280s<0\).  Consequently \(D(H)\ge D(0)\ge0\) for every
\(H\ge0\), proving (7.10).

Equality forces \(H=0\), then \(x=1\) in (7.12), and saturation
\(a=1+sx\).  This is exactly (7.3).  Finally, (7.9)--(7.10) give

\[
 \left(\frac{r}{4}\right)^{1/4}
 =
 \sqrt{\frac{2+s}{2(3+s)}}=\kappa,
\]
proving Theorem 5.

This optimality theorem is deliberately scoped to fixed-width palindromic
boundary profiles with axis local maximality.  It does not exclude
improvements from bands whose width grows with \(p\), non-palindromic
families, or extremizers with genuinely nonlocal maximizing bases.
