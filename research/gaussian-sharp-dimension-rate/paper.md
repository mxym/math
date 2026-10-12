# Gaussian centroid dimension–accuracy tradeoff at the quadratic-logarithmic scale

**Research note (7 October 2026, PDT).**
This is a strict continuation of the public all-integer Gaussian
quadratic-dimension theorem and its spherical-cap converse.
The analytic results below apply to arbitrary measurable, exactly
equal-mass Gaussian partitions. We claim the proved statements,
not historical priority over Gaussian vector quantization theory.

## Abstract

Let
\[
 F_d(k)=\sup_{\substack{(A_i)_{i=1}^k\ \mathrm{measurable\ partition}\\
             \gamma_d(A_i)=1/k}}
     \sum_{i=1}^k\left\|\int_{A_i}x\,d\gamma_d(x)\right\|^2,
 \qquad F_\infty(k)=F_{k-1}(k).
\]
Set \(L=\log k\), \(t_k=\Phi^{-1}(1-1/k)\),
\(h_k=k\varphi(t_k)\) and \(U_k=h_k^2/k\).

We prove three improvements to the previously published
fixed-additive-accuracy dimensional theorem:

1. **Sharp Gaussian extreme-value normalization and a universal
   asymptotic global gap.** Let \(\gamma\) denote the Euler–Mascheroni
   constant. Then
   \[
        0\le\limsup_{k\to\infty}
              k(U_k-F_\infty(k))\le2(1-\gamma).
   \tag{1}
   \]
   The rightmost constant comes from a dimension-\((k-1)\)
   regular-simplex Gaussian partition; exact finite-\(k\) global
   simplex optimality is **not** assumed.

2. **Asymptotically sharp spherical-cap dimensional obstruction.**
   For every fixed \(c>0\), and any integer sequence \(d_k\) with
   \(d_k/L^2\to c\),
   \[
     \boxed{\displaystyle
     \liminf_{k\to\infty}
          k[U_k-F_{d_k}(k)]\ge\frac1c.}
   \tag{2}
   \]
   Consequently, for any fixed finite \(C\ge0\), if
   \(D_C(k)\) denotes the least dimension achieving
   \(F_d(k)\ge F_\infty(k)-C/k\), then
   \[
    \boxed{\displaystyle
      \liminf_{k\to\infty}\frac{D_C(k)}{(\log k)^2}
       \ge\frac1{C+2(1-\gamma)}.}
   \tag{3}
   \]
   This improves the previous quantitative coefficient \(1/(C+16)\)
   by a fully identified extreme-value constant.

3. **A dimension–accuracy continuum of exact-mass constructions.**
   For every fixed \(A\ge1\) and all sufficiently large *arbitrary*
   integers \(k\), there is a partition in
   \[
       d\le\lceil A(\log k)^2\rceil+1
   \]
   satisfying
   \[
    \boxed{\displaystyle
      U_k-F_d(k)\le\frac{\mathscr C(A)}k,\quad
      \mathscr C(A)=
      4+4\log2+
      2\sqrt2\left(5+\frac{10}{\sqrt A}+\frac8A\right).
    }\tag{4}
   \]
   The proof refines the exponential tilting of the previous
   binary linear-code construction and uses the exact binary
   selector entropy bound \(H(w)<2\log2\).
   For example, the pairs
   \[
   (A,C)=(1,72),(4,41),(16,30),(64,25),
          (256,23),(1024,22),(262144,21)
   \tag{5}
   \]
   are all rigorous integer-constant guarantees.
   In particular,
   \(D_{21}(k)\le\lceil262144(\log k)^2\rceil+1\)
   for all sufficiently large \(k\), whereas the older
   construction needed tolerance \(92/k\) at coefficient \(A=1\).

The results improve concrete error guarantees and dimension
coefficients; they do **not** identify the exact function \(D_C(k)\),
the best possible constant, or the fixed-\(k\) Standard Simplex
optimizer.

---

## 1. Gaussian extremes through the constant term

Write \(\overline\Phi(x)=\int_x^\infty\varphi(u)du\).
Let \(Z_1,Z_2,\ldots\) be independent standard normals and
\(M_k=\max_{i\le k}Z_i\). Write \(m_k=\mathbb E M_k\).

**Lemma 1 (two constant-term expansions).**
For \(k\to\infty\), with \(L=\log k\),
\[
 \begin{aligned}
 t_k^2&=2L-\log L-\log(4\pi)+o(1),\\
 h_k^2&=2L-\log L-\log(4\pi)+2+o(1),\\
 m_k^2&=2L-\log L-\log(4\pi)+2\gamma+o(1).
 \end{aligned}\tag{6}
\]
Here
\[
 \gamma=-\int_0^\infty e^{-u}\log u\,du
\]
is Euler's constant. In particular,
\[
                   h_k^2-m_k^2\longrightarrow2(1-\gamma).
                                                        \tag{7}
\]

*Proof.* Twice integrating \(\varphi'(x)=-x\varphi(x)\)
by parts and using the elementary Mills upper bound give,
for \(t>0\),
\[
 \overline\Phi(t)
 =\varphi(t)\left(t^{-1}-t^{-3}+O(t^{-5})\right).
                                                        \tag{8}
\]
The remainder is positive and bounded by
\(3\varphi(t)t^{-5}\); thus this is a rigorous
asymptotic with an explicit tail estimate.
Since \(k\overline\Phi(t_k)=1\),
taking logarithms yields
\[
 L=t_k^2/2+\log t_k+\tfrac12\log(2\pi)
                       +O(t_k^{-2}).
\]
This first gives \(t_k^2/(2L)\to1\), and substitution
back proves the first line of (6).
Formula (8) gives
\(h_k=t_k+t_k^{-1}+O(t_k^{-3})\), so
\(h_k^2=t_k^2+2+o(1)\).

For the third line, define the standardized extreme
\[
                 Y_k=t_k(M_k-t_k).
\]
For each fixed real \(x\),
\[
 \Pr(Y_k\le x)=
 \left[1-\overline\Phi(t_k+x/t_k)\right]^k
          \longrightarrow e^{-e^{-x}},
\]
because the ratio of the two normal tails tends to \(e^{-x}\)
by (8). We verify **uniform integrability**, rather than
inferring expectation convergence from weak convergence.

For \(x\ge0\), the Gaussian upper-tail hazard
\(\varphi(t)/\overline\Phi(t)\ge t\) for \(t>0\) implies
\[
            \Pr(Y_k>x)
       \le k\overline\Phi(t_k+x/t_k)
       \le e^{-x}.
\]
For \(0\le x\le t_k^2/2\), integrating the same hazard
backwards gives
\[
 k\overline\Phi(t_k-x/t_k)
        \ge e^{x-x^2/(2t_k^2)}
        \ge e^{3x/4},
\]
so
\[
          \Pr(Y_k<-x)\le e^{-e^{3x/4}}.
\]
For \(t_k^2/2\le x\le t_k^2\),
monotonicity bounds the lower tail by
\(e^{-e^{3t_k^2/8}}\); its integral over
this finite-length interval tends to zero.
For \(x\ge t_k^2\), substitute
\(x=t_k^2+t_k u\), \(u\ge0\), and note
\[
 \int_{t_k^2}^\infty\Pr(Y_k<-x)\,dx
 =t_k\int_0^\infty\Phi(-u)^k\,du
 \le\frac{t_k\,2^{-(k-1)}}{\sqrt{2\pi}}\to0.
\]
The positive and negative tails are therefore uniformly
integrable, and
\[
 \mathbb E Y_k\longrightarrow
       -\int_0^\infty e^{-u}\log u\,du=\gamma.
\]
Consequently \(m_k=t_k+\gamma/t_k+o(t_k^{-1})\),
and \(m_k^2=t_k^2+2\gamma+o(1)\), proving (6)--(7).
\(\square\)

**Theorem 2 (unrestricted global optimum: constant gap).**
For every \(k\ge3\), the regular-simplex Gaussian
Voronoi partition in \(\mathbb R^{k-1}\) has
squared-centroid objective \(m_k^2/(k-1)\).
Consequently
\[
 0\le U_k-F_\infty(k)
 \le \frac{h_k^2}{k}-\frac{m_k^2}{k-1}
 =\frac{2(1-\gamma)+o(1)}k.
                                                        \tag{9}
\]

*Proof.* Let \(v_1,\dots,v_k\in\mathbb R^{k-1}\)
be unit regular-simplex vertices,
\(\langle v_i,v_j\rangle=-1/(k-1)\) for \(i\ne j\).
Partition by the largest Gaussian score
\(\langle v_i,G\rangle\); the cells all have mass \(1/k\).
The Gaussian score vector has the same law as
\(\sqrt{k/(k-1)}(Z_i-\bar Z)_{i=1}^k\),
and the mean of its maximum is
\(\sqrt{k/(k-1)}\,m_k\).
By simplex symmetry each cell centroid is collinear with
its winning vertex. Writing
\(b_i=\int_{A_i}x\,d\gamma_{k-1}(x)=\beta v_i\),
we get
\[
 k\beta=\mathbb E\max_i\langle v_i,G\rangle
                       =\sqrt{k/(k-1)}\,m_k,
\]
so the sum of squared centroid norms is
\(k\beta^2=m_k^2/(k-1)\).
The sharp one-cell Gaussian halfspace rearrangement
gives \(F_\infty(k)\le U_k=h_k^2/k\).
Finally \(m_k^2=O(L)\), so
\(km_k^2/(k-1)-m_k^2=o(1)\), and (9) follows
from Lemma 1. \(\square\)

**Consequence (full constant-order global envelope).**
Without claiming convergence of the unknown global
constant term, Theorem 2 establishes
\[
 \boxed{\displaystyle
 2\gamma\le
 \liminf_{k\to\infty}\Big[
    kF_\infty(k)-2\log k+\log\log k+\log(4\pi)\Big]
 \le
 \limsup_{k\to\infty}\Big[
    kF_\infty(k)-2\log k+\log\log k+\log(4\pi)\Big]
 \le2.}
 \tag{9a}
\]
This replaces an unspecified \(O(1)\) by
the explicit classical constants \(2\gamma\) and \(2\).

---

## 2. A constant-sharp spherical-cap asymptotic

We recall the two analytical inequalities from the
public spherical-cap converse, with short proofs.

**Lemma 3 (centroid-to-spherical-maximum bridge).**
For every measurable equal-mass Gaussian \(k\)-partition in
dimension \(d\ge3\), with objective \(P\), there exist
unit vectors \(u_1,\ldots,u_k\in S^{d-1}\) such that
\[
            \frac{kP}{h_k}
       \le\mathbb E\max_i\langle u_i,G\rangle. \tag{10}
\]

*Proof.* Let \(b_i=\int_{A_i}x\,d\gamma_d(x)\).
The halfspace rearrangement bounds \(\|b_i\|\le h_k/k\).
Choose \(u_i=b_i/\|b_i\|\), with any unit direction when
\(b_i=0\). Pointwise,
\(\max_j\langle u_j,x\rangle\ge
\sum_i1_{A_i}(x)\langle u_i,x\rangle\).
Therefore \(\mathbb E\max_i\langle u_i,G\rangle
\ge\sum_i\|b_i\|\ge
(k/h_k)\sum_i\|b_i\|^2\), proving (10). \(\square\)

**Lemma 4 (integrated uniform spherical-cap tail).**
Suppose \(d\ge3\), \(s\in(0,\sqrt d)\), and
\[
 {\cal B}_{d,k}(s)=
 \frac{k}{s\sqrt{2\pi(1-1/d)}}
 \left(1-\frac{s^2}{d}\right)^{(d-1)/2}\le1.
                                                        \tag{11}
\]
For all unit directions \(u_1,\dots,u_k\),
\[
       \mathbb E\max_i\langle u_i,G\rangle
                 \le s+\frac{d}{(d-1)s}. \tag{12}
\]

*Proof.* Write \(G=RV\), with independent
\(R=\|G\|\) and uniform spherical direction \(V\).
By gamma log-convexity, the density of \(V_1\) is
\(c_d(1-u^2)^{(d-3)/2}\) with
\(c_d\le\sqrt{(d-1)/(2\pi)}\).
Integrating the cap density by using
\(u/a\ge1\) for \(u\ge a\), gives
\[
 \Pr(V_1\ge a)
 \le \frac{(1-a^2)^{(d-1)/2}}
           {a\sqrt{2\pi(d-1)}}.
\]
Union bound over the \(k\) directions and
differentiate the logarithm of the right side:
its negative derivative is at least \((d-1)a\)
on \([a,1)\). Hence the expected spherical
maximum \(T=\max_i\langle u_i,V\rangle\)
satisfies
\(\mathbb ET\le a+1/((d-1)a)\)
whenever the union bound at \(a\) is at most one.
Since \(\mathbb ET\ge\mathbb E\langle u_1,V\rangle=0\),
the inequality \(\mathbb ER\le\sqrt d\) may safely
be multiplied by \(\mathbb ET\).
Use independence of \(R,T\) and \(a=s/\sqrt d\).
\(\square\)

**Theorem 5 (constant-sharp quadratic-dimension
spherical defect).**
Fix \(0<c<\infty\), and let \(d_k\) be any
positive integer sequence with
\[
          \frac{d_k}{(\log k)^2}\longrightarrow c.
\]
Then
\[
 \boxed{\displaystyle
 \liminf_{k\to\infty}
            k\left(U_k-F_{d_k}(k)\right)
                   \ge \frac1c.}            \tag{13}
\]

*Proof.* Write \(L=\log k\), \(d=d_k\).
For a fixed auxiliary \(\eta>0\), choose
\[
 s^2=2L-\log L-\log(4\pi)
                -\frac{2L^2}{d}+\eta.       \tag{14}
\]
Since \(d\sim cL^2\), for sufficiently large \(k\)
we have \(0<s^2<d\) and \(s^2=2L+O(\log L)\).

Taylor's formula with explicit remainder
\(\log(1-z)=-z-z^2/2+O(z^3/(1-z))\)
for \(0\le z<1\), applied to \(z=s^2/d\to0\),
gives
\[
 \begin{aligned}
 \log{\cal B}_{d,k}(s)
 &=L-\log s-\tfrac12\log(2\pi(1-1/d))
         +\tfrac{d-1}2\log(1-s^2/d)\\
 &=L-\tfrac12\log(4\pi L)
            -\tfrac{s^2}2-\frac{s^4}{4d}
            +o(1).                           \tag{15}
 \end{aligned}
\]
Indeed the discarded terms are
\(O(s^2/d+s^4/d^2+s^6/d^2+1/d)=o(1)\)
because \(s^2\asymp L\) and \(d\asymp L^2\).
Moreover \(s^4/(4d)=L^2/d+o(1)\).
Substitute (14) into (15) to obtain
\[
                 \log{\cal B}_{d,k}(s)
                   =-\eta/2+o(1).
\]
Therefore \({\cal B}_{d,k}(s)<1\) for all
large \(k\), so Lemma 4 applies. Put
\(H=s+d/((d-1)s)\). As
\(s\to\infty\) and \(d\to\infty\),
\[
 H^2=s^2+2+o(1)
 =2L-\log L-\log(4\pi)
       -2L^2/d+\eta+2+o(1).                  \tag{16}
\]
Lemma 1 also gives
\(h_k^2=2L-\log L-\log(4\pi)+2+o(1)\).
Thus
\[
           h_k^2-H^2=\frac{2L^2}{d}-\eta+o(1).
                                                        \tag{17}
\]
Using Lemmas 3--4 and the elementary identity
\[
 h_k^2-h_kH
 =\tfrac12(h_k^2-H^2)+\tfrac12(h_k-H)^2
 \ge\tfrac12(h_k^2-H^2),
\]
we obtain
\[
 \begin{aligned}
 k(U_k-F_d(k))
 &=h_k^2-kF_d(k)\\
 &\ge h_k^2-h_kH
 \ge L^2/d-\eta/2+o(1).
 \end{aligned}
\]
Take the liminf, use \(L^2/d\to1/c\),
and then send \(\eta\downarrow0\).
This establishes (13) with no assumed
optimizer existence. \(\square\)

**Corollary 6 (asymptotically improved dimension coefficient).**
Fix \(C\ge0\) and define \(D_C(k)\) to be the least
dimension such that \(F_d(k)\ge F_\infty(k)-C/k\).
Then, for all sufficiently large \(k\), the
dimension is defined (by dimension saturation),
and
\[
 \boxed{\displaystyle
 \liminf_{k\to\infty}
 \frac{D_C(k)}{(\log k)^2}
       \ge\frac1{C+2(1-\gamma)}.}            \tag{18}
\]

*Proof.* The earlier finite spherical-cap converse
already implies
\[
    D_C(k)\ge\frac{L^2}{C+16}
\]
for all sufficiently large \(k\).
Hence no subsequential limit of \(D_C(k)/L^2\)
can be zero. If the liminf is infinite, the
claim is automatic. Otherwise take a subsequence
on which \(D_C(k)/L^2\to c\in(0,\infty)\).
The definition and Theorem 2 give
\[
 \begin{aligned}
 k(U_k-F_{D_C(k)}(k))
 &\le k(U_k-F_\infty(k))+C\\
 &\le 2(1-\gamma)+C+o(1).
 \end{aligned}
\]
Theorem 5 gives a liminf on this subsequence
of at least \(1/c\). Therefore
\(1/c\le C+2(1-\gamma)\), or
\(c\ge1/(C+2(1-\gamma))\), as required.
\(\square\)

The estimate is strictly stronger than the elementary
coefficient \(1/(C+1)\): indeed
\(\gamma>1/2\), for instance because
\(\gamma>H_6-\log7>1/2\) by the
harmonic-integral comparison, where
\(H_6=49/20\). The logarithmic endpoint
\(\log7<39/20\) is also certified by the
companion exact checker.

**Scope.** This is a sharp-constant asymptotic **lower
obstruction derived from spherical caps**, not a proof
that the true optimal dimension coefficient equals
the right side of (18). There remains a potentially
substantial gap to known constructive coefficients.

---

## 3. A parameterized refinement of the binary linear-code construction

The former all-integer construction had only one preselected
dimensional coefficient and an error constant \(92\).
We retain the full dependence on dimension
\(m=\lceil A L^2\rceil\), \(A\ge1\),
and re-optimize the exponential-tilting cut from
\(B_0=\tfrac12\log L+12\) to
\[
                      B=\tfrac12\log L+6. \tag{19}
\]
This is not a numerical heuristic: every inequality is
controlled below by explicit integer or rational constants.

For the dyadic case \(k=2^r\), choose independent uniform
binary columns \(g_1,\dots,g_m\in\mathbb F_2^r\).
For each message \(u\in\mathbb F_2^r\), put
\[
 v_u=m^{-1/2}
    \left((-1)^{u\cdot g_1},\dots,
          (-1)^{u\cdot g_m}\right).
\]
For a fixed generator, these are unit Gaussian score
directions. A full-rank generator makes them distinct,
and the diagonal sign-flip group \(D_a v_u=v_{u+a}\)
acts transitively on the score-maximizing Gaussian cells,
so all \(k\) masses are exactly \(1/k\).

For \(G\sim N(0,I_m)\), let \(M=\max_u\langle v_u,G\rangle\),
let \(a_j=G_j/\sqrt m\), and set
\[
 Q_2=\sum_j a_j^2,\quad
 Q_4=\sum_j a_j^4,\quad
 {\cal G}=\{1/2\le Q_2\le2,\ Q_4\le10/m\}.
\]
The Gaussian fourth and eighth moments give
\[
 \begin{aligned}
 \mathbb EQ_2=1,\quad&\mathrm{Var}(Q_2)=2/m,\\
 \mathbb EQ_4=3/m,\quad&\mathrm{Var}(Q_4)=96/m^3,
 \end{aligned}
\]
and Chebyshev gives \(\Pr({\cal G}^c)\le10/m\).

**Lemma 7 (uniform tilted anti-concentration, improved cut).**
For every \(A\ge1\), \(L=\log k\ge10^{10}\) and
\(m=\lceil A L^2\rceil\), on every \(G\in{\cal G}\)
put
\[
 \lambda=\sqrt{2L/Q_2},\quad
 \Lambda=\sum_j\log\cosh(\lambda a_j),\quad
 \mu=\sum_j a_j\tanh(\lambda a_j),\quad
 s_y=\mu-\frac{B+y}{\lambda}
     \quad(0\le y\le\lambda/4).
\]
Let \(S_a=\sum_j a_j\varepsilon_j\) with independent
uniform signs. Then
\[
 \Pr_\varepsilon(S_a\ge s_y)
       \ge \frac{e^{-L+B+y-1}}{20\lambda},
                                                        \tag{20}
\]
and, conditional on \(G\), the random binary-generator
maximum satisfies
\[
 \Pr_g(M<s_y\mid G)\le\eta e^{-y},\qquad
             \eta=80e^{-5}<3/5.             \tag{21}
\]

*Proof.* Since \(Q_2\in[1/2,2]\),
\(\sqrt L\le\lambda\le2\sqrt L\).
Under the exponentially tilted independent-sign measure
\[
 \Pr_\lambda(\varepsilon_j=e)
        =\frac{e^{\lambda a_j e}}
                    {2\cosh(\lambda a_j)}
 \quad(e\in\{-1,1\}),
\]
the sum \(S_a\) has mean \(\mu\) and variance
\[
 V=\sum_j a_j^2\operatorname{sech}^2(\lambda a_j)
             \in[1/4,2],
\]
because \(\operatorname{sech}^2x\ge1-x^2\)
and \(\lambda^2 Q_4\le40L/m\le1/4\).
Every centered summand is bounded in absolute value
by \(2|a_j|\), so
\[
 \sum_j \mathbb E_\lambda|W_j|^3
      \le8\sqrt{Q_2Q_4}
      \le8\sqrt{20/m}.
\]
The classical Berry–Esseen inequality for independent,
not necessarily identically distributed summands with
absolute constant at most \(1\) therefore bounds the
normal CDF error by
\(64\sqrt{20/m}<288/\sqrt m\).

Since \(L\ge10^{10}\),
\(B=(\log L)/2+6\le\sqrt L/4\le\lambda/4\).
The first inequality follows because
\(\sqrt L/4-(\log L)/2-6\)
is increasing for \(L\ge16\) and is
positive at \(10^{10}\)
(\(\log(10^{10})<24\), \(\sqrt{10^{10}}=10^5\)).
Thus the tilted interval
\[
                   [s_y,s_y+1/\lambda]
\]
lies, upon subtracting \(\mu\) and dividing by \(\sqrt V\),
inside \([-1,0]\), with standardized length
at least \(1/(2\lambda)\).
Since \(\varphi(1)>1/5\), its normal probability
is at least \(1/(10\lambda)\).
The twice-applied Berry–Esseen error is at most
\(576/\sqrt m\le1/(20\lambda)\) for
\(L\ge10^{10}\), \(m\ge L^2\). Hence its actual
tilted probability is at least \(1/(20\lambda)\).

The change-of-measure identity and
\[
            \Lambda-\lambda\mu\ge
                 -\lambda^2Q_2/2=-L
\]
imply (20). For the last inequality, differentiate
the even function
\(\log\cosh x-x\tanh x+x^2/2\):
its derivative for \(x>0\) is \(x\tanh^2x\ge0\).

For each fixed \(G\), nonzero binary messages have
identically distributed Rademacher-weighted scores,
and **distinct nonzero messages have pairwise independent
scores over the random columns**. Indeed two distinct
nonzero vectors over \(\mathbb F_2\) are linearly independent,
so their character signs form independent pairs.
Chebyshev applied to the exceedance count gives
\[
 \begin{aligned}
 \Pr_g(M<s_y\mid G)
 &\le\frac1{(k-1)\Pr_\varepsilon(S_a\ge s_y)}\\
 &\le \frac{20\lambda e^{L-B-y+1}}{k-1}\\
 &\le80\sqrt L\,e^{-B-y+1}
 =80e^{-5-y}=\eta e^{-y}.
 \end{aligned}
\]
Here \(k-1\ge k/2\), \(\lambda\le2\sqrt L\), and
\(e^B=e^6\sqrt L\), as required.
Finally \(e>27/10\) gives
\(e^5>(27/10)^5>400/3\), so \(\eta<3/5\).
\(\square\)

**Lemma 8 (sharp dimension-dependent Gaussian maximum
estimate).** For every \(A\ge1\) and dyadic \(k=2^r\)
with \(L\ge10^{10}\), there exists a **full-rank**
binary generator of length \(m=\lceil A L^2\rceil\)
such that
\[
 \boxed{\displaystyle
 \mathbb E_G M\ge
       \sqrt{2L}-\frac{\log L}{2\sqrt{2L}}
       -\frac{T_A}{\sqrt L},\qquad
       T_A=5+\frac{10}{\sqrt A}+\frac8A.}    \tag{22}
\]
The associated score-max Gaussian partition has
exactly equal masses and
\[
 \boxed{\displaystyle
       U_k-P_{\rm code}
           \le\frac{3+2\sqrt2\,T_A}{k}.}     \tag{23}
\]

*Proof.* Conditional on \(G\in{\cal G}\), use the
threshold failure bound from Lemma 7 and integrate
downward over \(s_y=s_0-y/\lambda\). Since \(M\ge X_0\),
where \(X_0=m^{-1/2}\sum_jG_j\sim N(0,1)\), the exact
positive-part decomposition yields
\[
 \mathbb E_g[M\mid G]\ge
  \mu-\frac B\lambda-\frac\eta\lambda
       -\eta(4\sqrt L+|X_0|)e^{-\lambda/4}.
                                                        \tag{24}
\]
For clarity, the decomposition is
\[
 (s_0-M)_+
 =\frac1\lambda\int_0^{\lambda/4}
                 \mathbf1_{\{M<s_y\}}dy
          +(s_{\lambda/4}-M)_+.
\]
The remaining tail term is bounded by
\((4\sqrt L+|X_0|)1_{\{M<s_{\lambda/4}\}}\)
because
\(\mu\le\lambda Q_2\le4\sqrt L\).

Let \(\sigma=\sqrt{Q_2}\). Since
\(x\tanh(\lambda x)\ge\lambda x^2
             -(\lambda^3/3)x^4\)
for all real \(x\) (apply
\(\tanh u\ge u-u^3/3\) to \(|u|\)),
\[
 \mu\ge\sqrt{2L}\,\sigma
          -\frac83 L^{3/2}Q_4
          \quad\text{on }{\cal G}.
\]
Using \(\mathbb E Q_4=3/m\),
Cauchy–Schwarz and Chebyshev give
\[
 \begin{aligned}
 \mathbb E[\sigma1_{\cal G}]
  &\ge1-\sqrt{2/m}-\sqrt{10/m},\\
 \mathbb E[\mu1_{\cal G}]
  &\ge\sqrt{2L}
     -\frac{7/\sqrt A+8/A}{\sqrt L}.
 \end{aligned}                               \tag{25}
\]
The first line follows from
\(|\sqrt x-1|\le|x-1|\), and
\(\mathbb E[\sigma1_{{\cal G}^c}]
 \le\sqrt{\mathbb E\sigma^2\Pr({\cal G}^c)}\).
We have
\[
 \mathbb E[(B/\lambda)1_{\cal G}]
 \le\frac{\log L}{2\sqrt{2L}}
       +\frac6{\sqrt{2L}},
 \qquad \eta/\lambda<\frac3{5\sqrt L}.
\]
Because \(L\ge10^{10}\), \(\mathbb E|X_0|\le1\),
\(\eta<3/5\), and
\(e^{\sqrt L/4}\ge(\sqrt L/4)^4/4!\),
\[
 \begin{aligned}
 \eta(4\sqrt L+\mathbb E|X_0|)
                      e^{-\sqrt L/4}
 &\le\frac35(4\sqrt L+1)\frac{6144}{L^2}\\
 &\le\frac{18432}{L^{3/2}}
 \le\frac1{10\sqrt L}.
 \end{aligned}                                  \tag{26}
\]
Finally \(6/\sqrt2<17/4\), so the three
dimension-independent error terms in
(24) sum to
\[
          \frac{17/4+3/5+1/10}{\sqrt L}
          =\frac{99/20}{\sqrt L}
          <\frac5{\sqrt L}.                 \tag{27}
\]

On the complement of \({\cal G}\),
\(M\ge X_0\), and
\[
 \mathbb E[M1_{{\cal G}^c}]
   \ge-\sqrt{10/m}
   \ge-\frac1{\sqrt A\sqrt L}
\]
for \(L\ge10\). Combining (24)--(27),
we get the unconditional generator-data estimate
\[
 \mathbb E_{g,G}M\ge
   \sqrt{2L}-\frac{\log L}{2\sqrt{2L}}
    -\frac{5+8/\sqrt A+8/A}{\sqrt L}.
                                                        \tag{28}
\]

A generator has deficient rank with probability at most
\[
 \Pr(\operatorname{rank}<r)
       \le(k-1)2^{-m}
       \le e^{L-(2/3)A L^2}
       \le\frac1{A L^2}
\]
for \(L\ge10^{10}\), \(A\ge1\).
For the last estimate use
\(\log A\le A-1\), \(\log L\le L\):
\[
 \begin{aligned}
 (2/3)A L^2-L-2\log L-\log A
 &\ge(2/3)L^2-3L\\
 &\quad+[(2/3)L^2-1](A-1)>0.
 \end{aligned}
\]
For every fixed generator,
\[
 \mathbb E_G M^2\le2L+3
\]
by the Gaussian union bound on positive maxima,
integration of the upper tail of \(M_+^2\),
and \(M_-\le(X_0)_-\).
Thus Cauchy–Schwarz bounds the contribution of
rank-deficient generators to the average by
\[
 \sqrt{\frac{2L+3}{A L^2}}
       \le\frac2{\sqrt A\sqrt L}.
\]
Discard the deficient generators and normalize
by the probability of the full-rank event.
Since the positive lower bound for the retained
average only increases upon this normalization,
some full-rank generator has expected maximum
satisfying (22).

Its sign-flip orbit gives exactly equal cell masses
as explained above. The same Cauchy–Schwarz
calculation as in the published quadratic theorem
gives \(kP_{\rm code}\ge(\mathbb EM)^2\).
The right side of (22) is positive for our
large \(L\). Squaring gives
\[
 kP_{\rm code}\ge2L-\log L-2\sqrt2\,T_A.
\]
Mills' normal-tail bounds imply
\(h_k^2\le2L-\log L+3\).
Subtracting proves (23). \(\square\)

**Technical note on constants.** The use of the
explicit parameter \(A\) requires *no* change to
the Berry–Esseen absolute constant \(1\).
Increasing \(A\) improves both the
Gaussian weight-concentration terms \(A^{-1/2}\)
and the fourth-cumulant term \(A^{-1}\).
The additive floor \(5\) in (22) originates from
the local tilted interval's logarithmic prefactor
and the integrated failure term, not from an
unaccounted numerical optimizer.

---

## 4. Removing dyadic cardinality: one-coordinate exact-mass gluing

To handle every integer \(k\), use its binary expansion,
listed in strictly decreasing order:
\[
 k=q_1+\cdots+q_s,\qquad q_j=2^{r_j},
       \ r_1>\cdots>r_s\ge0,\qquad w_j=q_j/k.
\]
The binary entropy of these selector weights satisfies
the **sharp universal inequality**
\[
              H(w)=\sum_jw_j\log(1/w_j)<2\log2.
                                                        \tag{29}
\]
For completeness, put \(S_j=\sum_{\ell\ge j}w_\ell\).
The sum of the smaller distinct powers is less than
the present power, so \(S_{j+1}<w_j\) and
\(S_j\le2^{1-j}\). The exact entropy chain formula
\[
 H(w)=\sum_j S_jh_2(w_j/S_j),\qquad
 h_2(t)=-t\log t-(1-t)\log(1-t),
\]
and \(h_2\le\log2\) give (29).
The constant \(2\log2\) is asymptotically attained by
the binary expansion of \(k=2^s-1\), showing that
no smaller universal entropy constant is possible.

**Lemma 9 (Gaussian selector and energy identity).**
Suppose \(k=\sum_jq_j\), and for each \(j\)
an equiprobable Gaussian \(q_j\)-partition
in a common \(\mathbb R^m\) has objective \(P_j\).
There is an exactly equiprobable \(k\)-partition
in \(\mathbb R^{m+1}\) with objective
\[
                P_{\rm glue}\ge
                   \frac1{k^2}\sum_jq_j^2P_j.
                                                        \tag{30}
\]

*Proof.* Use one independent standard Gaussian scalar
to select block \(j\) with probability \(q_j/k\),
via consecutive exact Gaussian quantiles.
On the data coordinates, apply that block's
\(q_j\)-cell partition. Every final cell has mass
\((q_j/k)(1/q_j)=1/k\).
By independence its data-coordinate first moment is
\((q_j/k)\) times the corresponding local first moment.
The sum of squared data-coordinate moments is
exactly the right side of (30). The extra selector
coordinate contributes nonnegative squared moments.
\(\square\)

**Theorem 10 (complete quantitative dimension–accuracy curve).**
Let \(A\ge1\) be any fixed real constant.
For every sufficiently large integer \(k\), there exists
a measurable, exactly equiprobable \(k\)-cell
Gaussian partition in dimension
\[
                   d\le\lceil A(\log k)^2\rceil+1
\]
such that
\[
 \boxed{\displaystyle
     U_k-P(\mathcal A)\le\frac{\mathscr C(A)}k,
 \qquad
 \mathscr C(A)=4+4\log2+
     2\sqrt2\left(5+\frac{10}{\sqrt A}+\frac8A\right).
 }                                                       \tag{31}
\]
Consequently,
\[
             D_{\mathscr C(A)}(k)
                    \le\lceil A(\log k)^2\rceil+1.
                                                        \tag{32}
\]
All cardinalities are included; the conclusion does
not rely on a group acting transitively on *all*
\(k\) cell labels, only on each dyadic subblock.

*Proof.* Choose the integer threshold \(r_0\)
so every dyadic \(q\ge Q_0:=2^{r_0}\)
satisfies \(\log q\ge10^{10}\).
Let \(k\ge Q_0^2\), put \(L=\log k\), and
allocate a common data Gaussian block of dimension
\(m=\lceil A L^2\rceil\).

For each binary block \(q_j\ge Q_0\),
apply Lemma 8 in its own
\(\lceil A(\log q_j)^2\rceil\)-dimensional
data space, then extend cylindrically
to the common \(m\) dimensions. This produces
an exact equal-mass \(q_j\)-partition of objective
\[
 P_j\ge
 \frac{h(1/q_j)^2-[3+2\sqrt2\,T_A]}{q_j},
 \qquad T_A=5+10/\sqrt A+8/A.
                                                        \tag{33}
\]
For the finitely many smaller powers \(q_j<Q_0\),
choose any equiprobable partition, and use only \(P_j\ge0\).

Apply Lemma 9. Write \(W_{\rm sm}=\sum_{j:q_j<Q_0}w_j\).
The distinct binary powers smaller than \(Q_0\)
sum to at most \(Q_0-1\), so \(W_{\rm sm}<Q_0/k\).
The squared Gaussian upper-tail hazard
\(h(q)^2\) is globally 2-Lipschitz in
\(\log(1/q)\): for every \(q_j\le k\),
\[
 0\le h(1/k)^2-h(1/q_j)^2
          \le2\log(k/q_j)=2\log(1/w_j).
\]
The identity also holds at \(q_j=1\), with \(h(1)=0\)
by continuity. Therefore
\[
 \begin{aligned}
 k[U_k-P_{\rm glue}]
 &\le[3+2\sqrt2\,T_A]
  +2\sum_jw_j\log(1/w_j)
  +W_{\rm sm}\,h_k^2\\
 &<3+2\sqrt2\,T_A+4\log2
       +\frac{2Q_0\log k}{k}.
 \end{aligned}                                  \tag{34}
\]
The bound \(h_k^2\le2\log k\) follows from
the standard Gaussian exponential-moment inequality
\(q e^{\lambda h(q)}
 \le e^{\lambda^2/2}\), taking \(\lambda=h(q)\).
For \(k\ge Q_0^2\),
\[
 \frac{2Q_0\log k}{k}
       \le\frac{4\log Q_0}{Q_0}<1,
\]
since \(Q_0\ge2^{10}\).
Equation (34) is therefore strictly less
than \(\mathscr C(A)\), proving (31).
The global optimum is no greater than
the halfspace envelope \(U_k\), so (32) follows.
\(\square\)

**Corollary 11 (seven certified explicit tradeoff points).**
For all sufficiently large integers \(k\), the
following bounds all hold:

| Dimensional coefficient \(A\) | Guaranteed error \(C/k\) |
|---:|---:|
| \(1\) | \(72/k\) |
| \(4\) | \(41/k\) |
| \(16\) | \(30/k\) |
| \(64\) | \(25/k\) |
| \(256\) | \(23/k\) |
| \(1024\) | \(22/k\) |
| \(262144\) | \(21/k\) |

In each row \(d\le\lceil A(\log k)^2\rceil+1\).
For example,
\[
 \boxed{\displaystyle
 \frac1{22+2(1-\gamma)}
 \le\liminf_{k\to\infty}
          \frac{D_{22}(k)}{(\log k)^2}
 \le\limsup_{k\to\infty}
          \frac{D_{22}(k)}{(\log k)^2}
 \le1024.}                                     \tag{35}
\]

*Proof.* Using the exact rational estimates
\[
 \log2<7/10,\qquad\sqrt2<99/70
\]
(the first follows by the degree-three Taylor
lower bound for \(e^{7/10}>2\); the second by
\(99^2>2\cdot70^2\)), we have
\[
  \mathscr C(A)
   <\frac{34}{5}+\frac{99}{35}
                    \left(5+\frac{10}{\sqrt A}
                                  +\frac8A\right).
                                                        \tag{36}
\]
For the seven square values of \(A\) in the table,
the last expression is respectively below
the displayed integer constants.
All comparisons reduce to integer arithmetic
and are independently replayed in check_exact.py.
The first inequality in (35) is Corollary 6
with \(C=22\), and the last inequality is
Theorem 10 with \(A=1024\). \(\square\)

The limiting guaranteed additive constant produced
by this *particular* two-moment/tilting method is
\[
 \lim_{A\to\infty}\mathscr C(A)
       =4+4\log2+10\sqrt2.
                                                        \tag{37}
\]
This number is **not** claimed to be a
fundamental Gaussian quantization lower limit.
The optimizing partition may have much smaller loss;
our analysis is intentionally explicit and solver-free.

---

## 5. Scope, dependencies, and open quantitative questions

The new lower bound (18) and constructive upper bound (31)
give a mathematically explicit Pareto-type
dimension–accuracy region. They establish a stronger
range of the Gaussian dimension-rate frontier
than the earlier single \(D_{92}\) comparison.

The new results remain **classical mathematical proofs**,
not Lean-certified theorems. The proof of the binary
construction uses the standard independent-summand
Berry–Esseen theorem with deliberately relaxed
absolute constant \(1\); a published constant
below \(0.56\) is known. The normal maximum lemma
uses elementary Mills tails and a complete
uniform-integrability argument, rather than numerical
extreme-value fits.

The sharp leading coefficient of \(D_C(k)/(\log k)^2\)
for a fixed additive \(C\) remains open.
So does the existence and value of
\(\lim_{k\to\infty} k(U_k-F_\infty(k))\),
which may be smaller than the simplex comparator
\(2(1-\gamma)\); no Standard Simplex global
optimality is assumed.

Further directions include identifying the
optimal constant in the dimension-normalized
spherical defect (whether the factor \(1/c\)
in (13) is sharp), deriving matching upper
asymptotics for fixed \(d/L^2\to c\), and
producing polynomial-time certified binary
generator matrices. Unequal mass vectors
and the exact fixed-\(k\) Gaussian partition
classification are not resolved here.

Research context and a historically cautious
source screen appear in LITERATURE.md.
The checker establishes exact rational
parameter comparisons and a finite set of
code-character, entropy, and Mills interfaces;
**the universal theorems are analytic, not inferred
from finite tests.**
