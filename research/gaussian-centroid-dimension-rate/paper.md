# Gaussian centroid partitions: logarithmic-dimensional relative saturation and a sharp rate–distortion obstruction

**Independent mathematical research note — 7 October 2026 (PDT).**

This work continues the arbitrary-mass Gaussian centroid program in
[the companion manuscript](../gaussian-centroid-mass-envelope/README.md),
whose published proof provides the sharp first-order equal-mass asymptotic.
The present work studies how many Gaussian coordinates are actually
needed to approach the unrestricted optimum over \(k\) equal-mass cells.
All Gaussian partition constructions are explicit mathematical
threshold procedures; numerical optimization is not used in proofs.

## Abstract

Let \(\gamma_d\) be standard Gaussian probability on \(\mathbb R^d\).
For \(k\ge2\), define
\[
 F_d(k)=\sup_{\substack{\mathbb R^d=\bigsqcup_{i=1}^k A_i\\
                     \gamma_d(A_i)=1/k}}
       \sum_{i=1}^k
        \left\|\int_{A_i}x\,d\gamma_d(x)\right\|^2,
 \qquad F_\infty(k)=F_{k-1}(k).
 \tag{1}
\]
The companion mass-envelope theorem gives
\[
 \frac{h(1/k)^2-2}{k}\le F_\infty(k)
       \le\frac{h(1/k)^2}{k},
 \qquad h(q)=\frac{\varphi(\Phi^{-1}(1-q))}{q},
 \tag{2}
\]
where \(h(1/k)^2=2\log k-\log\log k+O(1)\).
The exact dimension saturation \(F_d(k)=F_{k-1}(k)\)
for \(d\ge k-1\) follows from the published fixed-mass
Gaussian duality theorem.

Our main result is an **optimal-order dimensional phase**:

**Theorem A.** For each fixed \(0<\varepsilon<1\),
there are explicit integers \(b_\varepsilon\ge2\)
and \(K_\varepsilon\) such that for every
\(k\ge K_\varepsilon\) there is an exactly equiprobable
measurable Gaussian partition in
\[
 d\le C_\varepsilon\log k,\qquad
 C_\varepsilon=\frac{2(b_\varepsilon-1)}
                        {\log b_\varepsilon},
\]
whose centroid objective is at least
\((1-\varepsilon)F_\infty(k)\).
The construction is a balanced \(b_\varepsilon\)-ary
tree of **Gaussian coordinate threshold partitions**;
it works for *all integers \(k\)*, not only powers.

Conversely, every partition meeting this relative
accuracy must have
\[
 d\ge(c_\varepsilon-o(1))\log k,
\]
where \(c_\varepsilon>0\) is determined by a
strictly increasing rate–distortion curve.
Thus the optimal dimension is \(\Theta_\varepsilon(\log k)\).

A stronger converse isolates a second scale:
achieving **additive \(O(1/k)\) accuracy**
to \(F_\infty(k)\) requires
\[
 \boxed{\displaystyle
  d\ge(2-o(1))\frac{(\log k)^2}{\log\log k}.}
 \tag{3}
\]
In particular, logarithmic dimension with a fixed
constant cannot recover the sharp two-log-term
asymptotic of the high-dimensional optimum.

We give exact first moments for two constructive
families and show that the simple one-pass
staircase construction has an asymptotically
sharp method loss of \(2/k\) in the equal-mass
problem. This distinguishes a limitation of
one construction from a limitation of the
actual global optimum.

## 1. Gaussian quantile and entropy preliminaries

For \(0<q<1\), put
\[
 t_q=\Phi^{-1}(1-q),\quad
 h(q)=\frac{\varphi(t_q)}q,\quad
 \varphi(t)=(2\pi)^{-1/2}e^{-t^2/2}.
\]
We extend continuously by \(h(1)=0\).
The following elementary bound is useful.

**Lemma 1 (globally explicit one-dimensional bound).**
For every \(0<q\le1\),
\[
 h(q)^2\ge
  2\log(1/q)-\log^+\!\log(1/q)-4,
 \tag{4}
\]
where the second term is defined as zero
at \(q=1\), and
\(\log^+u=\max\{0,\log u\}\) for \(u>0\).
Also
\[
 h(q)^2\le2\log(1/q),
 \tag{5}
\]
and
\[
 \frac{d\,h(q)^2}{d\log(1/q)}
 =2h(q)[h(q)-t_q]\in(0,2).
 \tag{6}
\]
The derivative tends to \(2\) as \(q\downarrow0\).

*Proof.* For (5), apply conditional Jensen
to \(\mathbb E e^{\lambda Z}=e^{\lambda^2/2}\),
restricted to \(\{Z\ge t_q\}\), and choose
\(\lambda=h(q)\):
\(q e^{h(q)^2}\le e^{h(q)^2/2}\).

To prove (4), first consider \(q\le1/10\).
The classical Mills bounds
\[
 \frac{t}{t^2+1}\varphi(t)\le\overline\Phi(t)
                \le\frac{\varphi(t)}t\quad(t>0)
 \tag{7}
\]
give \(t_q>1\) and
\(t_q^2\le2L\), where \(L=\log(1/q)>1\).
Since \(t+1/t\le2\sqrt{2L}\), the lower
Mills bound gives
\[
 t_q^2\ge2L-\log L-\log(16\pi)
                 >2L-\log L-4.
\]
For the last strict inequality use
\(e>8/3\), \(\pi<22/7\), and
\((8/3)^4=4096/81>352/7=16(22/7)\).
Because \(h(q)\ge t_q\), (4) follows
in the small-tail regime.

If \(q>1/10\), then \(L<\log10\).
For \(L\le1\), the right side of (4)
is at most \(2-4<0\).
For \(1<L<\log10\), the function
\(2L-\log L\) is increasing. Moreover
\(\log10<7/3\) (because \(e>27/10\)
and \((27/10)^7>10^3\)), whereas
\(\log\log10>\log2>2/3\).
Thus \(2L-\log L<14/3-2/3=4\).
The right side of (4) is negative,
proving the assertion without computing
any normal quantile.

For (6), differentiate
\(q=\overline\Phi(t)\) and
\(h=\varphi(t)/q\):
\[
 dh/dt=h(h-t),\quad
 dt/d\log(1/q)=1/h.
\]
The truncated Gaussian has strictly positive
variance \(1+t h-h^2\), so
\(0<h(h-t)<1\). Finally, two integrations
by parts yield
\(\overline\Phi(t)=\varphi(t)(t^{-1}-t^{-3}
+O(t^{-5}))\); hence \(h(t)=t+t^{-1}
+O(t^{-3})\) and \(h(h-t)\to1\).
\(\square\)

For any finite probability vector \(q_1,\ldots,q_r>0\),
write \(R_j=\sum_{\ell=j}^r q_\ell\).

**Lemma 2 (residual entropy, no sorting required).**
For every ordering of the \(q_j\),
\[
  \sum_{j=1}^r q_j\log\frac1{R_j}\le1.
 \tag{8}
\]

*Proof.* Since \(R_{j+1}=R_j-q_j\)
and \(s\mapsto-\log s\) is decreasing,
\[
 q_j\log\frac1{R_j}
 \le\int_{R_{j+1}}^{R_j}\log\frac1s\,ds.
\]
Sum and use
\(\int_0^1\log(1/s)\,ds=1\).
\(\square\)

## 2. Balanced branching in k−1 versus logarithmically many coordinates

Fix an integer \(b\ge2\). Given a node carrying
\(m\) equally likely target leaves, split it into
\(r=\min\{b,m\}\) children with integer target
counts differing by at most one, so that their
counts sum exactly to \(m\).
Continue until every leaf carries count \(1\).

Let
\[
 T=\lceil\log_b k\rceil .
 \tag{9}
\]
Every path has length at most \(T\). At every
level \(\ell<T-1\), every node has \(m\ge b\)
descendant target leaves: its integer count
is either \(\lfloor k/b^\ell\rfloor\)
or \(\lceil k/b^\ell\rceil\), each at least \(b\).
Thus each such level consists entirely of nodes
with **exactly \(b\) nonempty children**.

If \(m\ge b\), let \(m_1,\dots,m_b\)
be the balanced child counts and put
\(q_j=m_j/m\). Since
\(\lfloor m/b\rfloor\ge m/(2b)\)
and \(\lceil m/b\rceil\le2m/b\),
\[
       \frac1{2b}\le q_j\le\frac2b.
 \tag{10}
\]

At each tree level \(\ell\) allocate a new
independent standard Gaussian block of dimension
\(b-1\). **Reuse that same block among all
nodes at level \(\ell\)**, using node-dependent
thresholds. Given that the earlier blocks
selected some node \(v\), split its children
by the following sequential normal thresholds.
Set \(R_j=\sum_{a=j}^r q_a\),
\(s_j=q_j/R_j\), and
\[
 \begin{aligned}
 C_j&=\{Z_a<t_{s_a}\ \forall a<j,\
            Z_j\ge t_{s_j}\},
                       &&j<r,\\
 C_r&=\{Z_a<t_{s_a}\ \forall a<r\}.
 \end{aligned}                                   \tag{11}
\]
Only the first \(r-1\) coordinates of
that level's Gaussian block are used.
By independent coordinates and
\(\prod_{a<j}(1-s_a)=R_j\), the conditional
child probabilities are **exactly**
\(q_j\), and induction gives final
Gaussian mass precisely \(1/k\)
for every labeled target leaf.

The total dimension is at most
\[
                   d=(b-1)T.                  \tag{12}
\]

## 3. Nodewise moment energy

For a node split with child masses \(q_j\),
let \(\mu_j=\mathbb E[Z\mid Z\in C_j]\)
be the conditional mean vector of its
fresh Gaussian block, and put
\[
                 E(q)=\sum_jq_j\|\mu_j\|^2.
 \tag{13}
\]
When \(j<r\), coordinate \(j\) contributes
\(h(s_j)\) to \(\mu_j\). The last child has
no dedicated coordinate but
\(\|\mu_r\|^2\ge0=h(1)^2\).
Consequently
\[
                    E(q)\ge
               \sum_{j=1}^r q_j h(s_j)^2.
 \tag{14}
\]

**Lemma 3 (universal b-way energy).**
For \(b\ge2\) and every \(b\)-vector
of child masses obeying (10),
\[
 \boxed{\displaystyle
 E(q)\ge
 L_b:=2\log(b/2)-\log\log(2b)-6.}
 \tag{15}
\]
For all sufficiently large \(b\),
\(L_b>0\), and
\[
                      \frac{L_b}{2\log b}
                         \longrightarrow1.
 \tag{16}
\]

*Proof.* Apply Lemma 1 to \(s_j=q_j/R_j\),
interpreting the formula by continuity
at \(s_r=1\). By (14),
\[
 \begin{aligned}
 E(q)&\ge2\sum_j q_j\log\frac{R_j}{q_j}
   -\sum_j q_j\log^+\!\log\frac{R_j}{q_j}-4\\
 &=2H(q)-2\sum_j q_j\log\frac1{R_j}
   -\sum_jq_j\log^+\!\log\frac{R_j}{q_j}-4,
 \end{aligned}
\]
where \(H(q)=\sum_jq_j\log(1/q_j)\).
From \(q_j\le2/b\), \(H(q)\ge\log(b/2)\).
By Lemma 2, the residual entropy
sum is at most \(1\).
Since \(s_j=q_j/R_j\ge q_j\ge1/(2b)\),
\(\log^+\log(1/s_j)\le\log\log(2b)\)
for \(b\ge2\).
These estimates give (15). Finally
\(L_b=2\log b-\log\log b-O(1)\),
which proves (16). \(\square\)

**Lemma 4 (global first moments add across tree levels).**
For the exactly equiprobable \(k\)-cell
partition defined by the tree,
\[
 \boxed{\displaystyle
 P_{\rm tree}(k,b):=
 \sum_{i=1}^k
 \left\|\int_{A_i}x\,d\gamma_d(x)\right\|^2
       \ge\frac{(T-1)L_b}{k}.}
 \tag{17}
\]
The displayed lower bound is informative
when \(L_b>0\) and \(T\ge2\).

*Proof.* Each final cell has probability
\(1/k\). Conditioned on that cell, each
Gaussian block has mean equal to the
conditional mean \(\mu_j\) of the relevant
child split: earlier node choices depend
only on earlier blocks and future choices
depend only on later independent blocks.
Thus the total mean vector of a leaf is
the orthogonal concatenation of its
levelwise conditional means.

Let \(m_v\) be the number of leaves
below a tree node \(v\), so the
probability of reaching it is \(m_v/k\).
Grouping all \(k\) leaves by the node
at level \(\ell\) yields the exact
moment-energy identity
\[
 P_{\rm tree}(k,b)
 =\frac1k\sum_{\ell}
       \sum_{v\text{ at level }\ell}
          \frac{m_v}{k}\,E(q^{(v)}).
 \tag{18}
\]
Only internal nodes contribute; terminal
leaves have zero conditional mean in
unused later blocks. For each of the
first \(T-1\) levels, every node has
\(b\) children, hence \(E(q^{(v)})\ge L_b\).
The node probabilities at a fixed such
level sum to \(1\). Each of these levels
therefore contributes at least \(L_b/k\).
All other contributions are nonnegative,
proving (17). \(\square\)

## 4. Constructive logarithmic-dimensional relative saturation

**Theorem 5 (dimension \(O_\varepsilon(\log k)\)
suffices for any fixed relative accuracy).**
For every \(0<\varepsilon<1\), choose
an integer \(b=b_\varepsilon\) large enough that
\[
       L_b>0,\qquad
       \frac{L_b}{2\log b}\ge1-\frac\varepsilon2.
 \tag{19}
\]
Such integers exist by Lemma 3.
For all integers
\[
            k\ge K_\varepsilon:=b^{\lceil2/\varepsilon\rceil}
 \tag{20}
\]
the explicit balanced-threshold partition
constructed above uses
\[
 d=(b-1)\lceil\log_b k\rceil
          \le\frac{2(b-1)}{\log b}\log k
 \tag{21}
\]
Gaussian coordinates and satisfies
\[
 \boxed{\displaystyle
 P_{\rm tree}(k,b)\ge
          (1-\varepsilon)F_\infty(k).}
 \tag{22}
\]
No restriction that \(k\) be a power
of \(b\) is imposed.

*Proof.* The universal Gaussian
exponential-moment inequality (5)
gives the exact one-cell ceiling
\[
 F_\infty(k)\le
 U_k=\frac{h(1/k)^2}{k}
       \le\frac{2\log k}{k}.
 \tag{23}
\]
By (17) and
\(T-1\ge(\log k/\log b)-1\),
\[
 \frac{P_{\rm tree}(k,b)}{U_k}
 \ge\frac{(T-1)L_b}{2\log k}
 \ge\frac{L_b}{2\log b}
       \left(1-\frac{\log b}{\log k}\right).
\]
The hypotheses (19)--(20) make each
factor at least \(1-\varepsilon/2\);
their product is at least \(1-\varepsilon\).
Since \(F_\infty(k)\le U_k\), (22) follows.
The dimension estimate uses
\(T\le1+\log_b k\le2\log_b k\)
for \(k\ge b\). \(\square\)

The theorem is **constructive** at the level of
exact Gaussian quantiles; its constants may be
large, and no claim is made that the factor
\(2(b-1)/\log b\) is close to optimal.
The dependency \(b_\varepsilon\) can be
certified using rational bounds for logarithms
in the companion script, rather than
floating-point guesses.


## 5. An exact Gaussian information-theoretic upper bound

The construction above is an upper-dimensional result.
There is also a **sharp structural obstruction**
that applies to every measurable partition
in every dimension, not only to our tree.

For a probability vector \(p\), write
\[
 H(p)=\sum_i p_i\log(1/p_i),\qquad
 p_{\max}=\max_i p_i.
\]

**Theorem 6 (Gaussian rate–distortion converse).**
For every \(d\ge1\), every positive mass vector
\(p\), and every measurable Gaussian partition
with masses \(p_i\),
\[
 \boxed{\displaystyle
 P(\mathcal A)
 \le p_{\max}\,d
      \left(1-\exp\left[-\frac{2H(p)}d\right]\right).
 }                                                        \tag{24}
\]
In the equal-mass case this becomes
\[
 \boxed{\displaystyle
 F_d(k)\le \frac d k
                  (1-k^{-2/d}).}                         \tag{25}
\]
The result is independent of any regularity,
convexity, or conical hypothesis.

*Proof.* Let \(X\sim N(0,I_d)\) and
\(Y\in\{1,\dots,k\}\) be its deterministic
partition label. Write
\[
 \mu_i=\mathbb E[X\mid Y=i],\qquad
 \Sigma_i=\operatorname{Cov}(X\mid Y=i),
 \qquad D=\sum_i p_i\operatorname{tr}\Sigma_i.
\]
Every conditional distribution has a density,
finite second moment, and positive-definite
covariance because it is the restriction
of a positive Gaussian density to a set of
positive Lebesgue measure.

The Gaussian maximum-differential-entropy
inequality, proved from nonnegativity of
relative entropy to a Gaussian with matching
mean and covariance, yields
\[
 h(X\mid Y=i)
 \le\frac12\log\big((2\pi e)^d\det\Sigma_i\big)
 \le\frac d2
    \log\frac{2\pi e\,\operatorname{tr}\Sigma_i}d.
\]
Average with weights \(p_i\), and use
the concavity of logarithm:
\[
 h(X\mid Y)
 \le\frac d2\log(2\pi e\,D/d).
\]
Since \(Y\) is a deterministic function of \(X\),
\(I(X;Y)=H(p)\). Moreover
\(h(X)=\frac d2\log(2\pi e)\).
Thus
\[
 H(p)=h(X)-h(X\mid Y)
       \ge\frac d2\log(d/D),
 \qquad D\ge d e^{-2H(p)/d}.
\]
The total second-moment decomposition
(conditional expectation is orthogonal in
\(L^2\)) gives
\[
 \sum_i p_i\|\mu_i\|^2=d-D
       \le d(1-e^{-2H(p)/d}).
\]
Finally,
\[
 P(\mathcal A)=
     \sum_i p_i^2\|\mu_i\|^2
 \le p_{\max}\sum_i p_i\|\mu_i\|^2,
\]
proving (24). When \(p_i=1/k\),
the last inequality is an identity and
\(H(p)=\log k\), giving (25). \(\square\)

This is a standard information-theoretic
Gaussian rate–distortion mechanism,
adapted here to the exact squared-centroid
objective. We do not assert it is
historically new.

## 6. Optimality of the logarithmic dimension order

Define, for \(c>0\),
\[
              f(c)=\frac c2(1-e^{-2/c}).
 \tag{26}
\]
This function is strictly increasing from \(0\)
to \(1\), since
\[
 f'(c)=\frac12\left[
             1-(1+2/c)e^{-2/c}\right]>0.
\]
For \(0<\varepsilon<1\) there is a unique
\(c_\varepsilon>0\) satisfying
\(f(c_\varepsilon)=1-\varepsilon\).
For small \(\varepsilon\),
\(c_\varepsilon=\varepsilon^{-1}+O(1)\),
by expanding \(e^{-2/c}\).

**Theorem 7 (logarithmic-dimensional converse).**
Let \(d_k\) be any sequence of dimensions.
If there exist Gaussian partitions of
\(\mathbb R^{d_k}\) into \(k\) equal-mass
cells with
\[
 P(\mathcal A_k)\ge(1-\varepsilon)F_\infty(k)
\]
for all sufficiently large \(k\), then
\[
 \boxed{\displaystyle
 \liminf_{k\to\infty}\frac{d_k}{\log k}
               \ge c_\varepsilon.}         \tag{27}
\]
In particular the \(O_\varepsilon(\log k)\)
upper dimension in Theorem 5 is
**optimal in order of growth**.

*Proof.* The published arbitrary-mass envelope
(2) together with elementary Gaussian Mills
asymptotics gives
\[
 F_\infty(k)
    =\frac{2\log k-\log\log k+O(1)}k,
 \quad
 \frac{kF_\infty(k)}{2\log k}\to1.
 \tag{28}
\]
For any subsequence on which
\(d_k/\log k\to c\in(0,\infty)\),
Theorem 6 gives
\[
 \limsup\frac{kP(\mathcal A_k)}{2\log k}
       \le f(c).
\]
If \(d_k/\log k\to0\), the same ratio
tends to zero, since
\(P\le d_k/k\). Thus any subsequential
limit \(c<c_\varepsilon\) contradicts
the assumed relative lower bound.
The same argument for all possible
subsequences proves (27). \(\square\)

## 7. A second, strictly larger dimension scale

A constant-fraction objective can be attained
in dimension \(\Theta(\log k)\).
To preserve the **global second logarithmic
term**, substantially more coordinates are
necessary.

**Theorem 8 (necessary dimension for bounded
additive global gap).**
Suppose there is a constant \(C<\infty\)
and, for each sufficiently large \(k\),
a Gaussian partition of \(\mathbb R^{d_k}\)
into \(k\) equal-mass cells satisfying
\[
        P(\mathcal A_k)\ge
                  F_\infty(k)-\frac Ck.
\]
Then
\[
 \boxed{\displaystyle
 d_k\ge(2-o(1))
       \frac{(\log k)^2}{\log\log k}.}        \tag{29}
\]
More generally, if one requires
\[
 kP(\mathcal A_k)
 \ge2\log k-(1+o(1))\log\log k,
\]
then the same dimension lower bound holds.

*Proof.* Put \(L=\log k\). By (28) the
required objective implies
\[
        kP(\mathcal A_k)
                  \ge2L-\log L-O(1)
\]
for the bounded-gap assertion. For the
more general assertion the right side is
\(2L-(1+o(1))\log L\).
Theorem 6 requires
\[
 d_k(1-e^{-2L/d_k})
                 \ge2L-(1+o(1))\log L.
\]
Write \(x_k=2L/d_k\) and observe that
\[
 2L-d_k(1-e^{-x_k})
    =d_k(x_k-1+e^{-x_k})
    =2L\left[1-\frac{1-e^{-x_k}}{x_k}\right].
\]
The nonnegative quantity on the left is
at most \((1+o(1))\log L=o(L)\).
Since \((1-e^{-x})/x<1\) for every
fixed \(x>0\), this forces
\(x_k\to0\), hence \(d_k/L\to\infty\).
The Taylor expansion with its exact
alternating remainder gives
\[
 d_k(x_k-1+e^{-x_k})
 =\frac{2L^2}{d_k}(1+O(x_k)).
\]
Therefore
\[
 \frac{2L^2}{d_k}(1+o(1))
                     \le(1+o(1))\log L,
\]
which rearranges to (29). \(\square\)

This is a **necessary condition**, not
an existence theorem at the scale
\((\log k)^2/\log\log k\).
The precise minimal dimension needed
for additive \(O(1/k)\) global accuracy
remains open. Unlike the fixed-relative
accuracy setting of Theorem 5,
matching upper and lower dimensional
scales at this second level is
not established.

## 8. Exact regular-simplex product witnesses

The all-integer construction uses balanced
thresholds. For powers \(k=b^t\),
one obtains a particularly transparent
exact alternative using regular simplices.

Let \(v_1,\ldots,v_b\) be unit vertices
of a regular simplex in \(\mathbb R^{b-1}\).
Split a standard Gaussian vector by
the largest score \(\langle v_j,Z\rangle\).
Each child has probability \(1/b\), and
by symmetry its conditional mean is
collinear with the winning simplex vertex.
Writing
\[
       m_b=\mathbb E\max_{1\le j\le b}G_j,
       \quad G_j\stackrel{\rm iid}\sim N(0,1),
\]
the score covariance identity
\(\langle v_i,Z\rangle\overset d=
 \sqrt{b/(b-1)}(G_i-\bar G)\)
shows that the conditional mean
has squared magnitude
\[
                  e_b=\frac b{b-1}m_b^2.
\]

**Theorem 9 (exact b-ary simplex product).**
For every integers \(b\ge2,t\ge1\),
\(k=b^t\), there is an exactly
equiprobable \(k\)-cell partition in
\(d=t(b-1)\) Gaussian dimensions with
\[
 \boxed{\displaystyle
 P_{\rm simplex-product}
  =\frac{t}{k}\frac b{b-1}m_b^2.}            \tag{30}
\]
Its relative performance as \(t\to\infty\)
at fixed \(b\) is
\[
 \frac{P_{\rm simplex-product}}{F_\infty(k)}
       \longrightarrow
 \frac{b\,m_b^2}{2(b-1)\log b}.              \tag{31}
\]
This limit tends to \(1\) as
\(b\to\infty\).

*Proof.* Use \(t\) independent Gaussian
blocks of dimension \(b-1\).
Each block chooses one of \(b\)
simplex cells of mass \(1/b\).
The product partition has \(b^t\)
equal-mass cells. Conditioned on a
leaf, the \(t\) blocks remain independent
and their conditional means have orthogonal
coordinates, each of squared norm \(e_b\).
The first moment of each leaf therefore
has squared norm \(k^{-2}t e_b\),
and summing over \(k\) leaves proves (30).

Since \(F_\infty(k)\sim2\log k/k
       =2t\log b/k\), formula (31) follows.
Elementary Gaussian maximum tail estimates
give \(m_b\sim\sqrt{2\log b}\):
for any fixed \(\eta>0\), a union bound
and the upper normal tail bound imply
\(\max_jG_j\le(1+\eta)\sqrt{2\log b}\)
with probability tending to one;
the lower Mills bound implies the maximum
exceeds \((1-\eta)\sqrt{2\log b}\)
with probability tending to one.
Integrating the same Gaussian tail
bounds controls the two exceptional tails,
giving expectation convergence.
Thus the right side of (31) tends to one.
\(\square\)

For \(b=2\) one has
\(m_2=1/\sqrt\pi\), so (30)
recovers the exact orthant partition
value \(2t/(\pi 2^t)\). This is a
useful independent normalization check.


## 9. The one-pass staircase has an exact additive asymptotic barrier

The preceding constructions demonstrate why the
universal additive constant in the companion
arbitrary-mass theorem cannot simply be improved
by a tighter analysis of the **same fixed-order
staircase partition** in the equal-mass case.
This is not a lower bound on the true optimum.

Let \(\mathcal S_k\) be the one-pass
coordinate-threshold staircase partition
from the mass-envelope companion with
\(p_i=1/k\) for \(1\le i\le k\).
Define
\[
        g(m)=h(1/m)^2\ (m\ge2),\qquad
        U_k=\frac{g(k)}k.
\]

**Theorem 10 (exact formula and sharp construction loss).**
The staircase objective has the exact form
\[
 \boxed{\displaystyle
 P(\mathcal S_k)
 =\frac1{k^2}\sum_{m=2}^k
                       \frac{m}{m-1}g(m).}   \tag{32}
\]
Furthermore,
\[
 \boxed{\displaystyle
 \lim_{k\to\infty}
       k\left(U_k-P(\mathcal S_k)\right)=2.}
 \tag{33}
\]
Thus the companion theorem's universal
upper bound \(U(p)-P_{\rm stair}(p)\le2Q(p)\)
is asymptotically sharp **as a statement
about that particular construction**,
already for uniform masses. It does
not imply the universal coefficient
\(2\) is optimal for \(\mathcal M_d(p)\).

*Proof of the finite identity.* In the
one-pass staircase, the \(j\)-th Gaussian
threshold has conditional survival
probability \(1/m\), where
\(m=k-j+1\). The \(j\)-th cell's
conditional mean has squared component
\(g(m)\) in its own coordinate, and
each of the \(m-1\) later cells has
the same earlier-coordinate mean
\(-h(1/m)/(m-1)\):
this follows from
\(\mathbb E[Z\mathbf1_{\{Z<t\}}]=-\varphi(t)\)
and the exact Gaussian survival products.
Because every final cell has mass \(1/k\),
the entire contribution of that coordinate
to the objective is
\[
 \frac1{k^2}\left[
    g(m)+(m-1)\frac{g(m)}{(m-1)^2}\right]
 =\frac1{k^2}\frac m{m-1}g(m).
\]
Sum over \(m=2,\dots,k\), proving (32).

*Proof of the limit.* From (6), as
\(m\to\infty\),
\[
 \frac{d\,h(1/m)^2}{d\log m}\to2,\qquad
    0<\frac{d\,h(1/m)^2}{d\log m}<2.
 \tag{34}
\]
In particular \(0\le g(m)\le2\log m\)
by (5). Formula (32) gives
\[
 \begin{aligned}
 k(U_k-P(\mathcal S_k))
 &=\frac{g(k)}k
   +\frac1k\sum_{m=2}^k[g(k)-g(m)]\\
 &\qquad-\frac1k\sum_{m=2}^k\frac{g(m)}{m-1}.
 \end{aligned}                                \tag{35}
\]
The first term tends to zero.
The last term is bounded above by
\[
 \frac2k\sum_{m=2}^k\frac{\log m}{m-1}
                  =O\left(\frac{(\log k)^2}{k}\right)
                     \longrightarrow0.
\]
For the middle term, write \(u=m/k\).
For every fixed \(u\in(0,1]\),
the derivative convergence (34) implies
\[
               g(k)-g(\lfloor uk\rfloor)
                        \longrightarrow2\log(1/u).
\]
The uniform derivative bound in (34)
provides the dominating estimate
\[
 0\le g(k)-g(m)\le2\log(k/m).
\]
The discrete sums therefore converge
to the proper improper Riemann integral
\[
 \int_0^1 2\log(1/u)\,du=2.
\]
For completeness, split the sum at
\(m=\lfloor\delta k\rfloor\);
the range \(m\ge\delta k\) is uniformly
controlled by derivative convergence,
while the omitted range is at most
\(2\delta(1+\log(1/\delta))+o(1)\).
Let \(k\to\infty\) and then
\(\delta\downarrow0\).
Thus the middle term tends to \(2\),
giving (33). \(\square\)

**Methodological interpretation.**
The one-pass coordinate staircase is
universal over arbitrary masses and yields
an additive \(2Q(p)\) envelope, but in
the equal-mass limit it spends the entire
additive budget. A smaller universal
constant for the *true* optimum requires
additional geometric structure; the
higher-dimensional regular simplex
already improves the uniform asymptotic
loss, but its finite-\(k\) global
optimality is not established here.

## 10. Current research boundary and attribution

Theorems 5 and 7 give matching
\(\Theta_\varepsilon(\log k)\) upper and
lower dimensional orders for fixed
relative approximation. Theorem 8
gives the strictly larger
\(\Omega((\log k)^2/\log\log k)\)
necessary dimension for bounded
additive approximation. No matching
constructive upper bound at this
second scale is provided.

This is a statement about the **Gaussian
first-moment energy** (the first Hermite
level of Gaussian noise stability),
not an unrestricted positive-noise
stability optimum. Extensions to the
full correlated noise functional are
not claimed.

The Gaussian rate–distortion entropy
inequality, normal-tail expansions,
Gaussian halfspace rearrangement,
and large-normal-maximum asymptotics
are classical. We combine them with
an exact balanced threshold tree and
give the proof specifically for the
equal-mass multi-cell Gaussian
centroid objective. Whether equivalent
constructions or dimension-rate bounds
have appeared previously requires
further literature investigation.
No world-first or priority assertion
is made.

The full source, a rational-arithmetic
checker for the finite combinatorial
and logarithmic inequalities, and
a negative-control audit are included
in the repository. Numerical checks
are **not** used as proofs of the
universal theorems.

