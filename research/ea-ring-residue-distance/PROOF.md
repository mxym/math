# Exact residue reduction and the distance-failure exponent

## 1. Model and statement

A ring in this note is finite, commutative, has an identity, and is
not the zero ring. Fix such a ring \(R\) of order \(Q\). Let \(A_N\)
be the lower triangular \(N\)-by-\(N\) matrix with all entries
on and below the diagonal equal to 1. For \(i\in[n]\) and \(j\in[N]\),
the entries \(B_{ij}\) are independent with law
\(\mathrm{Ber}_p(R)\): zero with probability \(1-p\), and a uniformly
chosen nonzero ring element otherwise. This is the Bernoulli law
of [BCGIKRS, §2.2 and Definition 3.2], not a law on units and not
a fixed-row-weight distribution. Set \(G=BA_N\), so multiplication
of a row vector by \(A_N\) gives suffix sums (equivalently, reverse
the coordinate order and view them as prefix sums).

For a matrix \(G\) over \(R\) put
\[
 \Delta_R(G)=\min_{x\in R^n\setminus\{0\}}\operatorname{wt}(xG),
\]
which is zero for a noninjective map. For an injective generator this
equals the ordinary minimum Hamming weight of a nonzero codeword.
For arbitrary generators the latter distance is bounded below by
\(\Delta_R(G)\). We also prove the necessary failure lower bound
using positive-weight codewords, so all asymptotic failure statements
below apply to either convention.

Use natural logarithms and
\[
\begin{split}
 h(\delta)&=-\delta\ln\delta-(1-\delta)\ln(1-\delta),\\
 H_q(\delta)&=\frac{h(\delta)+\delta\ln(q-1)}{\ln q},\\
 J_q(\delta)&=\left(\sqrt{(1-1/q)(1-\delta)}
                     -\sqrt{\delta/q}\right)^2.
\end{split}
\]
Let \(q_*\) be the smallest size of a residue field \(R/\mathfrak m\),
\(\zeta=Q/(Q-1)\), \(p=C\ln N/N\) for fixed \(C>0\), and
\(n/N\to\rho\in(0,1)\). Fix \(0<\delta<1-1/q_*\) and suppose
\(\rho<1-H_{q_*}(\delta)\). Write \(A=C\zeta J_{q_*}(\delta)\).
For \(F_N=\{\Delta_R(G)<\delta N\}\), or the version with a
non-strict inequality, we prove
\[
\begin{array}{c|l}
 A<1 & \Pr(F_N)\to1,\\
 A=1 & \Pr(F_N)\to0,\quad \ln\Pr(F_N)/\ln N\to0,\\
 A>1 & \Pr(F_N)=N^{1-A+o(1)},\quad \Pr(F_N)=O(N^{1-A}).
\end{array} \tag{1}
\]
The shared lower bound does not need the strict GV margin. The
success statements do. All size thresholds and implicit constants
may depend on the **fixed** ring, \(\rho,C,\delta\). No tight
probability prefactor or dense-side converse at the GV bound is
asserted.

## 2. Exact algebraic reduction and random ensemble

For every matrix \(G\), independently of its distribution,
\[
 \Delta_R(G)=\min_{\mathfrak m}
             \Delta_{R/\mathfrak m}(G\bmod\mathfrak m). \tag{2}
\]
Indeed, a finite commutative ring is a product of finite local
rings. One proof uses nilpotence of its Jacobson radical:
its descending powers stabilize, and Nakayama's lemma makes the
stable power zero. Distinct maximal ideals are pairwise comaximal,
as are their powers, so the Chinese remainder theorem applied to
sufficiently high powers gives the indicated local factors. Over a
product, each row message is a tuple of factor messages, and the
support is the union of the factor supports. Taking a message
supported in only a minimizing factor gives equality with the
minimum of the local margins.

Suppose then that \(R\) is local with maximal ideal \(\mathfrak m\)
and residue field \(K\). For any nonzero \(x\in R^n\), take the
largest \(\ell\) with \(x\in(\mathfrak m^\ell)^n\).
The image of \(x\) in \((\mathfrak m^\ell/\mathfrak m^{\ell+1})^n\)
is nonzero. This quotient is a \(K\)-vector space, since
\(\mathfrak m\) annihilates it. Pick a \(K\)-linear functional
\(\phi\) which is nonzero on at least one entry of that image.
Entrywise application to \(xG\) gives
\(\phi(xG)=\phi(x)(G\bmod\mathfrak m)\).
Its support is contained in the original support, and
\(\phi(x)\ne0\), giving the lower bound for (2).

For the upper bound let \(\omega\ne0\) lie in the last nonzero
power of \(\mathfrak m\). Its annihilator is exactly \(\mathfrak m\):
the ideal kills it, and a unit cannot kill it. Multiplying lifts by
\(\omega\) embeds \(K\) additively and as an \(R\)-module into \(R\),
sending nonzero symbols to nonzero symbols. Lift a minimizing
nonzero residue-field message in this way; its output has exactly
the residual weight. In particular any **positive**-weight residue
output lifts to a positive-weight output of exactly that weight.
This uses no chain assumption on the local ring. Without the
injectivity convention (2) need not hold, as the accompanying
negative control with a \(2\)-by-\(3\) matrix over \(\mathbb Z/4\)
illustrates.

For all sufficiently large \(N\), \(a=\zeta p\) lies in \((0,1)\).
An entry has exactly the mixture law
\((1-a)\delta_0+a U_R\), where \(U_R\) is uniform on the entire
ring, because \(a/Q=p/(Q-1)\). Projecting to any residue field of
order \(q\) gives \((1-a)\delta_0+a U_q\). The equivalent
Bernoulli nonzero density in that field is \(a(1-1/q)\).
The projected **entries** remain independent, but different
residue-field matrices need not be independent.

In one projected field, fix a nonzero message of weight \(r\).
Each nonzero message coordinate multiplies a uniform field
symbol to another uniform one. Thus the independently sampled
columns yield independent increments with law
\[
 (1-u_r)\delta_0+u_r U_q,\qquad
 u_r=1-(1-a)^r. \tag{3}
\]
On a uniform refresh, adding to the state again gives an independent
uniform field element. The indicator of a nonzero accumulated
symbol is exactly a two-state Markov chain starting at zero with
transition
\[
 T_u=(1-u)I+u\mathbf 1\pi^\top,\qquad
 \pi=(\alpha,b)=(1/q,1-1/q).
 \tag{4}
\]
The number \(W_N\) of ones among the first \(N\) new states is the
output weight. Here \(u=u_r\). Formula (4) is the same transfer
underlying the fixed-field results of [Rin26], with a
full-field-refresh rather than a nonzero-increment parameter.

## 3. Sparse tilted tails and the critical line

Write \(Y_N=W_N/N\) and \(L=Nu\). With the marker
\(D_s=\operatorname{diag}(1,e^{su})\), its moment generating
function is
\[
 M_N(s)=\mathbb E e^{s L Y_N}=e_0^\top(T_uD_s)^N\mathbf 1.
\]
Let \(\Pi=\operatorname{diag}(\alpha,b)\) and
\(V=(\sqrt\alpha,\sqrt b)^\top\). The symmetric matrix similar to
\(T_uD_s\) is
\[
 B_s=D_s^{1/2}[(1-u)I+u VV^\top]D_s^{1/2}.
\]
It is positive semidefinite for \(0\le u\le1\). The start and end
vectors in the symmetric coordinates are
\(e_0^\top/\sqrt\alpha\) and \(D_s^{1/2}V\).
Consequently for \(s\le0\), \(M_N(s)\le\sqrt q\,\lambda_+(s,u)^N\).

For \(u\downarrow0\), uniformly on a compact interval of real \(s\),
\[
 B_s=I+u\begin{pmatrix}-b&\sqrt{\alpha b}\\
                    \sqrt{\alpha b}&-\alpha+s\end{pmatrix}+O(u^2),
 \qquad
 \lambda_+(s,u)=1+u\kappa(s)+O(u^2),
\]
where
\[
 \kappa(s)=\tfrac12(s-1+\sqrt{(s+b-\alpha)^2+4\alpha b}).
\]
In particular \(\kappa'(0)=b\) and
\(\kappa''(s)=2\alpha b((s+b-\alpha)^2+4\alpha b)^{-3/2}>0\).
At \(0<\delta<b\) the solution to \(\kappa'(s)=\delta\) is
\(s_\delta=(2\delta-1)\sqrt{\alpha b/(\delta(1-\delta))}
-(b-\alpha)<0\). Substitution gives
\(s_\delta\delta-\kappa(s_\delta)=J_q(\delta)\).
Chernoff with this fixed marker yields, for sufficiently small \(u\),
\[
 \Pr(Y_N\le\delta)\le
  \sqrt q\,\exp(-N u J_q(\delta)+O(Nu^2)). \tag{5}
\]
For later use, there are constants \(c>0,K>0\) depending only on
\(q,\delta\) such that for every \(0<u\le1\),
\[
 \Pr(Y_N\le\delta)\le K e^{-cNu}. \tag{6}
\]
For small \(u\) this follows from (5). For \(u\) bounded below,
take the marker \(D=\operatorname{diag}(1,e^\theta)\) with a small
negative \(\theta\) independent of \(u\). At \(\theta=0\), the
symmetric top eigenvalue is 1, has gap \(u\), and
\(\partial_\theta\ln\lambda_+(0,u)=V^\top
\operatorname{diag}(0,1)V=b\). Continuity on the compact range
of \(u\) makes this derivative uniformly greater than
\((b+\delta)/2\) on a short interval below 0. Integrate and apply
Chernoff to obtain \(K e^{-cN}\), which gives (6).

### 3.1. Matching lower exponent

For every fixed \(r\ge1\),
\(u=u_r\sim r C\zeta\ln N/N\), so \(L\to\infty\) and
\(Nu^2\to0\). The spectral gap of \((B_s-I)/u\) is bounded below
on every compact \(s\)-interval. Its Perron projector converges
uniformly to that of the matrix in the display above, whose
entries off the diagonal are strictly positive. The limiting
projection between the start and end vectors gives a continuous
factor \(c(s)>0\). For large \(N\), the second eigenvalue contribution
is relatively \(O(e^{-c_0 L})\), since the eigenvalue ratio is
at most \(1-c_0u\), uniformly on such an interval. Thus
\[
 \ln M_N(s)= L\kappa(s)+\ln c(s)+o(1), \tag{7}
\]
uniformly on compact \(s\)-intervals.

For \(0<y<\delta\), take \(s_y\) with \(\kappa'(s_y)=y\)
and tilt the law by \(e^{s_y L Y_N}/M_N(s_y)\).
Under the tilted law, \(Y_N\to y\) in probability: both tails
outside \([y-\nu,y+\nu]\) have exponentially small probability
in \(L\), by (7), differentiability of \(\kappa\), and Chernoff
with a sufficiently small positive or negative additional
parameter. Choose \(\nu>0\) with this interval inside
\((0,\delta)\). Undoing the tilt on it gives
\[
 \liminf \frac{1}{L}\ln\Pr(0<Y_N<\delta)
 \ge -J_q(y)-|s_y|\nu .
\]
Let \(\nu\downarrow0\) and \(y\uparrow\delta\). Together with (5),
this proves
\[
 \Pr(0<W_N<\delta N)=N^{-r C\zeta J_q(\delta)+o(1)}
 \quad\text{for each fixed }r. \tag{8}
\]

### 3.2. Fixed-weight critical-line lemma

For each fixed \(r\), tilt by \(s=s_\delta\).
The moment generating function of
\(\sqrt L(Y_N-\delta)\) under the tilted law has logarithm
\[
 \ln M_N(s+t/\sqrt L)-\ln M_N(s)-t\sqrt L\,\delta
     \longrightarrow t^2\kappa''(s)/2 .
\]
This follows directly by Taylor expansion in (7), since the
continuous \(c\) factors cancel, and the remainder is uniform.
By the classical moment-generating-function convergence theorem
[Curtiss], the limit under the tilted law is a nondegenerate
centered normal. In particular the interval
\([\delta-L^{-3/4},\delta]\) has tilted probability \(o(1)\):
after scaling it shrinks to a point at which the limiting normal
has no atom. Undoing the tilt,
\[
 \Pr(Y_N\le\delta)
 =M_N(s)e^{-s L\delta}\,
   \mathbb E_s[\,\mathbf 1_{Y_N\le\delta}
                        e^{s L(\delta-Y_N)}\,].
\]
The expectation is \(o(1)\), since it is bounded by the tilted
interval probability plus \(e^{s L^{1/4}}\). Also
\(L=r C\zeta\ln N+o(1)\) for fixed \(r\). We obtain
\[
 \Pr(W_N\le\delta N)=o(N^{-r C\zeta J_q(\delta)})
 \quad\text{for each fixed }r. \tag{9}
\]

## 4. Union over message weights

Work first in one projected field of order \(q\), with the common
\(a=\zeta p\). Let \(A_q=C\zeta J_q(\delta)\) and assume
\(A_q\ge1,\ \rho<1-H_q(\delta)\). There are
\(\binom nr(q-1)^r\) messages of weight \(r\).

1. For \(1\le r\le N/\ln^2 N\), \(u_r=ar+O((ar)^2)\) uniformly.
   Since \(N(ar)^2=O(r)\) throughout this range, (5) yields
   \(\Pr(W_N\le\delta N)\le \sqrt q N^{-r A_q}e^{K_0r}\)
   for constant \(K_0\). After multiplying by the message count,
   each summand is at most \(\sqrt q (K_1 N^{1-A_q})^r/r!\)
   for constant \(K_1\). If \(A_q>1\) their sum is
   \(O(N^{1-A_q})\). If \(A_q=1\), this factorial bound is
   summable uniformly. For each fixed \(r\) the summand tends
   to zero by (9), hence the sum tends to zero.
2. For \(N/\ln^2 N<r\le N/\ln N\), \(ar\) is bounded above by
   a constant, so \(u_r\ge1-e^{-ar}\ge c_1 ar\) for some
   constant \(c_1>0\). By (6) the per-message penalty is
   \(\exp(-\Omega(r\ln N))\). The count is at most
   \((en(q-1)/r)^r=\exp(O(r\ln\ln N))\); this range contributes
   less than any inverse power of \(N\).
3. For \(N/\ln N<r<\eta N\), \(u_r\) is bounded away from zero,
   so (6) gives \(\exp(-c_2N)\) for some \(c_2>0\).
   The bound \(\binom nr\le\exp(nh(r/n))\) gives at most
   \(\exp(c_2N/2)\) messages at each such weight if the fixed
   \(\eta>0\) is chosen sufficiently small. This contribution
   is exponentially small.
4. For \(r\ge\eta N\) in the remaining range, the exact
   field-state refresh transition in (3) has all entries
   at most \((1+(q-1)(1-u_r))/q\). Since
   \(1-u_r=(1-a)^r=o(1)\) uniformly here, the probability of
   any field-state output path from zero is at most its
   independent-uniform probability times
   \((1+(q-1)(1-u_r))^N=\exp(o(N))\).
   The uniform lower-weight event has probability at most
   \(\exp(-N(\ln q-h(\delta)-\delta\ln(q-1))+O(\ln N))\)
   by the Hamming volume estimate. The total over no more
   than \(q^n\) messages is exponentially small by the strict
   GV inequality.

For \(q\ge q_*\) and \(0<\delta<1-1/q_*\) we have
\(J_q(\delta)\ge J_{q_*}(\delta)\) by the explicit square-root
formula: the difference being squared is positive and increasing
in \(q\). Also \(H_q(\delta)\le H_{q_*}(\delta)\). To see the latter,
differentiate with respect to \(\ln q\): its derivative has the
sign of
\(\delta[q\ln q/(q-1)-\ln(q-1)]-h(\delta)\).
The bracket decreases in \(q\) (derivative
\(-\ln q/(q-1)^2\) with respect to \(q\)).
At \(q=q_*\) it equals
\(h(1-1/q_*)/(1-1/q_*)\).
The function \(h(x)/x\) decreases for \(0<x<1\), so the
derivative is negative as required. The finite union of the upper
bounds just obtained therefore applies via (2), including
at \(A=1\). No independence between different residual factors is
needed.

For the converse use one factor attaining \(q_*\). Distinct
weight-one messages supported on separate rows have independently
sampled output weights over that one factor. Each row has
probability \(v_N=N^{-A+o(1)}\) of producing **positive** weight
less than \(\delta N\), by (8) with \(r=1\).
Each such codeword lifts by (2). The chance that some row
does this is \(1-(1-v_N)^n\). It tends to one for \(A<1\)
and is \(N^{1-A+o(1)}\) for \(A>1\). At \(A=1\) it is bounded
below by \(N^{-o(1)}\) (use \(1-e^{-x}\ge c\min(1,x)\)
for \(x\ge0\)). Together with the upper bounds this proves (1).
The statement for ordinary image distance uses the same
positive-weight lower event and the margin upper bound.

## 5. Original binary comparison and the ring-size scope

The original binary Theorem 3.10 has
\(\beta=1/2-\delta>0\), \(C>1/\beta^2\), and its displayed
rate condition (3). The latter implies \(\rho<1-H_2(\delta)\):
\(\ln 2-h(\delta)\ge2\beta^2\) (binary Pinsker, or integrate
\(h''(x)=-1/[x(1-x)]\le-4\)).
Moreover
\[
 J_2(\delta)
 =\tfrac12-\sqrt{\tfrac14-\beta^2}
 =\frac{\beta^2}{\tfrac12+\sqrt{\tfrac14-\beta^2}}
 \ \ge\ \beta^2 .
\]
Since \(\zeta\ge1\) and \(J_{q_*}\ge J_2\), the same rate and
density conditions do imply high-probability distance over
every fixed finite commutative ring, without a rate loss in
\(\ln|R|\). They do **not** give the binary failure bound.

For a specific comparison take \(R=\mathbb Z/4\mathbb Z\),
\(\rho=1/100,\delta=1/4,C=64\); \(N\) may run through multiples
of 100 to match the exact rate of the original.
Then \(\beta^2=1/16\), \(C>16\), and the right side of the
original rate constraint (3) exceeds \(1/24>1/100\), using
\(e>2\) and \(\ln2<1\). The binary bound (5) in [BCGIKRS]
requires failure \(O(N^{-6})\). But \(q_*=2,\zeta=4/3\) here, and
\[
 A=\frac{64}{3}(2-\sqrt 3)=5.716249439\ldots<7 .
\]
The strict inequality is exact, as \((107/64)^2<3\).
By (1) the \(\mathbb Z/4\) failure probability is
\(N^{1-A+o(1)}\), asymptotically larger than any fixed multiple of
\(N^{-6}\). This refutes the unchanged bound (5) and also the unchanged
union estimate actually used to prove it (the source's (7),
including its factor \(N\beta^2\) in the exponent). The
contradiction works for the ordinary nonzero-codeword convention. At the same
\(\rho,\delta\) but \(C=9\), binary has
\(18J_2(\delta)>1\) and \(\mathbb Z/4\) has
\(12J_2(\delta)<1\), using \(5/3<\sqrt 3<16/9\).
The binary generator then reaches the target with probability
tending to one, whereas the \(\mathbb Z/4\) generator fails it with
probability tending to one. This latter choice is outside the
original sufficient condition (4) and is stated separately.

**Why fixed ring matters.** There cannot be uniform positive
distance over all commutative rings allowed to grow arbitrarily
with \(N\), at the same \(C\) and fixed \(\rho>0\). For example set
\(R_N=\mathbb F_2^{M_N}\) with \(M_N=\lceil e^N\rceil\).
Choose Bernoulli-\(p\) support bits and first use independent
uniform labels in \(R_N\) at active positions. Coupling by
resampling only an all-zero label yields the desired distribution
with probability of any change at most \(nN\,2^{-M_N}\).
With probability tending to one some row has a support position
in column 1, since \(np\to\infty\); fix the first such row from
the support alone. In any fixed residue projection, its active
labels have independent fair bits. The event that only its
column-1 label projects to 1 has probability at least \(2^{-N}\)
and is independent across the \(M_N\) projections conditional
on the support. Hence some projection has that pattern with
probability at least \(1-e^{-M_N2^{-N}}\to1\).
The suffix accumulation of that projected row has weight one,
and taking the corresponding idempotent-supported ring message
gives an actual weight-one word. This family is not needed for
the fixed-ring refutation above. If the nonzero labels were
instead required to be units, the law would be different.

The proofs concern only the Hamming distance of this abstract
random matrix ensemble. No conclusion about a decoder, a
computational assumption or a concrete protocol is made.
