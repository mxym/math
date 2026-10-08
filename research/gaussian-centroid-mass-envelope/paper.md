# Gaussian centroid partitions with arbitrary prescribed masses:
# a universal two-times-collision-probability approximation

*Standalone mathematical research note · 7 October 2026 (PDT)*
  
## Abstract

For any positive probability vector \(p=(p_1,\ldots,p_k)\) and
\(d\ge k-1\), consider the maximum
\[
 \mathcal M_d(p)=
 \sup_{\substack{\mathbb R^d=\bigsqcup_{i=1}^k A_i\\
                  \gamma_d(A_i)=p_i}}
       \sum_{i=1}^k
         \left\|\int_{A_i}x\,d\gamma_d(x)\right\|^2.
\]
Set \(t_i=\Phi^{-1}(1-p_i)\), \(\varphi(t)=(2\pi)^{-1/2}e^{-t^2/2}\),
\(U(p)=\sum_i\varphi(t_i)^2\), and \(Q(p)=\sum_i p_i^2\).

**Main theorem.** For *every* positive mass vector,
\[
 \boxed{\quad U(p)-2Q(p)\le \mathcal M_d(p)\le U(p)
                      \qquad(d\ge k-1).\quad} \tag{1}
\]
The lower bound comes from an explicit disjoint, axis-aligned,
sequential-threshold partition; it does *not* assume any
Gaussian simplex conjecture. The gap of at most \(2Q(p)\) is
dimension- and mass-distribution-independent.

We also establish the fully explicit mass-entropy approximation
\[
 B(p)-6Q(p)\le\mathcal M_d(p)\le B(p)+3Q(p),\qquad
 B(p)=\sum_i p_i^2\left[
 2\log\frac1{p_i}-\log^+\!\log\frac1{p_i}\right],               \tag{2}
\]
where \(\log^+ u=\max(0,\log u)\) for \(u>0\).
This determines the leading two logarithmic terms of the
unrestricted Gaussian first-moment optimum for **all** small,
even highly nonuniform prescribed masses, with an absolute
remainder proportional to \(Q(p)\).

The input problem and classical one-cell Gaussian halfspace
bound have historical antecedents. Originality and publication
priority are not asserted prior to a full literature review.

---

## 1. Statement and exact construction

Let \(k\ge2\), \(p_i>0\), \(\sum_i p_i=1\).
We optimize over measurable ordered partitions modulo
\(\gamma_d\)-null sets. No convexity, conical restriction,
regularity, symmetry, or equality of cell masses is assumed.
Write \(Z\sim N(0,1)\),
\[
 \varphi(t)=(2\pi)^{-1/2}e^{-t^2/2},\qquad
 \overline\Phi(t)=\Pr(Z\ge t),\qquad
 t_q=\overline\Phi^{-1}(q),\quad
 h(q)=\frac{\varphi(t_q)}q \quad(0<q<1).
 \tag{3}
\]
Thus \(h(q)=\mathbb E[Z\mid Z\ge t_q]\),
and \(U(p)=\sum_i p_i^2h(p_i)^2\).

Relabel the prescribed masses so
\(p_1\ge p_2\ge\cdots\ge p_k>0\),
and put
\[
 S_i=\sum_{j=i}^k p_j,\quad S_1=1,\quad
 q_i=\frac{p_i}{S_i}\in(0,1)\quad(1\le i<k).
 \tag{4}
\]
In \(\mathbb R^{k-1}\), with standard independent Gaussian
coordinates \(Z_1,\ldots,Z_{k-1}\), define the staircase cells
\[
 \begin{aligned}
 A_i&=\bigcap_{j<i}\{Z_j<t_{q_j}\}
                 \cap\{Z_i\ge t_{q_i}\}
                   &&(1\le i<k),\\
 A_k&=\bigcap_{j<k}\{Z_j<t_{q_j}\}.
 \end{aligned} \tag{5}
\]
These cells are disjoint and exhaust the space, up to a
union of Gaussian-null coordinate hyperplanes.

**Lemma 1 (exact masses and diagonal moments).**
The cells (5) satisfy, identically,
\[
  \gamma_{k-1}(A_i)=p_i\quad(1\le i\le k),
  \qquad
  \int_{A_i}x_i\,d\gamma_{k-1}(x)
       =p_i h(q_i)\quad(1\le i<k).
 \tag{6}
\]
Consequently, their objective \(\mathcal P_{\rm stair}(p)\)
obeys
\[
 \mathcal P_{\rm stair}(p)
       \ge\sum_{i=1}^{k-1}p_i^2 h(q_i)^2 .
 \tag{7}
\]

*Proof.* Since \(1-q_i=(S_i-p_i)/S_i=S_{i+1}/S_i\),
independence yields
\[
 \Pr(Z_j<t_{q_j}\ \forall j<i)
     =\prod_{j<i}(1-q_j)=S_i.
\]
Multiplying by \(q_i\) gives
\(\gamma(A_i)=S_iq_i=p_i\); the last
cell has mass \(S_k=p_k\).
For \(i<k\), coordinate \(Z_i\) is independent of
all earlier threshold constraints, and
\(\mathbb E[Z_i\mathbf1_{\{Z_i\ge t\}}]
       =\varphi(t)\) by one integration by parts.
Its contribution to the first moment of \(A_i\) is
\(S_i\varphi(t_{q_i})=p_i h(q_i)\).
The squared Euclidean norm dominates the square
of any specified component, proving (7). \(\square\)

**Supplement to Lemma 1 (exact staircase objective).**
The full first moments of (5) can also be expressed
without any multivariate Gaussian integration.
Writing \(b_{i,j}=\int_{A_i}x_j\,d\gamma_{k-1}\)
for \(1\le j<k\), one has
\[
 b_{i,j}=
 \begin{cases}
  0,&i<j,\\
  p_jh(q_j),&i=j,\\
  -p_i\,\dfrac{\varphi(t_{q_j})}{1-q_j},
                        &i>j.
 \end{cases}
\]
Indeed, for \(i>j\), conditioning on \(Z_j<t_{q_j}\)
gives \(\mathbb E[Z_j\mathbf1_{\{Z_j<t\}}]
=-\varphi(t)\) and the other independent
constraints have probability \(p_i/(1-q_j)\).
The exact objective is therefore
\[
 \boxed{\displaystyle
 \mathcal P_{\rm stair}(p)=
   \sum_{j=1}^{k-1}\left[
    p_j^2h(q_j)^2+
    \frac{\varphi(t_{q_j})^2}{(1-q_j)^2}
                       \sum_{i=j+1}^k p_i^2\right].}
 \tag{7a}
\]
The second, nonnegative term was deliberately omitted
from the universal envelope proof; it can strengthen
instance-specific lower certificates.

## 2. Two analytic lemmas

The first lemma is an exact, global Lipschitz property
of the Gaussian upper-tail hazard. It is the principal
analytic observation enabling a constant error bound.

**Lemma 2 (2-Lipschitz squared hazard in log tail mass).**
For every \(0<q_1\le q_2<1\),
\[
 0\le h(q_1)^2-h(q_2)^2
       \le 2\log(q_2/q_1).
 \tag{8}
\]

*Proof.* Set \(q=\overline\Phi(t)\) and \(h=\varphi(t)/q\).
Direct differentiation gives
\[
 \frac{dh}{dt}=h(h-t),\qquad
 \frac{dt}{d\log(1/q)}=\frac1h,
 \quad
 \frac{d(h^2)}{d\log(1/q)}=2h(h-t).
 \tag{9}
\]
The conditional mean of a nondegenerate random variable
supported strictly above \(t\) exceeds \(t\); hence
\(h-t>0\). The truncated standard-normal second moment
satisfies
\[
 \mathbb E[Z^2\mid Z\ge t]=1+t h,
\]
so its strictly positive variance is
\[
 \operatorname{Var}(Z\mid Z\ge t)
          =1+t h-h^2
          =1-h(h-t)>0 .
\]
Thus \(0<h(h-t)<1\). Integrating (9) over the
log-tail-mass interval proves (8). \(\square\)

**Sharpness of the analytic Lipschitz constant.**
The coefficient \(2\) in Lemma 2 cannot be
replaced by any smaller constant *in that
lemma*. To see this, integrate by parts twice:
\[
 \overline\Phi(t)=
  \varphi(t)\left(\frac1t-\frac1{t^3}
                   +O(t^{-5})\right)
       \qquad(t\to+\infty).
\]
The error follows from the exact remainder
\(3\int_t^\infty\varphi(x)/x^4\,dx\),
bounded above by \(3\varphi(t)/t^5\)
using the upper Mills inequality.
Consequently
\(h(t)=\varphi(t)/\overline\Phi(t)
=t+1/t+O(t^{-3})\) and
\(h(t)(h(t)-t)\to1\).
Equation (9) therefore gives
\(d(h^2)/d\log(1/q)\to2\) as \(q\downarrow0\).
This proves sharpness of the scalar Lipschitz
coefficient, **not** sharpness of the global
partition-envelope coefficient in Theorem 4.

The second lemma is a distribution-free weighted
entropy inequality for a decreasing probability vector.

**Lemma 3 (ordered residual-mass entropy).**
For any \(p_1\ge\cdots\ge p_k>0\), \(\sum_i p_i=1\),
and \(S_i=\sum_{j=i}^k p_j\),
\[
 \boxed{\displaystyle
 \sum_{i=1}^k p_i^2\log\frac1{S_i}
          \le\sum_{i=1}^k p_i^2=Q(p).}
 \tag{10}
\]

*Proof.* Put \(g_i=\log(1/S_i)\).
Since \(S_i\) decreases, \(g_i\) increases,
whereas \(p_i\) decreases. The weighted
negative-covariance identity is
\[
 \begin{aligned}
 &\sum_i p_i^2g_i-
    \Big(\sum_i p_i^2\Big)\Big(\sum_i p_i g_i\Big)\\
 &\hspace{5mm}=
 \frac12\sum_{i,j}p_ip_j(p_i-p_j)(g_i-g_j)
        \le0.
 \end{aligned} \tag{11}
\]
Next put \(S_{k+1}=0\). Because \(-\log s\)
decreases with \(s\in(0,1]\),
\[
 p_i\log\frac1{S_i}
   \le\int_{S_{i+1}}^{S_i}\log\frac1s\,ds.
\]
Summing the integrals gives
\[
 \sum_i p_i g_i
      \le\int_0^1\log\frac1s\,ds=1.
 \tag{12}
\]
Combining (11)--(12) proves (10). \(\square\)

## 3. Main theorem: additive two-collision-mass gap

**Theorem 4 (universal two-collision-mass centroid envelope).**
For every \(k\ge2\), \(d\ge k-1\), and positive
prescribed Gaussian cell masses \(p_i\) totaling one,
\[
 \boxed{\displaystyle
 0\le U(p)-\mathcal M_d(p)\le 2Q(p).}
 \tag{13}
\]
More precisely, the explicit partition (5), extended
cylindrically to \(\mathbb R^d\), attains objective
at least \(U(p)-2Q(p)\).

*Proof.* First, the **individual one-cell upper bound**
requires no assumption on cell shape.
If \(A\subseteq\mathbb R^d\) has Gaussian mass \(q\)
and \(b=\int_A x\,d\gamma_d\ne0\),
let \(u=b/\|b\|\) and \(H=\{x:\langle u,x\rangle\ge t_q\}\).
Then \(\gamma_d(H)=q\).
The pointwise integrand
\((\langle u,x\rangle-t_q)
 (\mathbf1_H-\mathbf1_A)\)
is nonnegative, and the threshold terms cancel
after integration because \(A,H\) have the same mass.
Therefore
\[
 \|b\|=\int_A\langle u,x\rangle\,d\gamma_d
 \le\int_H\langle u,x\rangle\,d\gamma_d
 =\varphi(t_q)=q h(q).                         \tag{14}
\]
It is also true for \(b=0\).
Applying this separately to all cells proves
\(\mathcal M_d(p)\le U(p)\).

For the lower bound, choose the decreasing order (4).
Because \(q_i=p_i/S_i\ge p_i\), Lemma 2 gives
\[
 0\le h(p_i)^2-h(q_i)^2
 \le 2\log\frac{q_i}{p_i}
 =2\log\frac1{S_i}.                           \tag{15}
\]
Multiply by \(p_i^2\), sum over \(i<k\),
and apply Lemma 1. We have
\[
 U(p)-\mathcal P_{\rm stair}(p)
 \le 2\sum_{i<k}p_i^2\log\frac1{S_i}
       +p_k^2h(p_k)^2.                       \tag{16a}
\]
The final omitted cell satisfies a stronger
bound than ordinary Cauchy--Schwarz.
For the upper-tail event \(H=\{Z\ge t_q\}\),
of mass \(q\), the Gaussian exponential
moment identity and conditional Jensen give,
for every \(\lambda\ge0\),
\[
 e^{\lambda^2/2}=\mathbb E e^{\lambda Z}
 \ge q\,\mathbb E[e^{\lambda Z}\mid H]
 \ge q\,e^{\lambda h(q)}.
\]
Taking logarithms and choosing
\(\lambda=h(q)>0\) yields
\[
 \boxed{\varphi(t_q)^2=q^2h(q)^2
              \le2q^2\log(1/q).}            \tag{16b}
\]
Since \(S_k=p_k\), the omitted contribution
is controlled by the **same residual entropy**.
Combining (16a)--(16b) with Lemma 3,
\[
 \begin{aligned}
 U(p)-\mathcal P_{\rm stair}(p)
 &\le2\sum_{i<k}p_i^2\log\frac1{S_i}
       +2p_k^2\log\frac1{p_k}\\
 &=2\sum_{i=1}^k p_i^2\log\frac1{S_i}
 \le 2Q(p).
 \end{aligned}                               \tag{16}
\]
The staircase partition is defined in exactly
\(k-1\) Gaussian coordinates. Extending it by
an independent centered Gaussian factor leaves
masses and squared first moments unchanged
for all \(d\ge k-1\). Taking the supremum
over feasible partitions proves (13). \(\square\)

**Interpretation.** Each individual Gaussian cell
of mass \(p_i\) could, in isolation, be a
halfspace with squared centroid
\(\varphi(t_{p_i})^2\). Theorem 4 proves that
we can satisfy **all** prescribed masses at once
with disjoint cells, losing at most
\(2\sum_i p_i^2\) in the sum of these
individually optimal squared moments.
No numerical search or optimization solver enters.

---
## 4. A universal scalar Gaussian quantile estimate

The additive approximation in Theorem 4 combines with
a *quantitative* elementary normal-tail estimate.
For \(0<q<1\), define
\[
 L(q)=\log\frac1q>0,\qquad
 \mathfrak b(q)=2L(q)-\max(0,\log L(q)).
 \tag{17}
\]
The positive-part logarithm avoids a spurious
\(-\log\log(1/q)\) divergence when \(q\to1\).

**Lemma 5 (sharpened universal hazard/entropy comparison).**
For every \(0<q<1\),
\[
 \boxed{\displaystyle
     \mathfrak b(q)-4
       \le h(q)^2\le\mathfrak b(q)+3.}       \tag{18}
\]
Both constants are absolute and hold without any
small-tail asymptotic assumption.

*Proof.* Set \(L=\log(1/q)\), \(t=t_q\).
By an integration by parts, for every \(t>0\)
the familiar Mills bounds are
\[
 \frac{t}{1+t^2}\varphi(t)
       \le\overline\Phi(t)
       \le\frac{\varphi(t)}t.                 \tag{19}
\]

First consider \(q\le1/10\).
Mills' lower bound at \(t=1\) gives
\(\overline\Phi(1)\ge\varphi(1)/2>1/10\);
indeed \(2\pi e<24<25\) using
\(\pi<4\) and \(e<3\).
Consequently \(t>1\) and \(L>1\).
The Mills bounds yield
\[
 t\le h(q)\le t+\frac1t,\qquad
 \frac{t^2}{2}+\log t+\frac12\log(2\pi)
 \le L\le
 \frac{t^2}{2}+\log(t+1/t)+\frac12\log(2\pi).
                                                       \tag{20}
\]
In particular \(t^2\le2L\).
Since \(t+1/t\le2\sqrt{2L}\),
the right inequality gives
\[
 t^2\ge2L-\log L-\log(16\pi).
                                                       \tag{21}
\]
To see \(\log(16\pi)<4\) with strict
elementary inequalities, note that
\(e>8/3\) and \(\pi<22/7\), while
\((8/3)^4=4096/81>352/7=16(22/7)\).
Hence \(h(q)^2\ge t^2>\mathfrak b(q)-4\).

For the upper bound, \(h(q)^2\le t^2+3\).
If \(t^2\ge L\), the left inequality
in (20) gives
\(t^2\le2L-\log L-\log(2\pi)\),
so \(h(q)^2\le\mathfrak b(q)+3\).
If \(t^2<L\), the elementary inequality
\(L-\log L\ge1\) gives
\(h(q)^2<L+3\le\mathfrak b(q)+2\).
Thus the result holds for all \(q\le1/10\).

Next suppose \(q>1/10\). Then
\(L<\log10\). Conditional Jensen applied
to \(q\,e^{\lambda h(q)}
 \le\mathbb E e^{\lambda Z}=e^{\lambda^2/2}\)
at \(\lambda=h(q)\) gives
\(h(q)^2\le2L\).
Therefore
\[
 h(q)^2-\mathfrak b(q)
       \le\max(0,\log L)
       \le\log\log10<1<3.
\]
For the lower bound, \(h(q)^2\ge0\)
and we show \(\mathfrak b(q)<4\).
For \(L\le1\), \(\mathfrak b(q)=2L\le2\).
For \(1<L<\log10\), the function
\(2L-\log L\) is increasing, so its
maximum occurs at \(L=\log10\).
Now \(\log10<7/3\), since \(e>27/10\)
(which follows by summing the first
five terms of its power series) implies
\(e^7>(27/10)^7>10^3\).
Also \(\log10>2\), since \(e<3\),
and \(\log2>2/3\) by the positive
arctanh series. Consequently
\[
 2\log10-\log\log10
       <\frac{14}{3}-\frac23=4.
\]
This proves \(\mathfrak b(q)-4<h(q)^2\)
and completes the proof. \(\square\)

**Theorem 6 (unrestricted mass-entropy envelope).**
For every \(k\ge2\), positive probability vector
\(p\), and \(d\ge k-1\), put
\[
 B(p)=\sum_{i=1}^k p_i^2\mathfrak b(p_i).
\]
Then
\[
 \boxed{\displaystyle
 B(p)-6Q(p)\le\mathcal M_d(p)
                  \le B(p)+3Q(p).}                       \tag{22}
\]

*Proof.* Applying Lemma 5 to each mass gives
\(B(p)-4Q(p)\le U(p)\le B(p)+3Q(p)\).
Theorem 4 gives \(U(p)-2Q(p)
 \le\mathcal M_d(p)\le U(p)\).
Combining these inequalities proves (22).
\(\square\)

## 5. Consequences for all small masses

**Corollary 7 (two-term entropy expansion without
comparable-mass assumptions).**
Suppose \(d\ge k-1\) and
\(p_{\max}:=\max_i p_i\le e^{-1}\).
Then
\[
 \boxed{\displaystyle
 \mathcal M_d(p)=
 2\sum_i p_i^2\log\frac1{p_i}
 -\sum_i p_i^2\log\log\frac1{p_i}
 +E(p),\qquad |E(p)|\le6Q(p).}             \tag{23}
\]
For *any* family of probability vectors with
\(p_{\max}\to0\), regardless of the ratio
\(p_{\max}/p_{\min}\),
\[
 \boxed{\displaystyle
 \mathcal M_d(p)\sim
   2\sum_i p_i^2\log\frac1{p_i}.}           \tag{24}
\]
The logarithmic second term is meaningful:
its magnitude divided by \(Q(p)\) tends to infinity,
whereas the error in (23) is at most \(6Q(p)\).

*Proof.* If \(p_i\le e^{-1}\), then
\(L(p_i)\ge1\) and \(\log^+ L(p_i)=\log L(p_i)\),
so (23) is exactly Theorem 6.
Let \(L_*=\log(1/p_{\max})\to\infty\).
For all \(L\ge L_*\),
\(\log L/L\) tends uniformly to zero
(because it is decreasing for \(L>e\)).
Also
\(Q(p)/\sum_i p_i^2L(p_i)\le1/L_*\).
Dividing (23) by
\(2\sum_i p_i^2L(p_i)\) proves (24).
Finally
\(\sum_i p_i^2\log L(p_i)
 \ge(\log L_*)Q(p)\), proving the
assertion about the second term. \(\square\)

**Corollary 8 (near-uniform masses and the exact
log-log coefficient).**
Fix \(0<a\le1\le b<\infty\).
Uniformly for all \(k\to\infty\), vectors with
\(a/k\le p_i\le b/k\), and \(d\ge k-1\),
\[
 \boxed{\displaystyle
 \mathcal M_d(p)=
 \left(2\log k-\log\log k-\log(4\pi)\right)
 \sum_i p_i^2+O_{a,b}(1/k).}                \tag{25}
\]
No equality between the masses is assumed.

*Proof.* Write \(p_i=c_i/k\), where \(c_i\in[a,b]\).
Then \(L(p_i)=\log k-\log c_i\),
so uniformly in \(i\),
\[
 2L(p_i)-\log L(p_i)
       =2\log k-\log\log k+O_{a,b}(1).
\]
The constant term \(-\log(4\pi)\) is
**not identified** by the stated \(O_{a,b}(1/k)\)
precision; inserting it in (25) merely
aligns the expression with the normal quantile
convention. Only the coefficients of the
leading and log-log terms are determined here.
Moreover \(Q(p)\le b/k\), since
\(\sum_i p_i^2\le(\max_i p_i)\sum_i p_i\).
Now apply (23). \(\square\)

**Corollary 9 (constructive global relative saturation).**
If \(p_{\max}\le e^{-10}\), set
\(L_*=\log(1/p_{\max})\ge40\). Then
\[
 \boxed{\displaystyle
 \frac{\mathcal M_d(p)}{U(p)}
 \ge 1-\frac{2}{2L_*-\log L_*-4}
 \ge1-\frac2{L_*}\qquad(d\ge k-1).}         \tag{26}
\]
The *explicit staircase partition (5)* satisfies
the same ratio. In particular, as
\(p_{\max}\to0\), it is asymptotically
optimal for the full unconstrained
fixed-mass Gaussian partition problem,
even for arbitrarily heterogeneous masses.

*Proof.* By Lemma 5, for \(L_i=L(p_i)\ge L_*\),
\[
 h(p_i)^2\ge 2L_i-\log L_i-4
           \ge2L_*-\log L_*-4
           \ge L_*,
\]
because \(2L-\log L\) increases for \(L\ge10\)
and \(L-\log L-4>0\) there.
Therefore \(U(p)\ge
 (2L_*-\log L_*-4)Q(p)\ge L_*Q(p)\).
Divide Theorem 4 and its explicit staircase
version by \(U(p)\). \(\square\)

**Corollary 10 (quadratic-mass concentration of near-maximizers).**
Let \(p_{\max}\le e^{-10}\) and \(0<\eta<1\).
For any feasible Gaussian partition with
squared-centroid objective at least \(U(p)-2Q(p)\),
write \(b_i=\int_{A_i}x\,d\gamma_d(x)\).
Define the deficient indices
\[
 I_\eta=\left\{i:
   \|b_i\|^2\le(1-\eta)\varphi(t_{p_i})^2\right\}.
\]
Then
\[
 \boxed{\displaystyle
 \sum_{i\in I_\eta}p_i^2
       \le\frac{2}{\eta L_*}\sum_i p_i^2.}  \tag{27}
\]
This applies in particular to the explicit
staircase construction; it also applies
to any attaining global maximizer.

*Proof.* Every one-cell deficit
\(\delta_i=\varphi(t_{p_i})^2-\|b_i\|^2\)
is nonnegative by (14), and the total
\(\sum_i\delta_i\le2Q(p)\)
by hypothesis. For every \(i\in I_\eta\),
\[
 \delta_i\ge\eta\varphi(t_{p_i})^2
      =\eta p_i^2h(p_i)^2
      \ge\eta L_*p_i^2
\]
by Corollary 9's pointwise estimate.
Summation proves (27). \(\square\)

---



### Dimension requirement: a rigorous obstruction and a logarithmic-dimensional example

The dimensional hypothesis \(d\ge k-1\) in the
all-mass collision bound must not be silently discarded.
There is a general complementary estimate for **every**
ambient dimension \(d\ge1\):
\[
 \boxed{\displaystyle
 \mathcal M_d(p)\le d\,\max_i p_i.}           \tag{27a}
\]
Indeed, writing \(b_i=\int_{A_i}x\,d\gamma_d\),
vector-valued Cauchy--Schwarz gives
\[
 \|b_i\|^2\le p_i\int_{A_i}\|x\|^2\,d\gamma_d(x).
\]
Summation and \(\mathbb E\|G\|^2=d\) give (27a).

For equal masses \(p_i=1/k\), the ceiling is
\(\mathcal M_d(p)\le d/k\), whereas the
individual-cell halfspace envelope obeys
\(U(p)\sim(2\log k)/k\).
Consequently, if \(d=o(\log k)\),
\[
 \frac{\mathcal M_d(1/k,\dots,1/k)}{U(p)}
               \longrightarrow0.
\]
Thus no universal additive \(C\sum p_i^2=C/k\)
envelope of the type in Theorem 4 can hold in
dimensions \(d=o(\log k)\): its gap in
units of \(\sum p_i^2\) must diverge.

For comparison, when \(k=2^d\), partition
\(\mathbb R^d\) into its \(2^d\) orthants.
Each orthant has mass \(1/k\), and its Gaussian
first-moment coordinates equal
\(\pm\sqrt{2/\pi}/k\). Therefore
\[
 \boxed{\displaystyle
 \frac{2d}{\pi k}
 \le\mathcal M_d(1/k,\dots,1/k)
 \le\frac d k,\qquad k=2^d.}                \tag{27b}
\]
The lower bound is attained by the orthant construction;
no claim of optimality in fixed dimension is made.
This shows that logarithmic Gaussian dimension already
supports a constant fraction of the high-dimensional
optimal scale, even though a \(1-o(1)\) approximation
at the minimal dimension remains a separate problem.


## 6. Positive-correlation Gaussian noise-stability approximation

There is also a uniform consequence for the full
Gaussian noise-stability functional, not just its
first derivative at zero correlation.

Let \(G,G'\in\mathbb R^d\) be standard
Gaussians with
\(\operatorname{Cov}(G,G')=\rho I_d\),
where \(0\le\rho<1\).
For any partition \(\mathcal A=(A_i)\), set
\[
 \operatorname{Stab}_\rho(\mathcal A)
   =\sum_{i=1}^k
     \Pr\{G\in A_i,\ G'\in A_i\},\qquad
 \mathcal N_{d,\rho}(p)
   =\sup_{\gamma_d(A_i)=p_i}
                 \operatorname{Stab}_\rho(\mathcal A).
\]

**Theorem 11 (constructive noise-stability envelope).**
For \(d\ge k-1\), every positive probability vector
\(p\), and every \(0\le\rho<1\),
\[
 \boxed{\displaystyle
 Q(p)+\rho[U(p)-2Q(p)]
 \le \mathcal N_{d,\rho}(p)
 \le Q(p)+\rho U(p)+\rho^2[1-Q(p)] .}
 \tag{28}
\]
More strongly, if \(\mathcal A_{\rm stair}\)
is the explicit partition (5), then
\[
 \boxed{\displaystyle
 0\le \mathcal N_{d,\rho}(p)
    -\operatorname{Stab}_\rho(\mathcal A_{\rm stair})
 \le 2\rho Q(p)+\rho^2[1-Q(p)].}
 \tag{29}
\]
The estimate is global over all measurable
mass-constrained Gaussian partitions; it makes
no assertion that the staircase partition
is exactly optimal at any fixed \(\rho>0\).

*Proof.* Let \(H_\alpha\) be the orthonormal
multivariate Hermite polynomial basis of
\(L^2(\gamma_d)\). For the cell indicators
\(f_i=\mathbf1_{A_i}\), define
\[
 W_j(\mathcal A)
  =\sum_i\sum_{|\alpha|=j}
       |\langle f_i,H_\alpha\rangle|^2
          \ge0.
\]
Mehler's identity follows by comparing
coefficients in the Gaussian generating
function
\[
 \mathbb E\left[
 e^{\langle s,G\rangle-\|s\|^2/2}
 e^{\langle t,G'\rangle-\|t\|^2/2}
 \right]=e^{\rho\langle s,t\rangle}.
\]
Together with Parseval it yields, for
\(0\le\rho<1\),
\[
 \operatorname{Stab}_\rho(\mathcal A)
  =\sum_{j=0}^\infty \rho^j W_j(\mathcal A),
 \qquad\sum_{j=0}^\infty W_j(\mathcal A)=1.
\]
The constant and first-degree coefficients are
\[
 W_0=\sum_i p_i^2=Q(p),\qquad
 W_1=\sum_i
    \left\|\int_{A_i}x\,d\gamma_d(x)\right\|^2.
\]
Since all higher-degree coefficients are
nonnegative, and \(0\le\rho^j\le\rho^2\)
for \(j\ge2\),
\[
 Q+\rho W_1\le\operatorname{Stab}_\rho(\mathcal A)
 \le Q+\rho W_1+\rho^2(1-Q).
\]
Theorem 4 gives \(W_1\le U\) for every
partition and
\(W_1(\mathcal A_{\rm stair})\ge U-2Q\).
Combining these inequalities proves both
(28) and (29). \(\square\)

**Remark.** This theorem concerns
nonnegative noise correlation. For
\(\rho<0\), Hermite terms of odd order
alternate in sign, so the monotonic
remainder argument does not apply.

---

## 7. Scope, provenance, and what remains open

Theorem 4's additive constant **2 is a proved universal
constant**, not claimed sharp. The exact smallest possible
constant in a comparison of \(\mathcal M_d(p)\)
to \(U(p)\) is not determined here.

The proof does not establish which partitions optimize
\(\mathcal M_d(p)\) for any fixed \(k\ge4\);
in particular it does not settle the equal-mass
Standard Simplex problem. The dimension assumption
\(d\ge k-1\) is essential to the stated constructive
argument, although the upper bound holds for all \(d\).

The Gaussian halfspace rearrangement bound and the
normal Mills inequalities are classical. The connection
to OpenAI Mathematics result 096 and our prior
fixed-mass Gaussian research is recorded in README.md
and LITERATURE.md. We claim the explicitly proved
inequalities and construction, **not** worldwide
mathematical priority before comprehensive historical
search and independent peer review.

**Computer verification is supplementary.**
The mathematical proofs of Theorems 4 and 6 and their
corollaries use no solver and no numerical computation.
The companion exact checker certifies finite rational
mass identities and entropy inequalities for a battery
of highly nonuniform and boundary-sensitive examples;
it must not be mistaken for proof of the universal claims.
