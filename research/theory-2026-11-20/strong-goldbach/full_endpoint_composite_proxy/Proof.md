# A full endpoint lift yields a composite proxy for the true tagged prime columns

This note evaluates the endpoint left out of the
[near-half cutoff lift](../rank_four_near_half/Proof.md). Its mean does
not vanish. It is exactly the reduced prime-density reference on the
usual logarithmic prime scale. Subtracting this known reference
gives the correct centered covariance. No claim is made about the
sign of its remaining fluctuations or about binary Goldbach.

Let \(N=2x\) be an even target, \(Y=\sqrt{x}\), \(L=\log x\),
\(\ell=\log L\), \(z=\exp(L/\ell^2)\), and
\(R_z(y)=1_{\{P^-(y)>z\}}\).
The physical box is
\[
 d,e\in E=[.65Y,.8Y],\qquad k\in I=[Y,1.1Y],\qquad(dek,N)=1.
\]
For a slope \(e\), \(\beta(e)\) counts its actual pairs \(p_2p_3\mid e\)
with \(p_2\in[x^{.029},x^{.031}]\), \(p_3\in[x^{.075},x^{.078}]\),
both genuine primes. Write \(H_E=.15Y\) for the length of \(E\).
A kernel \(f\) has tagged column
\[
 \Gamma_f(k)=\sum_{\substack{e\in E\\(e,N)=1}}\beta(e)f(N-ek).
\]
Use \(a(y)=\log y\,1_{\{y\ {\rm prime}\}}\) and \(b_z(y)=R_z(y)/V_z\),
where \(V_z=\prod_{p\le z}(1-1/p)\). These are distinct functions:
the first is the true prime weight, the second a rough comparison.

As in [the full free-branch proof](../full_free_hb_splice/Proof.md), put
\[
 K(y)=R_z(y)\sum_{\substack{sr=y\\r>x^{.505}}}\mu(r)\log s,\qquad
 F_U(y)=-R_z(y)\sum_{\substack{sca=y\\ca>x^{.505}\\a>U(s)}}
                     \mu_2(c)\log s,\quad \mu_2=\mu*\mu ,
\]
and use the wider old cutoff
\[
 T(s)=
 \begin{cases}
 x^{.674}s^{-1/4}&x^{.13}\le s\le x^{.32},\\
 \min(x^{.766}s^{-1/2},x^{.918}/s)&\text{otherwise}.
 \end{cases}
\]
Set
\[
 T^\sharp(s)=\max\{T(s),x^{.505}\},\qquad
 D(y)=F_T(y)-F_{T^\sharp}(y),\qquad
 R^\sharp(y)=K(y)-F_{T^\sharp}(y)=(K(y)-F_T(y))+D(y).                \tag{1}
\]
In particular the new residual **adds** \(D\); the sign is essential.

**Endpoint and prime-column transfer.**
* For each fixed \(\delta>0,A>0\), every modulus
\(2\le Q\le x^{.612-\delta}\), every reduced class \(j\bmod Q\),
and interval \(J\subseteq[x,3x/2]\), the actual composite-only
signed statistic \(D\) satisfies
\[
 \sum_{\substack{y\in J\\ y\equiv j\bmod Q}}D(y)
       =\frac{|J|}{\varphi(Q)}
                   +O_{\delta,A}((x/Q)L^{-A}).                      \tag{2}
\]
No distribution theorem for actual primes at this level is asserted.
* In the physical box, with
\[
 M(k)=H_E k
       \sum_{\substack{p_2,p_3\ {\rm in\ their\ bands}\\(p_2p_3,N)=1}}
                   \frac1{\varphi(kp_2p_3)},                        \tag{3}
\]
one has \(\Gamma_D(k)=M(k)+O_A(YL^{-A})\) and
\(\Gamma_{b_z}(k)=M(k)+O_A(YL^{-A})\) for each actual unit \(k\).
The **prime-free** score \(R^\sharp\) matches the true prime columns
in aggregate:
\[
 \sum_{k\in I,\,(k,N)=1}
        |\Gamma_{R^\sharp}(k)-\Gamma_a(k)|\ll_A xL^{-A}.              \tag{4}
\]
The difference may also be paired with arbitrary actual opposite
weights in the original fixed divisor envelope, as specified below.
* \(R^\sharp\) vanishes on all primes and all squarefree semiprimes;
it is nonnegative on all squarefree triprimes and all squarefree
rank-four \(y\) with \(P^+(y)\le x^{.505}\). This last sign statement is
about this large-free ledger, not a separate medium-slot subtraction.

## 1. Exact fixed-modulus two-free count

The lift can only modify \(s>x^{.413}\), where the old threshold is
\(x^{.918}/s\). Indeed all first-cut and annular pieces are above
\(x^{.505}\), and \(x^{.918}/s<x^{.505}\) precisely for
\(s>x^{.413}\). Thus
\[
 D(y)=-R_z(y)
   \sum_{\substack{sca=y,\ s>x^{.413},\ ca>x^{.505}\\
                       x^{.918}/s<a\le x^{.505}}}\mu_2(c)\log s .    \tag{5}
\]
On this literal domain
\[
 c<y/x^{.918}\le1.5x^{.082},\qquad
 x^{.413}<s<1.5x^{.495},\qquad a\gg x^{.423}.
\]
The strict upper \(s<y/x^{.505}\) is part of (5) and is not shortened.

Fix \(c\), leave \(R_z(c)\mu_2(c)\) unchanged, and work in reduced
class \(j\bmod Q\). The variables \(s,a,c\) are required to be units
of \(Q\). For a free variable \(n\) expand \(R_z(n)\) by the
Bonferroni polynomial \(P(n)\) through \(\lceil C\ell\rceil\)
prime factors. Write \(E(n)\) for the next positive factorial
polynomial, so \(|R_z(n)-P(n)|\le E(n)\) and
\(|P(n)|\le1+E(n)\). On any rectangular box the product error
is dominated pointwise by
\[
             E(a)+E(s)+E(a)E(s).
\]
Thus it is enough to use the same positive rectangle count
on these next-degree products; no average over moduli or
over targets is used to pay this sieve error. Every opened
divisor \(m\) is \(x^{o(1)}\), and those sharing primes with \(Q\)
give zero in the true reduced progression.
After opening \(a=m_a u,\ s=m_s v\), the two free integers
satisfy \(uv\equiv j\overline{c m_a m_s}\bmod Q\).
The uniform composite-modulus rectangle estimate from
[the full free-branch proof, §2](../full_free_hb_splice/Proof.md)
is
\[
 \#\{u\in J_1,\ v\in J_2:\ uv\equiv b_0\bmod Q\}
 =\frac{\varphi(Q)}{Q^2}|J_1||J_2|
 +O_\varepsilon\!\left(Q^{1/2+\varepsilon}
       +( |J_1|+|J_2|)Q^{-1+\varepsilon}\right)
\]
for any unit \(b_0\). It retains the exact factor \(\varphi(Q)/Q^2\).
In particular a modulus need not be squarefree.

To handle the exact windows, for each \(c\) the \(y\)-interval is
\(J\cap(c x^{.918},\infty)\), the independent \(a\)-range is
\(x^{.505}/c<a\le x^{.505}\), and \(s>x^{.413}\).
Use log-fine relative rectangles in the two free variables,
after dyadic subdivision, with width \(L^{-B}\) at their scales.
On the start, end, or boundary rectangles the same positive
estimate is used. For each fixed \(s,c\), the unresolved
product or \(a\)-boundary strips have total free \(a\)-length
\(O(L^{-B}W)\) on a scale \(a\asymp W\), and an \(s\)-boundary
strip is handled by symmetry. Thus their total principal
volume is \(O(L^{-B}x/c)\) per dyadic box; the divisor
weights and \(\log s\) cost fixed log powers.
The next-degree factorial contributions to the zero term are
arbitrary-log by \((\sum_{p\le z}1/p)^J/J!\) for sufficiently
large fixed \(C\), also when both factors are opened.
The finitely many box cuts and their smooth log weights can
be applied by partial summation or by the same mesh.

For clarity the complete bound is uniform **per modulus**.
The sum of \(Q^{1/2+\varepsilon}\) errors over all
\(c\le1.5x^{.082}\), both subpower divisor lists, box labels
and pointwise divisor weights, is at most
\(x^{.082+o(1)}Q^{1/2+\varepsilon}\).
Relative to \(x/Q\), this saves a power throughout
\(Q\le x^{.612-\delta}\) because
\(.082+3(.612)/2=1\).
For a common dyadic \(c\sim C_1,\ s\asymp S,\ a\asymp W\)
one has \(C_1SW\asymp x\) on any retained box.
The summed second error is therefore at most
\((x/S+x/W)Q^{-1+\varepsilon}x^{o(1)}\), also a fixed
power saving relative to \(x/Q\).
The argument applies to both signs of (5) via the
nonnegative rectangle error bounds and all physical
upper and lower cutoff endpoints. Thus any target-unit
filter apart from \((y,Q)=1\) was not needed for (2).

The exact mean after completing the rough factors has local
constant
\[
 \frac{\varphi(Q)}{Q^2}W_z(Q)^2,\qquad
 W_z(Q)=\prod_{\substack{p\le z\\p\nmid Q}}(1-1/p).
\]
The remaining coefficient \(c\) is rough and coprime to \(Q\).
Changing \(a\) to \(y/(cs)\), the mean of (5) becomes
\[
 -\frac{\varphi(Q)W_z(Q)^2}{Q^2}
  \int_J\int_{x^{.413}<s<y/x^{.505}}\frac{\log s}{s}
   \sum_{\substack{y/(s x^{.505})\le c<y/x^{.918}\\(c,Q)=1}}
                    \frac{\mu_2(c)R_z(c)}c\,ds\,dy .                \tag{6}
\]
The accumulated error is \(O_{\delta,A}((x/Q)L^{-A})\).
In particular the lower \(c\)-endpoint in (6) can be \(1\);
it must not be discarded by a polynomial-range cancellation estimate.

## 2. The exact nonzero endpoint term

At fixed \(y\) write
\[
 A_y=\log(y/x^{.505}),\quad Z_y=\log(y/x^{.918}),\quad
 u=\log(y/(s x^{.505})).
\]
The two exact \(s\)-endpoints become \(0<u<Z_y\), with
\(\log s=A_y-u\). Interchanging the finite \(c\)-sum and
this integral produces
\[
 \sum_{\substack{c<e^{Z_y}\\(c,Q)=1}}
     \frac{\mu_2(c)R_z(c)}c
       \left(A_y\log c-\tfrac12(\log c)^2\right).                   \tag{7}
\]
The \(c=1\) term in (7) has zero weight, but the endpoint
has already determined both logarithmic factors.

For
\[
 B_Q(w)=\prod_{\substack{p\le z\ {\rm or}\ p\mid Q}}
                      (1-p^{-1-w})^{-1}
\]
the harmonic Dirichlet series of the coefficient in (7) is
\(\zeta(1+w)^{-2}B_Q(w)^2\). Its zero at \(w=0\) is of
order two with leading coefficient \(B_Q(0)^2\). Uniformly
for \(e^{Z_y}\asymp x^{.082}\), the partial first logarithmic
moment is \(O_A(L^{-A})\), and the second is
\[
       2B_Q(0)^2+O_A(L^{-A}).
\]
For example, use the rough Perron shift
\(\Re w=-c_0/\log z\) as in the factored band
and differentiate once and twice in a small parameter
\(|v|\le c_0/(4\log z)\) multiplying a coefficient by \(c^{-v}\).
Cauchy's derivative bound costs at most a fixed log power.
The shifted vertical line gives a saving
\(\exp(-c_1\ell^2)\), uniformly in \(Q\); the finite Euler
products are polylogarithmically bounded and the usual
sharp Perron endpoint error is covered by
\(|\mu_2(c)|\le\tau(c)\) and the short-interval divisor bound.
There are no poles from the finite factors in this strip.
One may equivalently shift with the directly differentiated
Dirichlet series. The zero and the second derivative are
evaluated in the same normalization.

Hence (7) is \(-B_Q(0)^2+O_A(L^{-A})\).
The minus sign outside (6) makes the result positive.
The local factor simplifies **exactly**:
\[
    W_z(Q)B_Q(0)=\prod_{p\mid Q}(1-1/p)^{-1}=\frac{Q}{\varphi(Q)},
    \qquad
    \frac{\varphi(Q)W_z(Q)^2 B_Q(0)^2}{Q^2}
                       =\frac1{\varphi(Q)}.
\]
This proves (2). It is a nonzero cutoff-boundary term,
not the cancellation of two polynomial lower endpoints.

## 3. Actual tagged columns and the corrected covariance

For each actual tuple \(k,p_2,p_3\) the literal modulus is
\(Q=kp_2p_3\), the actual reduced residue \(N\bmod Q\),
and \(J_k=[N-.8Yk,N-.65Yk]\) has length \(H_E k\).
The unit slope condition corresponds to \((y,N)=1\).
It can be restored in (2) at arbitrary-log cost uniformly
per \(Q\): on the original rough support any violating \(y\)
has a prime \(p>z\) dividing \(N\). In the reduced
modulus-\(Q\) class there are at most
\(O(xL/(Qz)+L)\) such integers. Cauchy with Shiu's fixed
divisor-moment bound in this actual progression, and
\(|D(y)|\ll L\tau_4(y)\), makes their total
\(O_A((x/Q)L^{-A})\). Here \(x/Q\) is polynomial
and each \(p\mid N\) is coprime to \(Q\).
The same restoration is available for \(b_z\).

Thus (2) gives the first pointwise column assertion at (3).
For \(b_z\), the independent CRT count of rough integers
in a reduced class gives the literal mean
\[
        \frac{|J_k|}{Q}\frac{W_z(Q)}{V_z}
        =\frac{|J_k|}{\varphi(Q)}(1+O(L/z)).
\]
The approximation concerns only prime divisors of \(Q\)
above \(z\); all smaller factors are retained exactly.
Bonferroni's factorial tail, and the subpower number of
floor errors, give \(O_A((x/Q)L^{-A})\) uniformly for
all these \(Q\). This proves the second pointwise column
assertion. Summing the normalized errors over the actual
tag primes uses \(\sum_{p_2,p_3}1/(p_2p_3)=O(1)\).

The shared label case in (3) presents no hidden factor:
\[
 \frac1{\varphi(kp_2p_3)}
   =\frac1{\varphi(k)\varphi(p_2)\varphi(p_3)}
     \prod_{\substack{i\in\{2,3\}\\p_i\mid k}}(1-1/p_i).
\]
Therefore with the exact harmonic tag constant
\[
 C_{\beta,N}=\sum_{\substack{p_2,p_3\ {\rm actual}\\(p_2p_3,N)=1}}
                      \frac1{\varphi(p_2)\varphi(p_3)}\asymp1
\]
one has \(M(k)=H_E C_{\beta,N}(k/\varphi(k))(1+O(x^{-.029}))\)
uniformly, whether or not a tag divides \(k\).
In particular \(\sum_{k\ {\rm unit}}M(k)^2
\asymp x^{3/2}\varphi(N)/N\) by the ordinary positive
divisor expansion of \((k/\varphi(k))^2\) on unit \(k\)'s.

For the true prime transfer, the
[above-root calculation](../overroot_shared_k/Proof.md)
gives an arbitrary-log signed transfer of the short
Möbius convolution at cutoff \(x^{.505}\) to \(b_z\)
against any opposite true divisor-weight row.
Its complement is \(K\), by the exact identity
\(\sum_{r\mid y}\mu(r)\log(y/r)=\Lambda(y)\).
Proper prime powers are negligible by their ordinary
count and the divisor multiplicity of \(N-y\).
Choose the opposite test to be the sign of the full
column error independently of the opposite slope \(d\).
Dividing the signed bound by the number
\(\asymp Y\varphi(N)/N\) of unit slopes proves the
\(O_A(xL^{-A})\) absolute sum over \(k\), after raising
the input log accuracy. In the same way the full
free-branch bound gives
\(\sum_k|\Gamma_{F_T}(k)|\ll_A xL^{-A}\).
Together with the exact (1) and the two pointwise
column estimates above, this proves (4).

More explicitly, for any fixed \(B\) and actual weights
\[
 |u_{d,k}|\le L^B\tau(d)^B\tau(k)^B\tau(N-dk)^B
\]
on the original unit box,
\[
 \sum_d\left|\sum_k u_{d,k}
          [\Gamma_{R^\sharp}(k)-\Gamma_a(k)]\right|
                      \ll_{A,B} x^{3/2}L^{-A}.                     \tag{8}
\]
Indeed the absolute opposite row is \(O(YL^{C_B}\tau(k)^B)\)
by Cauchy and Shiu. Clip the last divisor weight above a
large log power and use its higher moments and the uniform
\(O(YL^C)\) envelope of the actual column difference.
This is not an estimate for an extra arbitrary joint mask
on the inner \(e\)-sum.

Let \(\mathcal V=\sum_k(\Gamma_a(k)-\Gamma_{b_z}(k))^2\)
be the original tagged centered covariance on this box.
The corrected identity is
\[
 \mathcal V
 =\sum_k(\Gamma_{R^\sharp}(k)-M(k))^2
      +O_A(x^{3/2}L^{-A})
 =\sum_k\Gamma_{R^\sharp}(k)^2-\sum_k M(k)^2
      +O_A(x^{3/2}L^{-A}).                                        \tag{9}
\]
The first equality follows from (4) and the uniform
divisor-moment envelopes. For the second, the cross mean
\(\sum_k M(k)(\Gamma_a(k)-\Gamma_{b_z}(k))\) is
arbitrary-log small on the \(x^{3/2}\) scale.
One can use the earlier weighted mean with \(k/\varphi(k)\);
alternatively expand
\(k/\varphi(k)=\sum_{j\mid k}\mu^2(j)/\varphi(j)\).
The log-large \(j\) tail uses its reciprocal divisor
moment and uniform prime/rough row envelopes.
For the retained \(j\), open the literal slope modulus
\(ej\), in the [proved Maynard wedge transfer](https://github.com/mxym/math/commit/bafa9b8f).
Both the true log-prime and the true rough comparison
have the same main in the actual class \(N\bmod ej\).
The common \(k\)-interval becomes a fixed macroscopic
prime prefix difference for each \(e\); all added \(j\)'s
are fixed log powers and the slope labels are unchanged.
The power-small correction from shared tag divisors in
(3) and all log errors are harmless in this comparison.
Expanding the square and applying (4) now gives the
second equality. Coincident slopes in the original
quadratic expression may be dropped separately
at \(O(x^{1+o(1)})\); no diagonal is declared zero.

## 4. Physical signs and remaining analytic input

For a nonzero original \(s\)-label, \(a=r,\ c=1\) always
passes the lifted cutoff: it passed the old one,
and the original strict \(r>x^{.505}\) passes the new floor.
The cutoff is still \(>\sqrt{r}\). For squarefree \(r\)
of rank one the residual label is zero; for rank two it
is either \(2\log s\) or zero, since at most one proper
nontrivial \(c\) can be admitted. These statements give
the prime, semiprime and triprime claims. For rank four
with every prime factor \(\le x^{.505}\), no original
\(r\) of rank one is admitted. A negative term at a
singleton outer divisor \(s=p_i\) can only come from
one of its \(c=p_j\) choices, of weight \(-2\log p_i\).
A two-prime \(c\) is positive and may be omitted for
a lower bound. That single-prime choice implies
\(y/(p_i p_j)>T^\sharp(p_i)\ge x^{.505}\), so the
complementary outer **pair** \(s=p_i p_j\) is admitted.
Its two remaining prime factors are each at most its
floor \(x^{.505}\); the only qualifying free factor is
the full complementary product. The pair score is
thus \(2\log(p_i p_j)\), paying both possible singleton
charges between \(i,j\). Other pair scores are
nonnegative. This proves the claimed exact rank-four
sign, including equality at the prime cutoff.

The new evaluated endpoint and composite proxy do not
force the centered variance to be small. An independent
estimate of the form
\[
   \sum_k\Gamma_{R^\sharp}(k)^2
       \le \sum_k M(k)^2+O_A(x^{3/2}L^{-A})
\]
would close this marked column-variance block by (9).
At the natural scale even a little-\(o\) version
gives natural-scale mean-square control of the true tagged
columns; it must bound actual signed rank-four giant and
higher-rank terms, not merely replicate their first moments.
Only the specified two-tag family and these reflected
prime **columns** are transferred here.
Neither this variance estimate nor the full unmarked
off-diagonal input of Pham's criterion is obtained.

