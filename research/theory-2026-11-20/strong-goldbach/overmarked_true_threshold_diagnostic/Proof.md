# A dyadic obstruction to pricing the actual overmarked high ranks alone

This concerns the *prime* source in the
[overmarked low-rank reserve](https://github.com/mxym/math/commit/58c66ac9),
not the earlier high-rank bank with a product-of-five-primes source.
No fixed-target upper bound or sign is inferred from averaging.

Use exactly the reserve's notation, scale, central window and score:
\(N=2x\), \(J_N=xJ_0\) with \(J_0\subset[1,4/3]\) a fixed positive-length interval,
\(L=\log x\), \(W=x^{1/\log L}\), and \(P=N-y\).
Put \(T=\log y/L\), \(u_i=\log p_i/L\), \(u_A=\sum_{i\in A}u_i\), and
\[
 K(y)=L\biggl(\sum_{A}(-1)^{|A|}|u_A-T/2|
       +\sum_A(-1)^{|A|}g_\epsilon(u_A)\sum_{i\in A}
         2u_i\{w_\beta(u_i)+\kappa v(u_i)\}\chi_\delta(u_i)\biggr)
\]
on actual squarefree \(W\)-rough composites; elsewhere it is zero.
Here \(\rho=.2501\), \(v=1\) from \(.25008\), \(v=0\) through \(.25002\),
\(0<\kappa\le1\), and \(w_\beta,\chi_\delta,g_\epsilon\) are exactly the
old admissible smooth cutoffs with \(\epsilon<\delta/5\).
Write \(L_N,H_N\) for the respective \(\log P\)-weighted sums of \(K(y)\)
over actual \(P\) prime and \(y\in J_N\) of rank \(2\)–\(4\) and rank
\(\ge5\). Write \(G_N\) for the genuine weighted binary prime count on
that same window, \(M_N=|J_N|\mathfrak S(N)\), and
\[
 {\cal M}(X)=\sum_{X\le n\le 2X}M_{2n}.
\]

For each fixed \(\kappa\) and sufficiently small fixed cutoff choices,
\[
 \liminf_{X\to\infty}
       \frac{\sum_{X\le n\le2X}H_{2n}}{{\cal M}(X)}
 \ \ge\ 1+\frac{\pi^2}{6}+\kappa(B_2+B_3)-E(\beta,\delta,\epsilon),       \tag{1}
\]
where \(E\to0\) in the admissible cutoff limit and
\[
 B_2=2\log(2(1-\rho))>.810,\qquad
 B_3=2\int_0^{1-2\rho}\frac{-\log t}{1+t}\,dt>1.458.                  \tag{2}
\]
In particular, take the same cutoff choices as in the reserve proof,
tightened so \(E<.001\). For every sufficiently large dyad there
exists a true even target \(N\) therein with
\[
     H_N>(2.6439+2.268\kappa)M_N.
\]
The sufficient threshold from the .380 reserve, \(2+.380\kappa\), is
therefore **not an attainable uniform upper bound on the signed
high-rank term with this score**. This holds even if the proposed
upper discarded no negative high ranks. To make an unconditional
separate-budget strategy feasible in mean, a replaced uniform low
reserve \(L_N\le -C M_N+B G_N+o(M_N)\), with \(1+B>0\), would require
\(C\) at least \(.6439+2.268\kappa\) merely to avoid this obstruction.
The conclusion does not preclude a bound proven only under a verified
small-\(G_N\) hypothesis, nor a coupled same-target bound for \(H_N+L_N\).

## 1. True dyadic normalization

Put \(C_2=\prod_{p>2}(1-1/(p-1)^2)\).
For even \(N=2n\),
\[
 \mathfrak S(2n)=2C_2\sum_{d\mid n}g(d),\quad
 g(d)=\mu^2(d)1_{2\nmid d}\prod_{p\mid d}(p-2)^{-1},\qquad
 \sum_d g(d)/d=C_2^{-1}.
\]
The series converges absolutely by its positive Euler product;
\(1+1/(p(p-2))=(1-1/(p-1)^2)^{-1}\).
For any fixed continuous weight on \(n/X\in[1,2]\), average a
finite divisor sum first, then bound the tail in the unweighted
count by \(\sum_{D<d\le2X}g(d)\lfloor 2X/d\rfloor\). Thus the even-target
singular-series mean is \(2\), also with the weight \(n/X\).
Consequently \({\cal M}(X)\sim3|J_0|X^2\).

On the other hand, the sum of the actual \(G_N\) over \(N=2n\) in
this dyad is the true prime-pair mass over the ordinary two-dimensional
region
\[
 \{(s,t):\ s,t>0,\ 2\le s+t\le4,\
                   2t/(s+t)\in J_0\},\qquad (s,t)=(P/X,y/X).
\]
All prime pairs in this region are odd-odd for large \(X\), so no
additional factor \(1/2\) occurs. Its area is \(3|J_0|\), by
integrating the \(t\)-length \(|J_0|(s+t)/2\) for fixed \(s+t\).
The ordinary prime number theorem on rectangles and approximation of
this fixed piecewise-linear boundary give
\[
       \sum_{X\le n\le2X} G_{2n}={\cal M}(X)+o({\cal M}(X)).
                                                               \tag{3}
\]
This is not a pointwise binary Goldbach estimate.

The cited reserve's cusp and zero-marker calibration give, uniformly
in \(N\) at the fixed cutoff choices,
\[
       L_N+H_N=2M_N-G_N+o(M_N).                                  \tag{4}
\]
Average (4) using the actual denominator \({\cal M}(X)\) and (3).
The result is \(1+o(1)\) for the normalized total composite score.

## 2. Low-rank signed average, same ledger

Temporarily replace the common divisor cutoff by the exact own-half
cutoff and the amplitude by \(2u(1+\kappa v(u))\); call the score
\(K_*\). The **true reflected-prime** finite-rank wall estimates
in the [one-mark finite-rank follow-up](../marked_cusp_finite_rank/Proof.md)
and rank-four treatment in §3 of the cited low-rank reserve give
\[
 \sum_{\substack{y\in J_N,\ P=N-y\ {\rm prime}\\2\le\omega(y)\le4,\
                    y\ {\rm squarefree},\ P^-(y)>W}}
       \log P\, |K(y)-K_*(y)|\le (E_0+o(1))M_N .
\]
Here \(E_0\ll\sum_{t\in\{\beta,\delta,\epsilon\}}t(1+|\log t|)^2\)
with fixed-rank constants; using instead the sequential small-cutoff
limit of the reserve suffices. Indeed, the midrange \(v\) is unchanged,
is bounded, and only its \(g_\epsilon,\chi_\delta\) cutoffs incur the
same two near-half walls. This does not assert any uniformity in the
high ranks or exchange a moving rank with shrinking parameters.

The pointwise sharp low-rank profile is particularly simple.
Set \(t_i=u_i/T\) so \(\sum t_i=1\). For rank two with least label \(u\),
\(K_*/L=-2\kappa u v(u)\); for rank three with every \(t_i<1/2\),
\(K_*/L=-2T-2\kappa\sum_i u_iv(u_i)\); with a giant \(t_i>1/2\)
the rank-three score vanishes. These are literal sharp subset identities.
At rank four the base linear mark exactly cancels the even cusp, and
the extra sharp mark is nonnegative before subtraction: for the
short-pair star its signed amplitude is \(-2\phi_{\rm extra}(\min u_i)=0\);
for the triangle, at most one of the three lower labels is in its
positive support and its amplitude is at most that of the largest.
If a giant exists all cofactor allocations cancel. Thus all
three sharp low ranks have nonpositive scores. There are no own-half
ties for a squarefree composite.

We need only the lower favorable magnitudes on ordinary *compact*
profiles: the rank-two part \(t_{\min}\ge\rho\) and the rank-three
nongiant region, keeping a small fixed distance from their boundaries
first. The latter can be charged an extra term \(2\kappa t_i\) for
each \(t_i\ge\rho\). On each such profile every actual factor is
polynomially long, hence bigger than \(W\) eventually. Since \(T=1+O(1/L)\)
and all thresholds are reached with a fixed margin on a compact
profile, the change from \(u_i\) to \(t_i\) costs \(o(1)\) on the
score weight. No nonsquarefree factor is inserted.

For clarity, the true averaging of a compact rank-\(k\) profile
weight \(b(t_1,\ldots,t_k)\), for \(k=2,3\), uses only the ordinary PNT.
The fixed-scale angular measure, in the unordered convention, is
\[
 I_k(b)=\frac1{k!}\int_{\substack{t_i>0\\\sum_i t_i=1}}
          b(\mathbf t)\frac{dt_1\cdots dt_{k-1}}{t_1\cdots t_k}.
\]
Indeed, fix \(k-1\) genuine distinct prime labels and their product
\(D\). For a fixed compact spatial interval \(aX\le y\le bX\),
the last prime is in \([aX/D,bX/D]\); all factors are bounded away
from exponent zero, so dyadic PNT gives an error \(o(X/(D\log X))\)
uniformly in the first \(k-1\) labels. A continuous angular test can
first be frozen on sufficiently fine exponent boxes because
\(t_k=1-\sum_{i<k}(\log p_i/\log X)+O(1/\log X)\).
The harmonic PNT on the fixed exponents of the other labels gives
the remaining \(\prod dt_i/t_i\). Removing repetitions changes the
count by \(o(X/\log X)\), either by the square-multiple bound or
the reciprocal square harmonic in the fixed exponent intervals.
Thus \(\log X\) times this rank-\(k\) counting measure tends to
\(I_k(b)\) times Lebesgue measure at scale \(X\). Combine with the
independent \(\log P\) prime PNT in the same \((s,t)\)-region from §1;
this is permitted **only after summing targets**. Both numbers are odd;
all composite factors here grow, so the parity convention is again
already paid in §1. First take compact supports, then exhaust the
indicated nonnegative angular integrands. No large-rank limit is used.

In rank two, sorting its smaller label gives
\[
 I_2(2t_{\min}1_{t_{\min}\ge\rho})
      =2\int_\rho^{1/2}\frac{du}{1-u}=B_2 .
\]
In rank three, \(1/(abc)=1/(ab)+1/(ac)+1/(bc)\) at \(a+b+c=1\)
and symmetry give
\[
 I_3(1_{\max t_i<1/2})
 =\frac12\int_0^{1/2}\int_{1/2-a}^{1/2}\frac{db\,da}{ab}
 =\frac12\sum_{j\ge1}\frac1{j^2}=\frac{\pi^2}{12}.
\]
For the extra rank-three contribution, \(3\cdot2/3!=1\);
pinning one label \(a\ge\rho\) gives
\[
 I_3\!\left(2\,1_{\max t_i<1/2}\sum_i t_i1_{t_i\ge\rho}\right)
 =\int_\rho^{1/2}\int_{1/2-a}^{1/2}\frac{db\,da}{b(1-a-b)}
 =2\int_0^{1-2\rho}\frac{-\log t}{1+t}\,dt=B_3 .
\]
All remaining sharp low-rank pieces have nonpositive sign, so
\[
 \limsup_{X\to\infty}
       \frac{\sum_{X\le n\le 2X}L_{2n}}{{\cal M}(X)}
 \le -\pi^2/6-\kappa(B_2+B_3)+E_0 .
\]
Together with §1 this proves (1). The finite numerical bounds
follow from the positive series for \(\log z\) in \((z-1)/(z+1)\)
and the lower polynomial \(1-t+\cdots-t^7\le(1+t)^{-1}\).
See the exact rational checker.

This is a feasibility limitation for a uniform *separate*
high-rank estimate with the old low reserve. It neither prescribes
the high-rank sign at a fixed target nor rules out the paired signed
estimate needed for a proof of Goldbach.
