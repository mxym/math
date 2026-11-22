# Finite angular rank for the entire sharp near-full quotient range

Keep exactly the original two-prime sharp score, the central interval
\(J\), and the parameters \(L,\ell,S,B,T_y,C_0,B_0\) of
[SharpTinyFactorDeletion.md](SharpTinyFactorDeletion.md). In particular
these are true primes \(x,r\), with \(x+mr=N\), \(x\in NJ\),
\(N/S^{C_0}\le r\le B=N/S\), and
\[
                       Q_y(m)=\sum_{\substack{d\mid m\\d<T_y}}\mu(d).
\]
As before \(N\) is an individual even target with
\(\operatorname{rad}(N)\le L^{B_0}\). Extra restrictions to a real
interval of \(r\) and a real interval of \(m\) may be imposed
throughout; at fixed \(y\) these simply intersect its real \(m\)
interval. All estimates below are uniform over these intervals
in the original near-full range.

**Theorem.** There are fixed \(A>0\), \(\xi_0>0\) such that, for each
fixed \(0<\xi\le\xi_0\), the entire true subsum on the mask
\(P^-(m)\le S^\xi\) is
\[
 \sum_{\substack{x+mr=N,\ x,r\ {\rm prime}\\
            x\in NJ,\ N/S^{C_0}\le r\le B\\P^-(m)\le S^\xi}}
       (\log x)(\log r)Q_y(m)
   =O\!\left(N\mathfrak S(N)\,
                 \xi(1+\log(1/\xi))^{A}\right)
                     +o_\xi(N\mathfrak S(N)).                     \tag{1}
\]
The displayed \(O\)-constant is independent of sufficiently
small fixed \(\xi\). The \(N\) limit is taken after fixing
\(\xi\). Thus at any prescribed fixed relative tolerance the
original sharp score on the entire assigned near-full \(r\)
interval can be replaced by its genuine squarefree quotients
with all prime factors \(>S^\xi\) and at most
\(\lfloor C_0/\xi\rfloor\) factors. The prime labels remain
physical and neither the upper prime mark nor the sharp divisor
threshold changes. The signed finite-rank remainder is not
estimated in (1).

The genuine terminal-collar estimate of the cited note and (1)
may be applied on disjoint \(r\)-intervals with this **same**
cutoff. The averaged-cutoff theorem of
[SmoothedTerminalQuotients.md](SmoothedTerminalQuotients.md)
concerns a different score. In particular it is not counted as
an additional credit here.

## 1. The real low-minimum mask in the comparison

Use the same \(Z_0=\exp(\ell^\theta)\), \(1<\theta<4/3\), and
full geometric palette of SharpTinyFactorDeletion. Fix its
comparison precision and \(K\) before \(\xi\). The covered
condition is at least \(2K\) occupied cells, and the chosen
\(K\)-tuple is the first sufficiently separated tuple of
occupied cells. All the reciprocal hit weights and known cell
flags are exactly as in that proof. Suppress \((xrm,N)>1\)
by the same power-small exception estimate.

To insert the exact \(P^-(m)\le S^\xi\) mask in the true
covered comparison, all fully-below and fully-above chosen
cells have a known contribution to the mask from their
extracted prime. At most one chosen cell straddles \(S^\xi\).
In that cell use the two independent bounded tag multipliers
\(1_{p\le S^\xi}\) and \(1_{p>S^\xi}\), **with the original
full-color reciprocal normalizer unchanged**. If the selected
primes already hit the low-minimum region the mask is
automatic; otherwise test \(P^-(m')\le S^\xi\) on the literal
residual \(m'\). This does not use reduced reciprocal masses
or asymptotics for the truncated color, and handles an equality
at the cutoff exactly. The occupied cell support of \(m\) is
still the support of \(m'\) united with the known selected
cells. Square restoration and all moving sharp-boundary
estimates are unchanged. For an extra real \(r\)-interval,
its endpoints are exactly the same type of genuine boundary
\(y=m r_0\) handled there.

The genuine Type I main applies to this exact predicate at
each fixed \(m\); the Type II shift has only the permitted
bounded tag multipliers and the same long-character major.
Thus the true covered low-minimum score equals
\[
 \mathfrak S(N)\int_{NJ}
   \sum_{\substack{m\in I_y,\ (m,N)=1\\
           P^-(m)\le S^\xi,\ m\ {\rm covered}}}
        \frac{c(m)Q_y(m)}m\,dx+O_D(NL^{-D}),                      \tag{2}
\]
where \(I_y\subseteq[T_y,yS^{C_0}/N]\) is the literal real
\(m\)-interval at \(y=N-x\), with any extra interval cuts.
The prime-product local factor \(c(m)\) is the same as in
SharpTinyFactorDeletion.

## 2. Missed genuine low-minimum quotients

Work on the missed support, with fewer than \(2K\) occupied
cells. Put \(m=v n\) with all prime powers at primes
\(\le Z_0\) assigned to \(v\). The entire missed part with
\(v>1\) in (2) and in the true score is already absolutely
\(o(N\mathfrak S(N))\) by §2 of the sharp tiny proof, regardless
of the extra masks. Take \(v=1\); repeated primes are negligible
in the true and modeled scores by the same actual-square
bound, and \(c(m)=1+o(1)\) uniformly on this remaining support.

Every remaining marked least prime \(p\le S^\xi\) belongs to
a cell \(j\) whose upper exponent satisfies
\(a_j=Ru_j/\log S\le R\xi\). Squarefreeness gives the strictly
correct identity
\[
              Q_y(p n)=
                    \sum_{\substack{d\mid n\\T_y/p\le d<T_y}}\mu(d).
\]
Each witness \(d\), since \(d\ge c_J S/p\), has a largest prime
\(q\) with \(\log q\gg\log S/(\omega(n_0)+1)\), where
\(n=q n_0,\ d=q d_0,\ d_0\mid n_0\). This holds with an absolute
positive constant in the exponent for \(\xi\le\xi_0<1/10\).
Fix \(p,n_0,d_0\). The allowed interval for \(q\) from the
witness has logarithmic length \(O_J(1+\log p)\); including all
\(y\) in the central support merely enlarges its endpoints
to \(c_JS/(p d_0),C_JS/d_0\). By the fixed-ratio Chebyshev
upper, the corresponding reciprocal mass is
\[
                O_J\!\left(
                       (\omega(n_0)+1)\frac{1+\log p}{\log S}
                       \right).
\]
For each set of fewer than \(2K\) occupied cells above or at
\(j\), the remaining
\(\tau(n_0)(\omega(n_0)+1)/n_0\)-harmonic is bounded by a
fixed Euler product and derivative; the reciprocal \(p\)-mass
in cell \(j\) is also bounded. Thus each set costs \(O(a_j)\).
There are at most
\(O((1+\log^+(1/a_j))^{2K})\) candidate sets because all its
indices are \(\ge j\). The downward geometric sum is
\[
       \sum_{a_j\le R\xi} a_j(1+\log^+(1/a_j))^{2K}
                 \ll \xi(1+\log(1/\xi))^{2K}.                   \tag{3}
\]
No bound on \(\omega(n_0)\) is assumed prior to this Euler
estimate. All the \(Q_y\) weights here were dominated
absolutely; a witness may be counted more than once.
As in the sharp proof, at each true fixed \(m\) the two-prime
positive sieve gives \(O_J(N\mathfrak S(N)c(m)/m)\). Consequently
(3) is valid also for the entire actual missed score, in units
of \(N\mathfrak S(N)\), and for the missed principal in (2).
The proof of this estimate did not assume that \(m\) is in
the terminal collar.

## 3. Uniform evaluation of the full integer model

By §3 of the sharp tiny proof, the full integer signed model
on \(I_y\), with its exact \(c(m)\) and target units and
without a minimum constraint, is \(O_D(L^{-D})\) uniformly
in real \(y\): simply take the unrestricted version of its
argument. It remains to subtract the full model on the
complementary \(P^-(m)>S^\xi\). We verify its exact limiting
measure and a bound uniformly in \(I_y\).

On this complementary support all primes of \(m\) are
eventually target units and \(c(m)=1+o_\xi(1)\) uniformly.
Also
\(\sum_{m\le S^{C_0},\ P^-(m)>S^\xi}\tau(m)/m=O_{C_0,\xi}(1)\),
by the elementary Euler product with
\(\sum_{S^\xi<p\le S^{C_0}}1/p=O_{C_0,\xi}(1)\).
Thus dropping \(c(m)-1\) incurs \(o_\xi(1)\) even absolutely.
Open \(m=d n\). Both factors are \(S^\xi\)-rough, with the
convention that \(1\) is rough. In \(u=\log_S d,\ v=\log_S n\),
their reciprocal counting measures, with coefficients
\(\mu(d)\) and \(1\) respectively, converge on each fixed
compact interval to
\[
        A_\xi=\exp_*(-\nu_\xi),\qquad
        B_\xi=\exp_*(\nu_\xi),\qquad
        \nu_\xi(dt)=1_{t>\xi}\frac{dt}{t}.                       \tag{4}
\]
Indeed every rank in a compact log interval is bounded at
fixed \(\xi\). Open the distinct primes with its exact \(k!\)
division; repeated factors contribute \(o_\xi(1)\) from
\(\sum_{p>S^\xi}p^{-2}\) and the bounded finite-rank
reciprocal sums. Reciprocal PNT then gives (4). The positive
measure \(B_\xi\) also dominates the limits of the unsigned
coefficients on both sides; at finite \(N\) the actual
unsigned \(d\)-measure is termwise dominated by the true
positive \(n\)-measure.

We need the uniformity for arbitrary real cutoffs, not only
weak convergence of an untruncated harmonic. Away from the
atom at zero, the two limiting measures in (4) are absolutely
continuous on every compact real interval. The same is true
of the full positive convolution \(B_\xi*B_\xi\).
Consequently the normalized actual unsigned mass near
\(u=1\), or near any \(u+v=t\ge1/2\), in a band of width
tending to zero tends to zero, uniformly in \(t\) on compact
sets. For example, if such intervals carried a positive
limsup, choose a convergent subsequence of their centers;
Portmanteau for each fixed closed neighborhood of the limit
would give an atom there. Compact restrictions can be
taken at \(C_0+1\) in each coordinate; their boundary
has no atom. This applies equally to the limiting measures.
Using this bound or a finite grid in \(u+v\), the convergence
of the actual signed model is uniform for all real interval
endpoints in \(I_y\). Indeed approximate each moving interval
by neighboring grid intervals and then shrink the grid.
Also
\(\log_S T_y=1+O_J(1/\log S)\) uniformly at the actual \(y\),
so the strict \(d<T_y\) can be replaced **in the limiting
integer model only** by \(u<1\). The total coordinate
\(u+v\) stays away from zero because \(m\ge T_y\asymp S\).
No atom from \(d=1\) or \(n=1\) was removed in opening the
two variables; only the total-zero point is outside the
literal range.

The convolution cancellation \(A_\xi*B_\xi=\delta_0\)
is exact as measures locally, since only finitely many
terms of the power series on positive compact intervals
can contribute in each factor. The signed density from
[RoughQuotientWholeAnnulus.md, §3](RoughQuotientWholeAnnulus.md)
is
\[
                  A_\xi=\delta_0+
                       \xi^{-1}\rho'(u/\xi)\,du.
\]
On a total window away from zero, the limiting truncated
convolution \((1_{u<1}A_\xi)*B_\xi\) therefore equals
\(- (1_{u\ge1}A_\xi)*B_\xi\). This is a nonnegative
measure there; we are evaluating an integer model only.
Uniformly on the total interval \([1/2,C_0]\) its mass is
\[
 \le \rho(1/\xi)\, B_\xi([0,C_0])
 \le \rho(1/\xi)
       \exp\!\left(\int_\xi^{C_0}\frac{dt}{t}\right)
 =\frac{C_0}{\xi}\rho(1/\xi).                                  \tag{5}
\]
Here \(\rho\) is the ordinary Dickman function, decreasing
to zero, with \(\rho(t)\le1/\lfloor t\rfloor!\).
The bound in (5) is smaller than every fixed power of
\(\xi\) as \(\xi\) decreases to zero. It also covers arbitrary
subintervals of the total window. The endpoints of the actual
\(I_y\) are in that window for large \(N\), and all weak-limit
errors just justified are \(o_\xi(1)\) uniformly.

Thus the entire low-minimum integer model has absolute
size at most \(O(C_0\rho(1/\xi)/\xi)+o_\xi(1)\) in reciprocal
units. Subtract the missed model and add the true missed
part using (3) and (2). This proves (1) with \(A=2K\).
Repeated prime factors in the retained rough quotients can
be removed by the already checked physical large-square
bound. Every remaining factor exceeds \(S^\xi\) and
\(m\le S^{C_0}\), giving the stated finite rank. Neither
the integer Dickman sign nor the finite-rank restriction
implies a sign of the actual complementary prime-coupled sum.
