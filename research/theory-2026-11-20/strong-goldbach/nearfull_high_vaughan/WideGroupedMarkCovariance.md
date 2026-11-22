# A signed wide-profile block at the true product-divisor cutoff

Let \(N,J,L,x,y,M_N\) and \(P_F\) be as in
[the wide finite-angle theorem](WideJointGiantFiniteAngles.md).
In particular this is a fixed even target, \(x+y=N\),
\(x\in NJ\), and the actual sum keeps \((x,N)=1\).
Let the fixed smooth real profiles \(F,G\) be supported
on \([0,b_F]\), \([0,b_G]\), respectively.
Write \(h=.515\). For an independent true prime mark
interval \(\mathcal R=(R_-,R_+]\), define the score
\[
 B_{F,\mathcal R}(x)=
   \sum_{\substack{r\mid x,\ r\ {\rm prime}\\ r\in\mathcal R,\ r<x}}
       (\log r)\sum_{\substack{d\mid x/r\\rd\le N^h}}
                         \mu(d)F\!\left(\frac{\log(dN/x)}L\right).
\]
The analogous \(B_{G,\mathcal Q}\) has its actual
interval \(\mathcal Q=(Q_-,Q_+]\) and cap \(es\le N^h\).
The cap does nothing if, for example,
\(R_+ N^{b_F}\le N^h\).

**Theorem.** Assume \(R_-,Q_-\ge N^\xi\) and
\(R_+,Q_+\le N^{h-\nu}\) for fixed \(\xi,\nu>0\).
Uniformly in the actual real intervals, at each
sufficiently large even \(N\),
\[
 \sum_{\substack{x\in NJ\\(x,N)=1}}
       B_{F,\mathcal R}(x) B_{G,\mathcal Q}(y)
  = F'(0)G'(0)M_N
       \frac{\log(R_+/R_-)}L\,\frac{\log(Q_+/Q_-)}L
      +o(M_N).                                                    \tag{1}
\]
If either profile is flat near zero, the entire
left side is \(O_A(NL^{-A})\) for every fixed \(A>0\).

In particular take the literal wide affine profile
\(F=G=(1+t/(1-\lambda))C(t)\) of
[the whole mark transfer](WholeMarkPrimeTransfer.md),
with \(\lambda=.006\), \(C=1\) near zero and \(C=0\)
for \(t\ge.490\). For each mark window
\((N^{.006},N^{.025}]\) the extra cap is automatic:
\(.025+.490=.515\). This is an actual part of the
original wide low–low score (not a different profile).
Its signed weight is
\[
       \left(\frac{.025-.006}{1-.006}\right)^2M_N+o(M_N)
                            > .00036 M_N                          \tag{2}
\]
for all large even \(N\). The contribution is positive
after its own signed summation; it cannot be added to
any overlapping decomposition of the same score.
No claim is made for the mixed crosses with its
complement, for the whole low–low sign, or for Goldbach.

## Proof

**Group the actual product divisor before Poisson.**
The support gives the literal independent restriction
\(d\le N^{b_F}\), since \(x<N\). Retain that inequality
before Fourier inversion. The Fourier factor for the
left profile is
\[
      \exp(i\eta\log d/L)\, \exp(i\eta\log(N/x)/L).
\]
For each transform variable \(\eta\) the first factor
belongs to the grouped coefficient
\[
 a_\eta(A)=\!\sum_{\substack{A=rd\\r\ {\rm prime},\ r\in\mathcal R\\
                          d\le N^{b_F},\ A\le N^h}}
              (\log r)\mu(d)d^{i\eta/L}.
\]
The second belongs to the common spatial test, not
to this coefficient. There is an identical
\(b_\zeta(B)\) on \(B=se\). All \(A\) and \(B\)
are units at \(N\), and \((A,B)=1\) on the true
target-unit rows. The small mark bounds make the
conditions \(r<x,s<y\) automatic. The grouped
coefficient satisfies \(|a_\eta(A)|\le L\tau(A)\),
uniformly in \(\eta\), so on any dyad of scale \(A_0\)
its norm is \(O(A_0^{1/2}L^{C})\) by the ordinary
divisor moments. There are **no additional**
\(d,e\) outer counts in this step.

Smooth the actual central interval in an
arbitrary-log thin collar at arbitrary-log cost
by the true crossed divisor moments. Cut
\(|\eta|,|\zeta|\) at a fixed log power; the Schwartz
tails of the fixed profiles are arbitrary-log small
against the absolute actual crossed divisor envelope.
At each retained pair of transform variables the
remaining normalized spatial weight is smooth,
fixed-compactly supported in \((0,1)\), and has
log-power derivative norms independent of \(A,B\).
Open \((x,N)=1\) by \(\mu(u)\), \(u\mid N\), as in
[the original mark block, §1](JointGiantActualMarkBlock.md).
All \(u>N^{.0001}\) have power-small cost by the
actual \(u\mid x\) count and the crossed divisor
bound. Put \(X=N/u\) on the remaining \(u\)'s.
The true integer line is \(A v_1+B v_2=X\);
Poisson in \(v_1\equiv X\bar A\bmod B\) gives
exactly the same phase and prefactor as in that proof,
\[
  \frac X{AB}\widehat\Psi_{\eta,\zeta}(\ell X/(AB))
                                      e_B(\ell X\bar A).
\]
All grouped coefficients remain independent of
their opposite coordinate.

**Power margin with gathered norms.**
When the independent dyadic product \(A_0B_0\le
N^{.998}\), elementary progression floors and real
variation cost at most \(A_0 B_0 L^C\) at each dyad:
the grouped absolute sums obey their ordinary
divisor harmonic bounds. Otherwise put
\(g=\log_X(A_0 B_0)\) and
\(m_0=\log_X\max(A_0,B_0)\). The true powers give,
for large \(N\),
\[
          .998-o(1)\le g\le1.03011,\qquad m_0\le.51506.
\]
Across these dyads apply the same
[Bettin--Chandee, Theorem 1](https://arxiv.org/pdf/1502.00769)
as in
[the original mark block, §2](JointGiantActualMarkBlock.md).
That theorem permits the actual grouped coefficients:
only their individual square norms are used, and
\((A,B)=1\) is its own coprimality restriction.
Cut frequencies at \(X^\epsilon(1+A_0 B_0/X)\)
for a sufficiently small fixed \(\epsilon>0\);
the Fourier decay discards the tail.
On signed frequency dyads Mellin-separate the smooth
Fourier argument as there. Oscillatory powers do not
change the square norms. The four exponents
relative to \(X\), before arbitrarily small losses,
are
\[
 \begin{array}{ll}
 .7g+.25m_0-.85,\quad .875g+.125m_0-1,&g\ge1,\\
 .5-.65g+.25m_0,\quad .5-.625g+.125m_0,&g<1.
 \end{array}
\]
The worst is at most
\(.7(1.03011)+.25(.51506)-.85=-.000158\).
Choose the frequency and analytic power losses
sufficiently small. Since the true \(d,e\) labels
have already been gathered into \(A,B\), there is
no further power loss from them, even for the wide
profiles. The \(N^{o(1)}\) actual target divisors,
log-power dyads and Fourier seminorms still leave
a fixed power saving. The powers in this step are
only used for the nonzero modes, not for discarding
any actual retained factors.

**The same zero harmonic, unfolded at real marks.**
Unfold the grouped coefficients in the zero term.
Restoring the omitted unit divisors gives exactly
\(\varphi(N)/N\), with a power-small harmonic cost.
For fixed true \(r,s\) the actual masks are
\((d,Ns)=(e,Nr)=(d,e)=1\), and \(r=s\) is excluded.
The extra prime-specific limits \(d\le N^h/r\)
and \(e\le N^h/s\) are at least \(N^\nu\).
They have no effect at arbitrary-log precision on
the short Möbius harmonics, because one may truncate
after unfolding to \(d,e\le S=\exp((\log L)^4)\)
successively using the same uniform signed tails as
in [the original zero mode, §3](JointGiantActualMarkBlock.md).
For instance in the \(d\) tail the actual mask is
\(Nse\), of fixed polynomial size, and partial
summation sees only an additional interval endpoint.
The same holds for the \(e\) tail; all absolute
harmonics outside these cancellations are log powers.
On \(d,e\le S\) both true product caps are automatic.
The argument shift uses the actual central \(x,y\),
as in that earlier zero mode.

Thus the \(d,e\) harmonic is exactly the same one
already evaluated there: both zero moments vanish,
the product first-log derivative term is
\(F'(0)G'(0)\mathfrak S(N)c(rs)/L^2\) after the
CRT unit density, and the higher terms are \(o(M_N)\)
after the two prime-log harmonics. If a profile
is flat, the short-box constant instead has complete
signed zero with arbitrary-log remainder. The true
mark harmonic \(\sum_{r\in\mathcal R}\log r/r\)
has main \(\log(R_+/R_-)\); the removals for actual
target primes, the matching diagonal, and \(c(rs)-1\)
are power-small or negligible on this scale.
This proves (1) and the strict positive coefficient
in (2).

## An evaluated strip against the entire original wide low score

For the specific wide affine profile in (2), take \(C=1\)
through \(.486\), as in the whole mark transfer.
Put \(\rho=.518\), \(k=F'(0)=1/(1-\lambda)\),
\(\tau=.009\), and \(\Delta=\tau-\lambda=.003\).
Write \(L_F\) for the original wide score restricted to
marks at most \(N^\rho\), and \(W_0\) for its genuine
subwindow \(N^\lambda<r\le N^\tau\).
Use brackets with the actual ordered reflected rows
and target-unit condition as in
[the both-high reduction](JointGiantBothHighReduction.md).
Then
\[
 \langle W_0,L_F\rangle=\langle L_F,W_0\rangle
       = k^2\Delta(\rho-\lambda)M_N+o(M_N).                       \tag{3}
\]
The equality here means the same asymptotic even for
nonsymmetric \(J\); exact equality for a given \(N,J\)
is not required. Thus the true part of the wide
low–low product in which at least one mark is in
\(W_0\) is evaluated, with coefficient
\[
            k^2\{2\Delta(\rho-\lambda)-\Delta^2\}>0.
            \tag{4}
\]
This strip overlaps (2); the two amounts must not be
added without subtracting the literal overlap. If one
has already removed the union in (4), the self-pairing
of the disjoint remaining interval
\((N^{.009},N^{.025}]\) is instead
\(k^2(.025-.009)^2M_N+o(M_N)>.00025M_N\) by (1).
Its mixed crosses with still larger low marks remain
unpriced.

For the proof, opening \(W_0\) produces only actual
moduli \(q=rd\le N^{.499}\).
Ordinary maximal-prefix true-prime Bombieri--Vinogradov
therefore applies against \(\Pi(N-x)\).
The coefficient multiplicity for \(q\) is at most
\(\tau(q)\); real partial summation, including the
spatial shift in \(F\), is harmless. The exact reduced
main has \(1/\varphi(rd)\) and \((rd,N)=1\).
If \(r\mid d\), use \(d=r d'\) on squarefree
\(d\) and the absolute \(1/\varphi(r^2)\) bound
times the \(d'\)-harmonic; the \(r\)-sum with
this extra reciprocal power is power-small.
For \((d,rN)=1\), uniform masked
\(\mu(d)/\varphi(d)\) and its first log moment
at \(H=Nr\) give
\[
 \sum_{(d,H)=1}\frac{\mu(d)}{\varphi(d)}
                      F\!\left(\frac{\log(dN/x)}L\right)
       =-\frac{k\mathfrak S(H)}{L}+o(L^{-1}).
\]
The uniform endpoint harmonic calculation is that of
[the whole mark transfer, §2](WholeMarkPrimeTransfer.md);
only the first derivative survives. Summing the
literal \(r\)-log harmonic on \((N^\lambda,N^\tau]\)
and using \(c(r)=1+O(1/r)\) gives
\(\langle W_0,\Pi\rangle=-k\Delta M_N+o(M_N)\).
The same proof works in reflection.

The original \(-H_F=E\) is the genuine nonnegative
high affine source
\[
       E(x)=\sum_{\substack{x=q m,\ q>N^\rho\\q\ {\rm prime},\ m>1}}
                     k\,\frac{(\log q)\Lambda(m)}{L}.
\]
This holds since all divisor arguments on such a row
are at most \(\log(N/q)/L<.482\), within the exact
affine part of \(F\). In particular \(P_F=L_F-E\)
is a literal decomposition. The right coefficient
\(a_F=1-(1-\lambda)k\) is zero, so
[the whole mark transfer](WholeMarkPrimeTransfer.md)
gives \(\langle W_0,P_F\rangle=k\Delta M_N+o(M_N)\).

To evaluate \(\langle E,W_0\rangle\), use the true
product distribution of the same transfer, §1:
the actual \(E\) source has a genuine polynomial
prime slot \(q\) and the bounded \(\Lambda(m)/L\)
coefficient in its independent cofactor slot.
The moduli from \(W_0\) are still at most \(N^{.499}\).
This time the reduced principal retains
\((rd,Nx)=1\) at each fixed genuine \(x\).
The preceding inner harmonic proof is unchanged
with the polynomial mask \(H=Nxr\), and
\[
 \sum_{\substack{r\in (N^\lambda,N^\tau]\\r\ {\rm prime},\ r\mid Nx}}
          \frac{\log r}{\varphi(r)}=O(L^2N^{-\lambda})
\]
uniformly. Thus the restored principal is
\(-k\Delta\mathfrak S(Nx)+o(1)\) at each actual \(x\),
before its weight \(E(x)\).
The use of arbitrary auxiliary unit masks is part of
the cited product distribution; no prime density is
assumed on the other leg before the moduli are opened.

The factor \(\mathfrak S(Nx)=\mathfrak S(N)c(x)\)
can be replaced here by \(\mathfrak S(N)\) at
\(o(M_N)\) cost. Indeed \(q>N^\rho\),
and the only \(m\)'s weighted by \(\Lambda(m)\)
are genuine prime powers. Ordinary Chebyshev on
the \(q\)-interval at fixed \(m\) and
\[
       \sum_{m=p^j}\frac{\log p}{p^j}\,|c(p)-1|\ll1
\]
show \(\sum_x E(x)|c(x)-1|=o(N)\) on target units.
The high affine source mean is
\(\sum_x E(x)=(1-\rho)k|J|N+o(N)\) by
[the unconditioned high-window calculation](JointGiantBothHighReduction.md).
It follows that
\(\langle E,W_0\rangle=-(1-\rho)k^2\Delta M_N+o(M_N)\);
reflect for \(\langle W_0,E\rangle\).
Now \(k=(1-\lambda)k^2\) and \(L_F=P_F+E\)
give (3). Finally use (1) for
\(\langle W_0,W_0\rangle=k^2\Delta^2 M_N+o(M_N)\)
and exact inclusion-exclusion to obtain (4).

This uses true prime and product BV only on the
strict sub-root \(W_0\) moduli. The rest of the wider
window in (2) is not thereby evaluated against an
arbitrary opposite mark, and there is no estimate
of the total low–low sign.
