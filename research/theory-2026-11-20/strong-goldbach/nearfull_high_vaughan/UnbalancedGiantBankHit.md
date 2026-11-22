# Exact small-prime allocation in an actual two-giant signed block

Use \(N,J,L,x,y=N-x,Q_F,Q_G\) as in
[the unbalanced giant block](UnbalancedGiantMarkDispersion.md).
In particular \(F\) is an arbitrary fixed real smooth compact
profile, \(G\) is a fixed real smooth profile supported in
\([0,b_G]\) and flat near zero, and all marked rows have
\((x,N)=1\). Write \(M_N=|J|N\mathfrak S(N)\).
Keep the literal prime \(q\) in any interval with lower bound
\(N^\lambda\) and upper bound \(N\), or in any fixed collection
of such intervals. The cofactor \(m=x/q>1\) may be required
if working in the composite-only score. Keep the opposite
literal prime \(r\) in any actual subinterval of
\([N^{\rho_-},N^{\rho_+}]\).

Fix \(0<\eta<\sigma<\lambda\) and a strict margin in
\[
          \rho_->\tfrac12,\qquad
          33(\rho_++b_G)+28\sigma<17.                    \tag{1}
\]
Write \(\mathcal P\) for the actual primes in \((N^\eta,N^\sigma]\)
and \(\omega_{\mathcal P}(m)\) for the number of distinct such
prime factors of \(m\). The signed physical score
\[
 W(q,m;r,n)=(\log q)(\log r)\,Q_F(m;x)Q_G(n;y),
 \qquad x=qm,\quad y=rn,\quad x+y=N,\quad x\in NJ             \tag{2}
\]
is the same on every row; it is not a new calibrated score.

**Exact band removal.** The sum of (2) over all the specified
rows with \(\omega_{\mathcal P}(m)>0\) is \(O_A(NL^{-A})\)
for every fixed \(A\), uniformly in the target and mark
intervals. In fact one may multiply it by any \(1\)-bounded
function of a fixed finite occupancy vector within \(\mathcal P\),
constant within each vector, supported on the nonzero vectors.
Parts of the bank are fixed exponent subintervals. The
coefficients of this function may depend on \(N\).

**Actual rough-floor corollary.** Also suppose
\(\lambda+\rho_->1\) with a fixed positive margin. In the
entire block the contribution of the rows \(P^-(m)\le N^\sigma\)
is \(o(M_N)\). Thus the full score on this block is unchanged to
\(o(M_N)\) by requiring \(P^-(m)>N^\sigma\) on the left
cofactor. The zero-marker cofactor \(m=1\), if included,
is untouched by that requirement. This is a one-sided
deletion only: two such whole signed deletions cannot in
general be combined without paying the actual intersection.

For example with
\[
 \lambda=.501,\quad [\rho_-,\rho_+]=[.50999,.51001],
 \quad b_G=.0015,\quad \sigma=.004,
\]
the left side of (1) is \(16.99183\). Thus this deletion
allows the entire genuine \(q\) range from \(N^{.501}\) to
the physical endpoint, not just the \(.996\) chart of the
unbalanced block or the balanced \(.515\) range. There is no
lower bound here for the remaining signed quartic correlation,
and no sign change on rows without such a left small factor.

## 1. Exact allocation to a genuine short prime

Remove \(x\)'s divisible by \(p^2\) for some actual
\(p\in\mathcal P\). Their number is
\[
 \le \sum_{p>N^\eta}\left\lfloor N/p^2\right\rfloor
   \ll N^{1-\eta}.
\]
The whole log-weighted cost is power-saving by Cauchy and
ordinary divisor moments for \(x,N-x\). Indeed the number
of mark choices, the bank multiplicity, and the scores
are all bounded by fixed divisor powers, and \(N^\eta\)
is a fixed positive power during this proof.

On the surviving rows write \(m=pv\) for every true
bank prime \(p\mid m\). Their exact normalized mass is
\[
      \sum_{\substack{p\mid m\\p\in\mathcal P}}
                     \frac1{1+\omega_{\mathcal P}(m/p)}=1.
\]
This identity is per physical marked row \((q,m;r,n)\).
No probabilistic independence of bank events is used.
Also \(p\ne q\) by \(\lambda>\sigma\). Since \(p\nmid v\),
the *whole* left divisor score is
\[
 Q_F(pv;x)=\sum_{d\mid v}\mu(d)
   \left[
       F\!\left(\frac{\log(dN/x)}L\right)
       -F\!\left(\frac{\log(dN/x)}L+\frac{\log p}L\right)
   \right].                                                   \tag{3}
\]
A vector-dependent multiplier described above is inserted
as a bounded function of the actual \(v\)-vector plus one
in the bin of \(p\); refine the \(p\) cells to respect those
fixed bin endpoints.

Regroup \(x=p a\) with actual \(a=qv\). The long
coefficient may be signed and includes the sum over
the real \(q\mid a\), the log weight of \(q\), the
reciprocal selector, and all \(d\mid v=a/q\) in (3).
At fixed representatives \(x_0,p_0\) in a small cell,
this is a function of \(a\), not of \(p\). More precisely,
it uses the two short arguments
\[
      \frac{\log(dN/x_0)}L,\qquad
      \frac{\log(dN/x_0)}L+\frac{\log p_0}L .
\]
It is bounded by a fixed divisor power times \(O(L)\);
the latter is removed before applying dispersion. The short
coefficient is precisely the true prime \(p\), in its
actual interval and with its target-unit mask. It is
Siegel–Walfisz with arbitrary further unit masks: ordinary
prime Siegel–Walfisz uniformly in the fixed log-power
modulus, also for differences of two actual prefixes,
and deletion of prime divisors of the target and additional
mask. Only \(O(L)\) primes divide the target; the other
deletions cost at most a fixed divisor power of the
auxiliary mask (or simply by its number of distinct prime
factors). No uniform prime asymptotic at the geometric
cell width is required.

In the resulting separated product one can drop \(p\nmid v\),
since the additional physical rows all satisfy \(p^2\mid x\)
as above; they still have fixed total divisor power
multiplicity. This is done in the true side before
application of dispersion. On the reduced side the
principal cancels below for every \(x\), with no requirement
to reimpose this nonseparable mask.

## 2. Same literal progression and flat inner harmonic

Open \(e\mid n\) on the right, keeping the genuine
progression
\[
                         p a\equiv N\pmod{r e}.
\]
The modulus \(r e\) is a target unit and \(e\le N^{b_G}\);
\(r\) exceeds \(e\) and only one prime of its size can
divide \(r e\). Apply the localized unbalanced dispersion
of [§1 of the unbalanced giant block](UnbalancedGiantMarkDispersion.md)
to the independent long \(a\) and true short \(p\), at
\[
   X_0\asymp_J N,\qquad B\asymp p,\qquad
                  \gamma=\log_{X_0} R\le \rho_++b_G+o(1)
\]
for modulus dyad scale \(R\). The proof of that lemma
uses divisor bounds only on the long coefficient; it does
not require a true prime there. The localized majorant is
chosen on the \(a\)-variable so that every enlarged product
\(p a\) avoids \(N\) at constant relative distance.

Here are the details of separation. Choose fixed-aspect
product boxes narrow enough in \(p,a\) to permit that
long-slot majorant for every box meeting \(NJ\). Inside
them take an arbitrarily log-fine \(p,a\) mesh, respecting
actual \(p\) intervals and any occupancy-bin endpoints.
Delete those subboxes crossing the endpoints of \(NJ\);
the physical \(x\)'s they affect lie in strips of length
\(O_J(N L^{-C})\). Ordinary crossed divisor moments and
Cauchy pay their signed weights at arbitrary-log precision.
For every retained box choose its central representative
\(x_0\) and a \(p_0\) from its short interval. The spatial
variation in \(x\) and the angular variation in \(p\)
inside (3) are \(O_{F,J}(L^{-C})\), uniformly in all
actual \(d\mid v\). The right profile at \(e\mid n\)
is separated through the same \(x\)-representative.
The true freezing cost is bounded by the same crossed
divisor powers. For the reduced side there is only an
additional absolute harmonic \( \sum_{k\le N}
\tau(k)^{O(1)}/\varphi(k)\). The larger fixed-aspect box
determines the Cauchy smoother even for the finest
subcell. Thus signed separation and all error sums cost
only fixed log powers before the arbitrary-log saving.

The long \(a\) can have an actual factor \(r\) in the
*reduced* model, even where that is impossible in true
rows. Retain the literal \((r,x)=1\) in the model;
for a fixed \(x\) it is independent of \(e\). Since
\((e,r)=1\), the factor \(1/\varphi(r e)\) splits.
After assembling all \(e\)-dyads, the exact inner factor
is
\[
      \sum_{\substack{e\ge1\\(e,Nx)=1}}
          \frac{\mu(e)}{\varphi(e)}
                   G\!\left(\frac{\log(eN/y)}L\right)
                       =O_A(L^{-A}).                         \tag{4}
\]
This is the uniform flat harmonic from
[the balanced giant-mark block](AsymmetricGiantMarkDispersion.md),
with \(Nx\le N^2\) and fixed initial plateau of \(G\).
There is no \(p\)- or \(q\)-dependent factor in its test
beyond the exact unit mask in (4). Neither \(r\) nor
its bound is averaged across distinct targets. Summing
its remaining \(1/\varphi(r)\) harmonic, the weights of
the actual \(p,a\) and the finitely many mesh components
proves exact band removal.

## 3. From a genuine small-prime band to the actual lower-factor gate

For each actual pair of quotients \(m,n\), the condition
\(m q+n r=N\) and the target-unit mask force \((m,n)=1\).
It gives two genuine prime affine arguments in an integer
parameter with slopes \(n,-m\). Enlarge the parameter
interval to the full central interval at fixed \(m,n\),
of length \(\asymp_J N/(mn)\). This has a fixed
polynomial scale because
\[
                   mn\ll N^{2-\lambda-\rho_-}.
\]
At \(p\mid mn\) one affine argument is a nonzero
constant and the other has one root; at \(p\mid N\)
the two roots coincide; elsewhere there are two.
At \(p=2\) the target is even, \(m,n\) are odd, and
there is one root. A positive two-form Selberg sieve
at a sufficiently small fixed power of the parameter
length gives the true log-prime bound
\[
  \sum_{\substack{mq+nr=N,\ x\in NJ\\q,r\text{ prime in windows}}}
        (\log q)(\log r)
     \ll_{J,\lambda,\rho_-}
               \frac{M_N c(m)c(n)}{mn},
 \qquad c(h)=\prod_{\substack{p\mid h\\p>2}}\frac{p-1}{p-2}.
                                                                 \tag{5}
\]
This is the long affine positive upper from
[the full super-root transfer, §3](WholeSuperrootPrimeTransfer.md);
its proof does not assume any angular support on the
divisor profiles. No stated \(p\)-root restriction is
a claim of joint asymptotic here.

Extend the fixed profiles smoothly to compact profiles
on the real line. Fourier inversion of the actual
\(Q_F(m;x)\) bounds it by the integral of the product
\[
       \prod_{p\mid m}|1-e^{it\log p/L}|
\]
against a fixed Schwartz weight (the central spatial
factor has modulus one). The same holds for \(Q_G\).
For either leg, the harmonic in (5) times this product
is \(\ll(2+|t|)^C\) by the Euler series
\[
 \prod_{p\le N}
  \left(1+\frac{c(p)|1-e^{it\log p/L}|}{p-1}\right).
\]
The powers of a prime are already included exactly
through \(1/(p-1)\). Split using
\(|1-e^{iz}|\le\min(2,|z|)\) and the prime reciprocal
harmonics. Marking any prime \(p\le N^\eta\) on the
left adds at most
\[
           \ll \frac{|t|}{L}
                 \sum_{p\le N^\eta}\frac{\log p}{p}
             \ll \eta |t|.
\]
The sum is zero if this prime range is empty. Integrate
both fixed Schwartz bounds. Therefore every actual
row with \(P^-(m)\le N^\eta\) costs in absolute value
\(O_{F,G,J,\lambda,\rho_-}(\eta M_N)\), with a constant
independent of \(\eta\). This also absorbs the minor
overlap where such a row has a band hit as well.

For each fixed \(0<\eta<\sigma\), the difference
between requiring \(P^-(m)>N^\sigma\) and no roughness
equals the signed band sum plus a subset of the above
small-prime rows. First let \(N\to\infty\), then
\(\eta\downarrow0\). This proves the actual rough-floor
corollary, retaining the same exact one-sided physical
orientation and the original score.
