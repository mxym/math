# The true asymmetric giant-mark block with a polynomially short cofactor

Use the fixed even target \(N\), a fixed interval \(J\Subset(0,1)\),
\(L=\log N\), \(x\in NJ\), \(y=N-x\), and the scores
\[
 Q_F(m;x)=\sum_{d\mid m}\mu(d)F\left(\frac{\log(dN/x)}L\right),
 \qquad
 Q_G(n;y)=\sum_{e\mid n}\mu(e)G\left(\frac{\log(eN/y)}L\right).
\]
The profiles are fixed real smooth functions; \(F\) may have any
fixed compact support, and \(G\) is flat near zero with support in
\([0,b_G]\). All prime marks in this note are literal primes. Keep
\((x,N)=1\) on every physical row.

Fix closed positive-width exponent intervals \(I_q,I_r\) with a
strict positive margin in the following conditions for all
\(\alpha\in I_q,\rho\in I_r\):
\[
 0<\sigma=1-\alpha,\qquad \tfrac12<\rho,\qquad
                  33(\rho+b_G)+28\sigma<17.                       \tag{1}
\]
Any actual subintervals of these prime ranges are allowed. Then
for every \(A>0\), uniformly for all sufficiently large even \(N\),
\[
 \sum_{\substack{x+y=N,\ x\in NJ,\ (x,N)=1\\
      x=qm,\ y=rn,\ q,r\ {\rm prime}\\
      \log q/L\in I_q,\ \log r/L\in I_r}}
   (\log q)(\log r) Q_F(m;x)Q_G(n;y)
                                \ll_A NL^{-A}.                    \tag{2}
\]
The actual prime \(q\) can be very long, above \(N^{.995}\),
while the opposite prime \(r\) is also genuinely above the root.
For example take \(I_q=[.99599,.99601]\),
\(I_r=[.50999,.51001]\), and \(b_G=.0015\).
Here the worst value on the left of (1) is \(16.99211<17\).
The upper cutoff on \(q\) is polynomially below \(N\); in
particular the proof does not include the unit cofactor or an
original subpower terminal window. The full signed contribution
of this block is zero at the stated scale, not the full
two-composite covariance.

This is a different strict region from the balanced
[Fouvry–Radziwiłł block](AsymmetricGiantMarkDispersion.md), where
the longer slot is Siegel–Walfisz and the mark \(q\) is at
most \(N^{17/33}\). Here the *short* signed divisor score is
Siegel–Walfisz. The analytic input in this note is
[Wright I, Theorem 2.3 and §4](https://arxiv.org/pdf/2604.25177v2),
with the macroscopic-residue step proved below, not assumed
from its printed small-residue statement. The older published
[Fouvry–Radziwiłł unbalanced proof](https://arxiv.org/pdf/1811.08672)
gives the same argument with \(36\sigma\) in place of
\(28\sigma\). The illustrative box violates that older sufficient
inequality, including with the smallest \(\rho,\sigma\) in the box.
No new general level-of-distribution result beyond these methods
is asserted.

## 1. Localized unbalanced dispersion at the literal large residue

Write \(X_0=MB\), where \(M\) is the long slot and \(B\)
the short slot (Wright's \(N\), not the target here). Take fixed
relative-width subintervals within \([M,2M]\), \([B,2B]\),
and real bounded divisor-power coefficients supported on even
smaller arbitrary subintervals. Assume \(X_0\asymp_J N\) and
that a fixed enlargement of the long interval, multiplied by
any short position in its interval, lies in a fixed compact
subset of \((0,N)\). Also assume every actual short coefficient
is supported on \((n,N)=1\), which is sufficient for our
application. The modulus dyad scale is denoted \(Q\).
In particular our use has \(Q\gg B\), \(M\ge QX_0^c\) and
\(B\ge X_0^c\) for a fixed \(c>0\).

The proofs in question apply with residue \(a=N\) and use one
fixed nonnegative long-variable smoother \(\psi(m/M)\) in
Cauchy–Schwarz, equal to one on the true long interval and
supported in that enlargement. This can be an affine rescaling
of a fixed compact Gevrey cutoff, so the Poisson formula and
its \(O(M^{-1})\) error in
[Fouvry–Radziwiłł, Lemma 2.1](https://arxiv.org/pdf/1811.08672)
still hold with a fixed constant in the \((\log X_0)^4\)
frequency bound. A larger fixed constant in the log bound also
covers the partial summations with \(\widehat\psi\). In particular
the actual tiny subintervals only enter the original
coefficients; the Cauchy smoother never needs their width.
Here are the residue checks in the proof.

* The first Cauchy step and the \(U,V\) main terms and errors
  (FR §§3–5, formulas (17)–(23)) use \((a,q_i)=1\) and Poisson
  uniformly in the reduced residue. Neither uses a bound on
  the size of that residue. Their errors are \(B^2Q L^{O(1)}\).
* In the truncation of \(W\), FR's (25) and Lemma 6.1 use
  \(|a|\le X_0/3\) to avoid \(mn-a=0\) in the *support of the
  Cauchy smoother*, not just the support of the input long
  coefficient. In our localized setup
  \(0<c_J N\le N-mn\le N\) on that support; thus every divisor
  weight in that argument is on a positive integer comparable
  to \(X_0\). The target units in the short slot make the
  progression for \(|mn-a|\) reduced modulo \(n\). For the
  additional condition \(m\equiv a\overline{n'}\pmod{k}\),
  reduce the affine progression for \(a-mn\) by
  \(g=(k,n-n')\); its gcd is precisely \(g\) because
  \((a,nk)=1\) on the relevant row. It has interval scale
  \(X_0/g\) and modulus \(nk/g\ll (X_0/g)Q/M\).
  Thus the same short-interval divisor bound (FR Lemma 2.3)
  applies, with an extra \(\tau(g)\) before reduction.
  For completeness this extra divisor weight can be kept in
  the gcd truncation: for \(n\ne n'\) open
  \(\tau(g)=\sum_{u\mid k,u\mid n-n'}1\). For a pre-existing
  common modulus \(\delta\mid k\), the pair now has modulus
  \([\delta,u]\le 2B\), and its \(n,n'\) weight is
  \(\ll B^2L^{O(1)}/[\delta,u]\) below \(B^{1/4}\) by the
  reduced divisor bound (the class of \(n'\) is a unit).
  For the larger pair moduli use divisor bounds
  \(B^{o(1)}\) and the elementary bound \(O(B^2/[\delta,u])\).
  Since
  \[
    \sum_{u\mid k}\frac1{[\delta,u]}
       \le \frac{\tau(\delta)}{\delta}\sum_{v\mid k}\frac1v,
  \]
  summing \(k\sim Q\), with any prescribed divisor
  \(\delta\mid k\), keeps both reciprocal \(\delta\)'s.
  In the large \([\delta,u]\) portion use Rankin with
  exponent \(1/4\), in that portion only, to obtain the
  additional \(B^{-1/16+o(1)}\). In detail, the resulting
  \(1/[\delta,u]^{3/4}\) times the \(k\)-harmonic over multiples
  of \([\delta,u]\) costs \(O([\delta,u]^{-7/4})\). Group by
  \(g_0=(u,\delta)\mid\delta\) and \(v=u/g_0\), for which
  \([\delta,u]\)=\delta v\); the sums of
  \(\tau(\delta)\delta^{-7/4}\) and \(v^{-7/4}\) converge.
  In this part one may omit the other gcd-cutoff conditions
  since the power saving already pays for them. For \(n=n'\)
  the weight is
  \(O(MB L^{O(1)})\), since the remaining prescribed
  \(k\) costs \(M/k\) with \(\tau(k)\), and the
  \(n\)-weight is an ordinary divisor moment. This gives
  the stated polylogarithmic \(D\)-cutoff error
  \(MB^2D^{-1/2}L^{O(1)}\) for
  \(d,d_1,\delta,\delta_1,\delta_2\) in (26)–(30).
  For example when \(\delta_1>D\) the modulus \(k\)
  is a multiple of \(\delta\delta_1\) with
  \(\delta_1\mid\delta^\infty\); the remaining sum is
  bounded by
  \(L^{O(1)}\sum_{\delta}\tau(\delta)\delta^{-2}
      \sum_{\delta_1\mid\delta^\infty,\delta_1>D}\delta_1^{-1}
    \ll D^{-1/2}L^{O(1)}\).
  The first two truncations \(d,d_1\) use the unconditioned
  reduced divisor progression in \(n\) for the long variable.
* The CRT formula (32)–(38) and the zero-frequency restoration
  (40)–(42), (50) use only the reduced residue, not its size.
  The zero-frequency restoration is the same positive divisor
  estimate on \(M/[q_1,q_2]\), or the bound already given for
  this model in FR §6.4. The Poisson remainder is
  \(M^{-1}B^2Q^2L^{O(1)}\).
* In FR (47), the residual smooth phase after reciprocity has
  size at most \(O(D^{O(1)}L^4 |a|/(MB))\): indeed
  \(|h|\ll (Q^2/M)L^4\) and the denominators contain one
  short variable and both long moduli up to powers of \(D\).
  Its logarithmic derivatives have the same bound. Thus the
  integrations leading to (48) are unchanged with
  \(|a|\ll_J MB\). In the succeeding trilinear estimate
  the explicit multiplier in FR (49), or Wright §4 just
  before (8), is a bounded power of \(1+|a|/(MB)\);
  the other fixed congruence decompositions do not depend on
  the size of \(a\). In particular the use of Wright's
  partially fixed modulus bound on (48) gives the same (8):
  \[
    D^{O(1)}X_0^\epsilon
        (Q^{15/8} B^{11/4}+M^{3/20}Q^{33/20}B^{51/20}).
  \]

These are all the size uses of \(a\) in FR §§3–6 and
Wright §4. This does not assert that arbitrary supports at
\(a\asymp X_0\) are safe. In particular shifting the residue
per modulus rather than changing the Cauchy support would not
give this proof. The displayed preliminary error
\(O(MB^2Q^{-1}X_0^{\eta-\epsilon/2}
       +X_0^{1+\eta+\epsilon^2})\) in Wright §4 is harmless
even if retained: choose its small parameters after the
strict positive lower bound on \(\log B/\log X_0\).

The short-sequence discrepancy of FR Lemma 8.1 is
\(E^*\ll_A B^2QL^{-A}\) if the short slot is
Siegel–Walfisz with arbitrary auxiliary unit masks and
\(B\ge X_0^c\). Thus one obtains \(O_A(X_0L^{-A})\)
for the sum of absolute discrepancies, with
\(D=L^{C_A}\), provided the two normalized error exponents
satisfy
\[
       15\gamma+14\sigma<8,\qquad 33\gamma+28\sigma<17,
       \qquad \gamma=\log Q/\log X_0,\quad
                       \sigma=\log B/\log X_0.
\]
The first follows from the second for \(\gamma\ge1/2\);
all omitted margins, including \(M>QX_0^c\), follow on
compact subsets of (1).

## 2. The short signed coefficient has the required distribution

Fix a central representative \(x_0\) before freezing the
spatial weights. On the short slot \(m\asymp B\), put
\[
 \beta_m=1_{(m,N)=1}1_{m\in I}
         \sum_{d\mid m}\mu(d)F\left(\frac{\log(dN/x_0)}L\right).
\]
There is no restriction of roughness or squarefreeness on \(m\).
We check the Siegel–Walfisz discrepancy with auxiliary mask
\((m,v)=1\), for \((a_0,k)=1\) and \(k\) at most a fixed
log power; this is exactly what is needed in FR Lemma 8.1.
The standard larger \(k\) range in its proof uses only
\(|\beta_m|\ll\tau(m)\). The desired bound at small \(k\)
is \(O_A(BL^{-A}\tau(v)^{C})\) (a fixed divisor power
suffices in the harmonic over \(v\)).

Split \(m=dj\) at \(d=\sqrt B\), keeping the actual interval
\(I\). For \(d\le\sqrt B\), fix \(d\) and count free
\(j\), including its independent target and auxiliary
unit masks. Compare the reduced progression with its
principal by inclusion-exclusion, with per-\(d\) error
\(O(\tau(N)\tau(v)\tau(k))\): the remaining free count
on a coprime residue after opening a divisor has the
same length-over-\(k\) term as its reduced average.
Factors of \(k\) in that divisor cannot occur in the
progression or reduced sum. The aggregate error is
\(B^{1/2}\tau(N)\tau(v)L^{O(1)}\), power-saving by
the fixed polynomial lower bound on \(B\).

For \(d>\sqrt B\), fix \(j\ll\sqrt B\); the actual
\(d\)-interval has endpoints on scale \(Y\asymp B/j\).
Use ordinary Möbius Siegel–Walfisz in a reduced progression,
with the coprime mask \(H=Nv\). To see its uniformity in
the target, use the exact mask convolution
\[
  \mu(d)1_{(d,H)=1}
     =\sum_{h\mid d,\ p\mid h\Rightarrow p\mid H}\mu(d/h).
\]
Terms with \((h,k)>1\) occur in neither reduced sum.
For \(h\le Y^{1/4}\), Möbius Siegel–Walfisz on the actual
interval at scale \(Y/h\), followed by the absolute
\(h^{-1}\) sum, costs \(O_A(YL^{-A}\tau(v)^C)\).
For the tail the count of integers up to \(O(Y/h)\) is
\(O(Y/h)\) on actual support, and the Rankin bound
\[
 \sum_{h>Y^{1/4},\ p\mid h\Rightarrow p\mid H}h^{-1}
  \le Y^{-1/(4\log L)}
          \prod_{p\mid H}(1-p^{-1+1/\log L})^{-1}
 \ll_A L^{-A}\tau(v)^C
\]
holds. Indeed for \(p\mid N\) split at \(L^2\): the small
primes contribute \((\log L)^{O(1)}\) by Mertens and the
others contribute \(O(1)\) to the logarithm. Each prime
of \(v\) contributes at most an absolute factor.
Partial summation in \(d\) allows the literal smooth
factor \(F(\log(dN/x_0)/L)\), whose variation is bounded.
Sum the harmonic \(\sum_{j\ll\sqrt B} B/j\), and
increase the log accuracy by one. This proves the
asserted short-slot property uniformly in both masks,
all actual prefixes, and central representatives.
It uses no distribution result above the ordinary
log-modulus Möbius regime on this slot.

## 3. Restore the literal two-prime correlation

Open only the genuine \(e\mid n\), obtaining the
progression \(qm\equiv N\pmod{r e}\), with
\(e\le N^{b_G}\). The prime \(r\) exceeds \(m\)
and \(e\), and is below the true prime \(q\) by
fixed margins from (1). Thus \((r,e)=(r,x)=1\).
There is at most one possible \(r\) in a fixed modulus
\(re\) since it exceeds the root of \(N\) and
\(re<N\). No residue is changed. The long slot is
the genuine unit prime coefficient on \(q\) with
\(\log q/L\).

Make fixed-aspect outer subdivisions of \(q,m\)
so that whenever a box meets the central product
range its enlarged long support times its short
support stays inside a fixed compact subinterval
of \((0,N)\). This is possible with fixed ratios
sufficiently close to one in terms of the two
endpoints of \(J\). On each such box make a log-fine
independent subdivision of \(q,m\), and omit those
subboxes crossing the two endpoints of \(NJ\).
Their true \(x\)'s lie in strips of total length
\(O_J(NL^{-C})\). Ordinary divisor moments and
Cauchy applied to \(\tau(x)^D\tau(N-x)^D\) pay
any fixed divided-component multiplicity and
all log weights there. On the retained subboxes
freeze both spatial arguments in the profiles at
their central representative. The derivative in
\(x\) of their displayed log arguments is
\(O_J(1/(NL))\); true crossed divisor moments
again make the total loss arbitrarily log-small.
The same estimates for the reduced principal
use the additional absolute harmonic
\(\sum_{k\le N}\tau(k)^{O(1)}/\varphi(k)\).
In the finite-log mesh the Cauchy smoother of
§1 is always that of the *outer* box.

Apply §1 to each retained box and dyad of
\(k=re\), using §2 on the actual \(m\)-coefficient.
All dyad scales satisfy \(\gamma\le\rho+b_G+o(1)\)
and \(\gamma\ge\rho+o(1)\). The error is summed
absolutely, so the actual \(r,e\) weights of
size \(O(L)\) cost only extra log powers. This
leaves the exact reduced principal, with
\(1/\varphi(re)=1/(\varphi(r)\varphi(e))\),
and the literal mask \((e,Nx)=1\).
At each \(x\) one can reassemble the dyads in
\(e\) before applying the signed flat harmonic:
\[
 \sum_{(e,Nx)=1}\frac{\mu(e)}{\varphi(e)}
              G\left(\frac{\log(eN/y)}L\right)\ll_A L^{-A}.
\]
This is the uniform flat short-harmonic cancellation
from [the balanced block, §1](AsymmetricGiantMarkDispersion.md):
the masked \(\mu/\varphi\) harmonic has a zero at the
origin, and its tail from a fixed initial power of
\(N\) has arbitrary log savings uniformly for
\(Nx\le N^2\). Reassembly is essential; an individual
\(e\)-dyad need not cancel. The sum of
\(\log r/\varphi(r)\) costs \(O(L)\), and the remaining
absolute source divisor envelope is \(NL^{O(1)}\).
This proves (2).

The block need not have a pointwise zero coefficient:
one may take \(F=1\) on a short initial interval but
\(F=0\) throughout a neighborhood of the displayed
positive \(\sigma\), still with arbitrary wider compact
support elsewhere. On true \(m\) prime in that
neighborhood one has \(Q_F=1\) exactly for large
\(N\). The distribution argument does not replace this
prime cofactor, the long prime, or the opposing real
mark by independent densities in the original sum.

A useful cutoff corollary for genuinely flat \(F\) is that
the whole composite-only tail \(q\ge N^{\alpha_0}\) vanishes
against the same \(r\)-window, whenever (1) holds strictly
at \(\alpha_0\). If \(F\) is constant on \([0,a_F]\),
then for \(1<m\le N^{a_F/2}\) every true divisor of \(m\)
falls into that initial plateau for large \(N\), and
\(Q_F(m;x)=0\) by \(\sum_{d\mid m}\mu(d)=0\). Therefore
only a fixed polynomial range of \(m\) remains, and (2)
applies to it (enlarge the nominal upper \(q\)-exponent
slightly to absorb fixed central constants). This corollary
does not include the prime atom \(m=1\), nor does it price
the matching nearly-full tail of a nonflat \(F\).
