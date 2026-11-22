# A level .555 upper sieve for genuine angular prime-product sources

Use exactly the source class and normalization of
[AngularPrimeDomination](../AngularPrimeDomination.md):
\(P\) is a prescribed even integer, \(I=[P/3,2P/3]\),
\(X_P=|I|\mathfrak S(P)\), \(\Pi(y)=(\log P)1_{y\ {\rm prime}}\),
and \(C(x)\ge0\) is a bounded angular weight times \(\log P\)
on the genuine squarefree rank-\(k\) products in \(I\).
Here \(k\ge2\), the least-factor exponent cutoff is fixed positive,
and the allowed profiles and position weights are as in that proof.
The source mean is \(m_C=|I|^{-1}\sum_{x\in I,(x,P)=1}C(x)\).
Then, uniformly through the even targets,
\[
 \limsup_{P\to\infty}
    \left\{\frac{\langle C,\Pi\rangle}{X_P}-\frac{400}{111}m_C\right\}
    \le 0.                                                     \tag{1}
\]
This improves the constant \(200/53\) from that proof using its
same three-group construction on the actual Rosser support,
not a different source or a new distribution theorem.

## 1. The enlarged classical Rosser support

Take \(x_0=P/3\), and in Section 1 of
[the original proof](../AngularPrimeDomination.md) set
\[
 D=x_0^{111/200},\qquad z=x_0^{187/1000},\qquad
 \Theta=2221/4000=.55525 .
\]
The upper classical Rosser label on the large bank is still
restricted by every odd cubic prefix
\(l_1\cdots l_{j-1}l_j^3<D\), with \(l_i\) in their
true decreasing order. The exact rounded-up inclusion--exclusion
tree and the separate small-prime bank are unchanged. This is
a pointwise positive upper even if the first cubic test
already discards some primes below \(z\).

Use [Lichtman, arXiv:2309.08522v1, Proposition 6.1 and its proof](https://arxiv.org/html/2309.08522v1#S6)
with spectral exponent \(\theta=7/32\), and an upper bound
\(\alpha=1001/1000\) for the exponent of the actual residue
\(a=P\). For all large \(P\), the scale \(x\) of each dyadic
product chart obeys \(P\le x^\alpha\). The proof of the
proposition applies at any fixed source length \(A\) in its
stated range \(x^\tau\le A\le x^{1/3-\tau/2}\), with
\(\tau>0\) chosen sufficiently small after the source ranges.
The notional physical label level in the proposition is
\(x^{\Theta-2\tau}\). We use \(D\le x^{\Theta-2\tau}\),
which has fixed slack if \(\tau<10^{-5}\); fixed scale constants
do not affect this strict exponent comparison. Odd cubic
prefixes imply the required all-prefix square support:
the preceding odd cubic constraint implies the next even
square constraint since \(l_{j}\le l_{j-1}\).
The upper prime ceiling \(t_1=\log l_1/\log x\) is
\(.187+o(1)\).

Here are explicit checks covering every length of the true
large-bank label. Split at \(t_1=.1107\).

* If \(t_1\ge .1107\), the three entries of (6.2) in
  Lichtman are at least \(.55535\), greater than \(.65\),
  and greater than \(.60\), respectively, at the extreme
  allowed endpoints (fixed dyadic constants may first be
  absorbed by allowing ceiling \(.1871\)). Thus (6.2)
  covers \(\Theta\), at any number of label primes.

* If \(t_1<.1107\) and there are at least three primes,
  \(t_1\) is strictly below
  \(\mu=\min((1-\theta)/(4-3\theta),(1-\alpha\theta)/4)\).
  In the notation of (6.9), the three upper entries defining
  the interior of \(w(t_1,t_2,t_3)\) are respectively greater
  than \(.581,.5561,.778\). These follow from
  \(0\le t_3\le t_2\le t_1<.1107\) and direct substitution.
  The lower gate for this entry is \((1+t_1)/2\le .55535\).
  So this is an **active** entry and proves (6.4) with
  \(\Theta=.55525\). We do not apply (6.4) on an empty
  or two-prime prefix.

* If \(t_1<.1107\) and there are at most two primes,
  the enlarged modulus after attaching the small-prime
  bank is at most \(x^{.2214+b+o(1)}\), far below the
  ordinary convolution BV level. This includes the unit
  label; the same separate branch in the original proof
  controls it.

The three independent factor groups and the three inequalities
(6.3) therefore hold on each admissible large-bank vector.
Use exactly the original proof's binning and margins:
choose \(A=Nx^{-\tau}\) for the short source length \(N\),
assign the group indices on one feasible representative
of the rounded exponent box, and then retain the **same**
indices throughout that box. The first, second, third
power margins from (6.3) are \(3\tau,3\tau,2\tau\);
passing from \(A\) to \(N\) spends respectively
\(2\tau,\tau,(1+2\theta)\tau\).
The independent small-bank factor, of size \(x_0^b\),
joins group three and costs at most \((2+2\theta)b\)
in any product rail; choose \(b\ll\tau\).
Then choose the rounding mesh sufficiently small for
all remaining box endpoint losses, after picking the
small-prime cutoff exponent. This leaves strict room
for (5.2), including \(Q_1<N/x^{\epsilon'}\) and the
factor \(a^\theta\) at the actual residue. Within a
repeated bin the finite factorial factors and the
removed repeated **prime** error are handled as before:
for the latter, actual and model costs are bounded
by \(x^{o(1)}\sum_{q\ll x^{.555+b},\ \exists r>x^\xi,\ r^2\mid q}
(x/q+1)\), a fixed-power error. Proper prime powers in
source labels and repeated or target-dividing source
primes retain their old fixed-power deletion. No
wholly arbitrary weights on moduli are admitted.

The rest of Sections 1--2 of the original proof is unchanged.
In particular its selected short HB slot has Siegel--Walfisz
with the auxiliary unit masks, while the two-large-free
branch uses the uniform Proposition 3.2, which permits
the enlarged modulus since \(.555+b<2/3-O_k(\tau)\).
The smooth source separation, bounded coefficient
truncations, and the actual common interval are as there.
All fixed power reserves can be taken before the logarithmic
saving. The exact rounded progression sum is evaluated
first; its principal-only error is removed by sending the
rounding mesh to zero after the large-target limit for the
fixed small-bank exponents. Then send the small-prime
cutoff exponent to zero with \(b\) fixed. Thus no weighted
error is lost by deleting irregular angular boundaries.

## 2. True model and signed consequence

The same dimension-one upper linear sieve in the
principal now has \(s=.555/.187=555/187\in[1,3]\).
With the usual \(F(s)=2e^\gamma/s\) on this interval
and the Mertens factor
\(e^{-\gamma}\mathfrak S(P)/(.187\log P)\), the
coefficient is \(2/.555=400/111\). The exact omitted
unit primes in the local profile cost \(1+o(1)\) on
fixed angular support, and small-bank approximation and
Jordan approximation are the same as in
[the original proof](../AngularPrimeDomination.md).
This proves (1).

For the **same** native quadratic \(J_H\), the existing
two-sided identity (2) in the original proof is
\(\langle C,J_H\rangle/X_P=\langle C,\Pi\rangle/X_P-4m_C+o_*(1)\).
It does not depend on the value .53 of the outer upper
sieve. In the same iterated order of limits it follows that
\[
 \limsup_{\theta_0\downarrow0}\limsup_{P\to\infty}
 \left(\frac{\langle C,J_H\rangle}{X_P}+\frac{44}{111}m_C\right)
 \le0.                                                         \tag{2}
\]
Here \(\theta_0\) is the rough-band parameter in the native
score, not the spectral exponent. The old absolute face,
band, and prime-power errors in the actual rank-two and
rank-three applications remain valid (in particular they
can keep the old \(200/53\) upper wherever only an absolute
tail is needed). Therefore in its equation (4) the native
ordered high-by-high lower becomes
\[
 \liminf_{\theta_0\downarrow0}\liminf_{P\to\infty}
    \frac{\langle J_{H,2}+J_{H,3},J_H\rangle}{X_P}
    \ge \frac{44}{111}\Big(2+4\log2-\frac{\pi^2}{6}\Big)>1.23 .
                                                               \tag{3}
\]
These are disjoint ranks of the first coordinate in a
single ordered interaction. We have not doubled (3) by
reflection, nor applied it to a different cusp kernel.
No lower bound for the remaining native signed bilinear
terms is asserted.

## Comparison and scope

[Slava Chan's November 6 preprint, Theorem 2.1 (12)--(14)
and Proposition 4.1](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf)
**claim a stronger** upper for the overlapping class of
fixed finite bounded-rank smooth true product-prime
families, with every source factor of fixed polynomial
length, bounded weights with polylogarithmic Euler
derivatives, and no additional arithmetic filter.
Its distribution is indeed at the literal target residue
\(N\) modulo \(q\), not a fixed small residue or an
ordinary marginal. Its \(K/2=3.3808684\) is the corresponding
constant here: its \(H_N=C_N N/\log^2N\) and our
\(\mathfrak S(N)=2C_N\), and the ordinary profile mean
includes the chosen macroscopic interval's length.
One could pass from its smooth class to compact Jordan
profiles by the original positive approximation and
compare the actual thin-tail bounds separately.
That preprint's retained-phase Proposition 3.2,
large-modulus Appendices A--E and coefficient/numerical
realization are **not independently verified or used here**.
The present estimate is a parameter change in a different
ordinary Rosser construction under the explicitly cited
Lichtman inputs, not a claim of priority.

This improves a true fixed-target envelope and a
specific signed native response. It does not control the
whole signed remainder, and does not remove the general
positive-envelope parity budget obstacle.
