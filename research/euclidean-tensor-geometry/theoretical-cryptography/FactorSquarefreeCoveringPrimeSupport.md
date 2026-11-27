# Prime-support obstruction for squarefree distinct covers with minimum at least seven

A distinct cover of the integers is a finite family of residue classes
with distinct moduli greater than one whose union is all integers.
Let \(Q\) be the least common multiple of its moduli.

**Theorem.** If every modulus is squarefree and at least \(7\), then
\(2\cdot3\cdot5\cdot7\mid Q\) and \(Q\) has at least \(142\) distinct
prime factors. In particular its largest prime factor is at least \(821\)
and \(Q>10^{338}\). Equivalently, if any of \(2,3,5,7\) is absent or
\(\omega(Q)\le141\), a squarefree distinct cover must have a
modulus at most \(6\).

The starting point is the distortion method of
[Balister, Bollobás, Morris, Sahasrabudhe and Tiba](https://arxiv.org/abs/2211.01417)
and, specifically, the joint conditional-density comparison of
[Dai, Li, Li and Yi, Lemmas 3.1–3.2](https://arxiv.org/html/2611.15110v1).
Their Theorem 1.3(ii) gives the unconditional squarefree bound \(7\),
and their introduction notes a computational indication of a bound \(6\).
The present result is a proved restriction on a possible minimum-\(7\)
case; it does not prove the unconditional bound \(6\) or settle the
nonsquarefree odd-covering problem.

## Distortion and the squarefree two-state reduction

Use the CRT product over the prime factors of \(Q\), choosing an increasing
coordinate order. A class is introduced at its greatest prime factor.
Given a prefix, let \(\alpha\) be the uniform fraction of the next prime
coordinate \(p\) covered by newly introduced classes. For fixed
\(0\le\delta\le1/2\), set \(c=1/(1-\delta)\),
\[
 g(a)=c(a-\delta)_+,\qquad
 \kappa(a)=\frac{1}{1-\min(a,\delta)},\qquad
 \Delta(a)=c-\kappa(a).
\]
Tilt the conditional distribution of this coordinate by giving its
covered part mass \(g(\alpha)\) and splitting masses uniformly separately
over the covered and uncovered parts. The empty and full cases agree
with this prescription. The earlier marginal is unchanged, and the
conditional probability of any one residue is at most \(\kappa(\alpha)/p\).
Thus the distorted masses of the different introduced portions sum to at
least one if the family covers. If only \(a\ge\alpha\) is known, \(g(a)\)
and \(\kappa(a)/p\) are upper bounds for the corresponding quantities.
We allow \(a>1\) as a formal bound, using the same \(g,\kappa\).

Here is the specialization of the joint comparison that retains this
smaller point-mass cap. At a prefix, for the still unintroduced classes
record a vector of counts indexed by their remaining sets of prime
coordinates. For the current \(p\), the count for the singleton
\(\{p\}\) divided by \(p\) upper bounds \(\alpha\).
For later stages, let \(A_0\) be the vector of contributions not involving
\(p\); \(A_1\) is the sum of all possible contributions from classes that
do involve \(p\), after removing it from their remaining supports.
The realized new vector is \(A_0\) plus a sum of nonnegative vectors,
each occurring with conditional probability at most \(\kappa(a)/p\).
An increasing directionally convex function \(\Phi\) of this vector has
conditional expectation bounded by
\[
 V_{\kappa(a)}=\Phi(A_0)+\frac{\kappa(a)}p
                       [\Phi(A_0+A_1)-\Phi(A_0)] .
\]
Indeed, in the telescoped increment of \(\Phi\), the increment from
any one included vector is bounded by its increment if all preceding
vectors were included. Taking the conditional expectation proves this
inequality with no independence assumption.

The repair \(g(a)+\max\{V_{\kappa(a)},\,V_c-\Delta(a)/c\}\) is an
increasing directionally convex function of \(a,A_0,A_1\) by Dai et al.,
Lemma 3.2 at \(\vartheta=1/c\). The algebraic assertion of the lemma also
holds for \(a>1\), since for all \(a\ge\delta\) the same expressions have
\(\kappa=c\) and \(g\) affine. This permits backward iteration starting
from \(\Phi=0\), rather than independently bounding each stage. At
each earlier coordinate the input counts map to \(a,A_0,A_1\) by
nonnegative linear maps, which preserve increasing directional
convexity. The resulting bound is monotone in the supplied counts.
This is a finite comparison; no joint limiting distribution is needed.

To evaluate at the empty prefix, complete the comparison counts by
allowing all subsets whose moduli are at least \(7\), at most one class
per subset. In the two comparison states a previous prime either imposes
no active incidence, or all its incidences are active. If \(s\) previous
primes are active, put \(t=2^s\), the number of possible prefix subsets.
For a still later support of greatest prime at least \(7\), each vector
entry has its complete count \(t\). The two next states are \(t\) and
\(2t\). The admissible singleton count at \(p\), before division by \(p\),
is \(0\) at \(2,3\) (a modulus at most \(6\)), \(t-1\) at \(5\) (only
the empty prefix is disallowed), and \(t\) at every \(p\ge7\).
In particular the modulus \(7\) itself is not silently discarded.

Consequently, if the continuation function is \(H(t)\), the complete
upper comparison at the preceding stage is
\[
 T_pH(t)=g(a)+H(t)+
  \max\{\kappa(a)D,\ cD-\Delta(a)/c\},
 \qquad D=\frac{H(2t)-H(t)}p, \tag{1}
\]
where \(a=0\) at \(2,3\), \(a=(t-1)/5\) at \(5\), and \(a=t/p\)
otherwise. In the completed comparison, when replacing the status of a
prime by a two-state branch, all supports containing that prime have
their prefix count doubled together, while all remaining supports have
exactly the same admissibility rules just specified. In particular, for
the future singleton at \(5\), activating a preceding small prime adds
\(t\) to the previous \(t-1\), leaving \(2t-1\) rather than \(2t\).
This justifies the scalar reduction of the full vector iteration. The bound from the
first stage at \(t=1\) is an upper bound on the total distorted covered
mass estimated by the union bound.

## The finite rank certificate

For each membership pattern among \(2,3,5,7\), form the comparison
profile of length \(141\) by taking its included small primes and then
the first available primes at least \(11\). This suffices for an
arbitrary support of at most \(141\) primes: pad a shorter support
with unused larger primes, and compare every large coordinate with its
lower packed counterpart, using the **same distortion parameter** as at
that counterpart. For fixed \(\delta\) and \(p\ge7\), increasing \(p\)
decreases \(a=t/p\), \(g(a)\), and \(\kappa(a)\), and increases
\(\Delta(a)\); both max branches in (1) decrease, since \(D\ge0\).
The recursion is monotone in the continuation, as each branch is a
convex combination of \(H(t)\) and \(H(2t)\) plus a fixed correction.
It also preserves the increasing property, either from the vector
comparison or by increasing the complete counts. This proves the
packed-profile domination inductively.

The following specifies \(\delta\) for each prime in the packed profile
using its index among **all** primes, not its position within that profile:

| Absolute prime indices | \(p\delta\) |
|:--|--:|
| 1–2 | 0 |
| 3 | 1 |
| 4 | 2 |
| 5–7 | 4 |
| 8–11 | 8 |
| 12–19 | 16 |
| 20–31 | 32 |
| 32–50 | 64 |
| 51–54 | \(p/2\) |
| 55–80 | 128 |
| 81–97 | \(p/2\) |
| 98–125 | 256 |
| 126 onward | \(p/2\) |

The companion program computes (1) with exact rational numbers.
The cutoff \(t=1024\) is exact, not a tail heuristic: for all primes
in the packed profiles, \(\kappa(a)=c\) and \(g(a)\) is affine for
\(t\ge1024\) (at \(2,3\), \(g=0\) and \(\kappa=c=1\)).
Hence the continuation is affine throughout that tail by backward
induction, with coefficients computed from (1); below it there are
just the ten states \(t=2^s,\ 0\le s<10\).
All sixteen bounds are strictly below \(9999/10000\).
The largest occurs with all four small primes and is approximately
\(0.99987584593274\). Thus none of the supports is feasible.

## Excluding a missing small prime with no rank bound

For this part, use the weaker independent Bernoulli comparison
(Dai et al., Theorem 2.6), also obtained by replacing the conditional
cap by \(c/p\) everywhere. Omit the missing prime from the complete
allowed sequence. At every included prime put \(b_p=c_p/p\), and choose
independent Bernoulli variables \(I_p\) with means \(b_p\). With
\(X=2^{\sum_{q<p}I_q}\), the contribution at \(p\ge5\) is bounded by
\[
 b_p\,\mathbb E(X-p\delta_p-\mathbf 1_{\{p=5\}})_+ ;
\]
at \(2,3\) it is zero. Adding unused primes for this comparison only adds
admissible terms and cannot decrease its bound. As before, all
restrictions are based on modulus at least \(7\).

Through the first \(N=12000\) absolute primes use the same table, keeping
the first and third moments of \(X\) and the probabilities of \(X=2^s\)
for \(s\le18\). From a threshold \(A=p\delta_p+\mathbf 1_{\{p=5\}}\)
the expectation above is recovered as \(\mathbb E X-A+
\sum_{2^s<A}(A-2^s)\mathbb P(X=2^s)\), with \(A<2^{18}\).
Each stored nonnegative probability and moment is rounded upward
at scale \(10^{36}\); every distribution and moment update has
nonnegative coefficients. The exact constant \(A\) is subtracted only
after bringing the terms to a common denominator. No conditional
renormalization or floating-point comparison enters the certificate.

Write \(R\) for the upper third moment after the \(N\)-th absolute prime.
For \(k>N\) use \(\delta_{p_k}=1/2\). By
[Dusart's explicit prime bound](https://doi.org/10.1090/S0025-5718-99-01037-6),
\(p_k>10k\) on this range: \(\log k>9\) and \(\log\log k>2\).
A stage costs at most \(32\mathbb EX^3/(27p_k^3)\) using
\((x-A)_+\le4x^3/(27A^2)\), which follows by factoring
\(4x^3-27A^2x+27A^3\) for \(x\ge A\). The third moment is multiplied
by \(1+14/p_k\). Thus before stage \(k\) it is bounded by
\(R(k/N)^{7/5}\), using \(1+x\le e^x\) and the harmonic-sum
integral. The remaining cost is at most
\[
 \frac{32R}{27\cdot 10^3 N^{7/5}}
       \sum_{k>N} k^{-8/5}
 \ \le\ \frac{32R}{16200 N^2}.
\]
The first \(N\) stages plus this infinite tail are below \(3/4\) in all
four cases: the diagnostic decimals for missing \(2,3,5,7\) are
respectively \(0.28620,\ 0.39283,\ 0.48274,\ 0.55963\) (rounded upward).
So every hypothetical cover in the statement contains all four primes.

The largest-prime and LCM consequences follow from the product of the
first \(142\) primes; their numerical inequalities are also checked by
the companion certificate. No unrestricted estimate for arbitrary
nonsquarefree moduli is claimed.
