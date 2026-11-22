# The exactly-two-small debit is dominated on true Goldbach rows

Use the notation and **same literal score** of the
[direct composite-gap identity](../direct_goldbach_composite_gap/Proof.md).
Thus \(N=2x\) is even, \(L=\log x\), \(\ell=\log L\),
\(z=\exp(L/\ell^2)\), \(J=xJ_0\) for a fixed nondegenerate interval
\(J_0\subset[1,3/2]\), and \(\mathfrak S(N)\) is its singular factor.
Write \(P=N-y\), and keep only genuine \(P\) prime. A prime dividing
\(y\) is *small* if it is \(<C_y=y/x^{1-\epsilon}\).
Let \(k(y)\) count those primes on a squarefree, \(z\)-rough \(y\).
The reference \(\mathcal R_0\) here always uses the *own*
square-root cutoff \(\sqrt y\) in both parts, keeping the actual
calibrated payer from the gap score \(\mathcal R_{\rm gap}\).
Use \([u]_+=\max(u,0)\).

**Theorem.** Fix the odd payer rank \(m\ge3\) in the direct identity.
There are \(C>0\) absolute, \(c>0\) depending only on \(J_0\), and an
absolute \(\epsilon_0>0\) with the following property. Fix
\(0<\epsilon<\min(\epsilon_0,.04/m)\), then let \(x\to\infty\).
Uniformly in the even target, all the quantities below use only
actual true-prime opposite legs.
1. The complete negative debit of the squarefree \(z\)-rough
exactly-two-small class satisfies
\[
 \sum_{\substack{y\in J,\ P\ {\rm prime}\\y\ {\rm squarefree},\
                    P^-(y)>z,\ k(y)=2}}
      \log P\,[-\mathcal R_0(y)]_+
       \le \frac C\epsilon\, x\mathfrak S(N).                    \tag{1}
\]
There is no restriction on the number or the parity of the other
prime factors of \(y\).
2. An explicit squarefree class \(\mathcal U\) with no small
prime factors satisfies
\[
    \sum_{\substack{y\in\mathcal U\\P\ {\rm prime}}}
       \log P\,\mathcal R_0(y)
       \ge \frac c{\epsilon^2} x\mathfrak S(N).                 \tag{2}
\]
It is physically disjoint from (1).
3. On both classes the same conclusions hold for the actual gap score
with additive \(o_{\epsilon,m,J_0}(x\mathfrak S(N))\) errors, and so,
for any sufficiently small fixed \(\epsilon\), the direct identity
implies
\[
 {\cal G}_J(N)\ \ge\
     \frac{c}{2\epsilon^2}x\mathfrak S(N)
   + \sum_{\substack{y\in J,\ P\ {\rm prime}\\
          y\ {\rm squarefree},\ P^-(y)>z,\ \omega(y)\ge5,\ k(y)\ge3}}
          \log P\,\mathcal R_{\rm gap}(y)
   +o_{\epsilon,m,J_0}(x\mathfrak S(N)).                        \tag{3}
\]
The remaining sum includes the **full** original calibration payer.
The theorem does not supply its lower bound. Indeed the ordinary
two-form upper sieve gives
\({\cal G}_J(N)\ll x\mathfrak S(N)\) with an absolute constant.
Consequently this residual must supply a genuinely negative amount
at least of order \(\epsilon^{-2}x\mathfrak S(N)\) as the fixed
\(\epsilon\) is chosen small. The protected reservoir is not a net
Goldbach gain by itself.

## 1. The exactly-two-small upper

Set \(R=\sqrt y\). For \(y=pqM\) with the actual small primes \(p<q\),
the hyperbolic score plus its pair-completion term sums over *all*
subproducts \(c\mid pq\) with coefficients \(\mu_2(c)\), since the
missing \(c=pq\) is restored if \(pq\ge C_y\); the \(m\)-factor payer
does not occur. With \(d\mid M\), \(b=M/d\), and \(u\mid pq\),
group the raw and free contributions according to their common
large divisor \(du>R\). Their combined coefficient at this divisor is
\[
 \mu(u)\{(1+\mu(d))\log b+(\mu(d)-1)\log(pq/u)\}.               \tag{4}
\]
Indeed the raw contribution at \(du\) is
\(\mu(d)\mu(u)\log(bpq/u)\). For the free contribution,
sum \(\mu_2(c)\log(bpq/(uc))\) over \(c\mid pq/u\).
On this squarefree product use \(\mu_2(c)=(-2)^{\omega(c)}\).
The constant coefficient sums to \(\mu(pq/u)=\mu(u)\);
for each prime \(t\mid pq/u\), the coefficient of \(\log t\)
is \(\sum_{c\mid(pq/u)/t}\mu_2(c)=-\mu(u)\).
This yields (4), including \(u=1\).
If \(d>R\) all four \(u\)'s are present and the total is zero
by the two elementary alternating-subset identities.

For additional detail, when \(d\le R/p\) the admitted set is
empty, \(\{pq\}\) or \(\{q,pq\}\). For \(\mu(d)=+1\) these
give nonnegative totals; for \(\mu(d)=-1\) the last set has
positive total \(2\log p\) and the other two give zero. When
\(R/p<d\le R\), the admitted set is \(\{p,q,pq\}\).
For \(\mu(d)=-1\) its total is \(2\log(pq)\); for
\(\mu(d)=+1\) it is \(-2\log b\).
This proves the upper majorization
\[
                  [-\mathcal R_0(y)]_+
 \le  \sum_{\substack{d\mid M\\\sqrt y/p<d\le\sqrt y}}
                       2\log(M/d).                             \tag{5}
\]
(The raw-and-free decomposition uses only squarefree \(y\).)
The majorization does not need the complementary pairing between
even macro ranks, and also covers odd macro parity.

Remove the opposite primes dividing \(N\); their contribution
is \(O(x^{o(1)})\), because
there are \(O(1)\) such \(P\in[x/2,x]\) and every score and
majorant is bounded by \(L^{O(1)}\tau(y)^{O(1)}\). All remaining
\(y,p,q,d,b\) are units modulo \(N\).

Put \(w=x^\epsilon/2\). Both \(d,b\) in (5) have all prime
factors \(>w\), since they are composed of the other actual
primes, which are \(\ge C_y\ge x^\epsilon\). Fix \(p,q,d\) and
put \(H=pqd\). Relax \(y\in J\) to \(x\le Hb\le1.5x\).
This interval for \(b\) has length \(Y=x/(2H)\gg x^{.49}\)
for \(\epsilon_0<.004\), since \(p,q<1.5x^\epsilon\) and
\(d\le\sqrt{1.5x}\). We use the uniform upper
\[
 \#\{b\in[x/H,1.5x/H]:P^-(b)>w,\ N-Hb\ {\rm prime}\}
       \ll Y\,\frac{\mathfrak S(N)}{\epsilon L^2}.              \tag{6}
\]
Here is a disjoint-bank derivation with uniform constants.
In the first prime bank \(r\le w\) sieve **both** \(b\) and
\(N-Hb\), with a dimension-two upper beta sieve of level
\(x^{.07}\). Its number of forbidden residues is two
unless \(r\mid NH\), when it is one (including \(r=2\)).
The second bank \(w<r\le x^{.04}\) sieves only \(N-Hb\),
with the linear upper sieve of level \(x^{.16}\).
It has one root at all \(r\nmid H\), zero when \(r\mid H\).
Either individual upper-sieve polynomial is pointwise a
nonnegative majorant for its bank's sifted indicator; hence
their product majorizes the true simultaneous sifted indicator.
Because the banks are disjoint, multiplicativity by the CRT
gives the product of the corresponding two main expectations
against uniform residues, before summing over \(b\).
Both dimension conditions are bounded uniformly, since the
numbers of roots are at most two and one, respectively, and
the root at 2 is single. The dimension-two parameter
\(\log(x^{.07})/\log w\) tends to \(.07/\epsilon\) at fixed
\(\epsilon\), so take \(\epsilon_0\) small enough that the
upper factor is bounded by an absolute constant. The second
parameter is 4. The standard bounded beta-sieve coefficients
and the CRT floor errors give a total error
\[
 \ll\sum_{u\le x^{.07}}2^{\omega(u)}\sum_{v\le x^{.16}}1
          \ll x^{.23}L^{O(1)} .
\]
This is negligible versus the upper in (6).
In the first bank, the local product is
\(\ll \mathfrak S(N)V(w)^2\) with
\(V(t)=\prod_{r\le t}(1-1/r)\).
Without the divisors of \(H\), its ratio to \(V(w)^2\)
is the truncated singular factor at \(N\); extension to the
full factor changes it by \(1+O(L/w)\).
Omission or collision of roots caused by \(r\mid H\) changes
the two bank products by at most \(\prod_{r\mid H}(1+O(1/r))
=1+O(L/z)\): all factors of \(H\) exceed \(z\).
The second bank product is therefore
\(\ll V(x^{.04})/V(w)\ll\epsilon\).
Together \(V(w)^2\ll(\epsilon L)^{-2}\).
Finally the actual opposite prime is \(\ge x/2\), so is not
a discarded sieve prime. This proves (6).

Multiply (6) by the two logarithmic factors \(O(L^2)\)
from \(\log P\) and (5). The \(d\)'s satisfy
\(\sqrt x/p<d\le\sqrt{1.5x}\). Uniformly on this range,
ordinary one-dimensional upper sieving gives
\(\#\{D<d\le2D:P^-(d)>w\}\ll D/(\epsilon L)\):
here \(D\gg x^{.49}\), and one can use level \(x^{.10}\)
and ordinary floor remainders. Summing these dyads,
\[
   \sum_{\substack{\sqrt x/p<d\le\sqrt{1.5x}\\P^-(d)>w}}\frac1d
            \ll\frac{\log p+1}{\epsilon L}.
\]
The prime sum
\(\sum_{z<p<q\le1.5x^\epsilon}(\log p+1)/(pq)\ll\epsilon L\)
follows by \(\sum_{p<q}(\log p+1)/p\ll\log q\) and
\(\sum_{q\le U}\log q/q\ll\log U\).
The resulting upper is \(O(x\mathfrak S(N)/\epsilon)\),
with absolute constant. This proves (1).

## 2. The enlarged true positive reserve

Fix \(\beta=.001,\ \nu=.010\), and take
\(\epsilon_0<\beta/8\). Choose a true prime marker
\(r\in(x^{.011},x^{.012})\), a unit at \(N\).
Independently choose a squarefree \(B>1\) with
\(B\le x^\nu\) composed entirely of true primes in the
bank \((2x^\epsilon,x^\beta]\) not dividing \(N\).
Put \(h=rB\le x^{.022}\).
Let \(\mathcal U\) consist of \(y=ha\in J\) with
\(a\) squarefree and \(x^{.21}\)-rough.
The factorization \(y=rBa\) is unique:
\(r\) and every prime dividing \(B\) lie in their respective
disjoint banks below \(x^{.21}\), and \(a\) has no factor in
either bank. Hence both the labels and their multiplicities
are determined by the physical row \(y\).
All primes of \(y\) exceed \(C_y\), since
\(C_y\le1.5x^\epsilon<2x^\epsilon\); none is small.

For each \(h\), apply the lower linear sieve with level
\(D=x^{.46}\) to \(a=(N-P)/h\) against the true prime
sequence \(P=N-y,\ y\in J,\ P\equiv N\bmod h\), weighted
by \(\log P\). The exact modulus upon opening \(d\mid a\)
is \(hd\), including prime squares if \(d\) and \(h\)
share a prime. The local multiplicative density is
\[
 g_h(t)=
 \begin{cases}
    0,&t\mid N,\\
    1/t,&t\mid h,\\
    1/(t-1),&t\nmid Nh .
 \end{cases}
\]
Rows with \(P\mid N\) can be omitted at the negligible cost
discussed above. The dimension upper condition holds uniformly
since \(g_h(t)\le1/(t-1)\) for \(t\ge3\) and \(g_h(2)=0\).
The local product at \(x^{.21}\) is
\(\asymp\mathfrak S(N)/L\) uniformly: versus \(V_N(x^{.21})\)
the primes dividing \(h\) change it by
\(\prod_{t\mid h}(1+O(t^{-2}))=1+o_\epsilon(1)\).
The lower sieve factor is strictly positive at
\(.46/.21>2\), with an absolute lower margin.

Multiply each lower sieve inequality by \(2^{\omega(B)}\)
and sum over the actual labels. For each modulus \(M_0=hd\),
the number of reconstructions and the total weight of those
reconstructions are bounded by a fixed power of
\(\tau(M_0)\): \(h\mid M_0\) and for each \(h\), the
two banks recover \(r,B\) uniquely, while
\(2^{\omega(B)}\le\tau(h)\).
Ordinary BV applies because \(hd\le x^{.482}\).
The fixed divisor weights are harmless by Cauchy-Schwarz:
use BV with arbitrarily large log reserve for the unweighted
first error factor, and use the trivial maximal-prefix
discrepancy \(E(M_0)\ll xL/M_0\) with
\(\sum_{M_0\le x^{.482}}\tau(M_0)^{O(1)}/M_0
\ll L^{O(1)}\) for the second.
This gives, before the squarefree restriction on \(a\),
\[
   \sum_{r,B}2^{\omega(B)}
      \sum_{\substack{y=rBa\in J,\ P\ {\rm prime}\\
                       P^-(a)>x^{.21}}}\log P
       \ \gg_{J_0}\ \frac{x\mathfrak S(N)}{L}
                   \sum_r\frac1{\varphi(r)}
                   \sum_B\frac{2^{\omega(B)}}{\varphi(B)}
                        -O_A(xL^{-A}).                         \tag{7}
\]
The repeated-factor loss in \(a\) is bounded even dropping the
opposite primality: using \(a\le1.5x/h\), for each
prime \(s>x^{.21}\) the floor count is at most
\(1.5x/(hs^2)\). Thus the lost weight is at most
\(O(xL\sum_{r,B}2^{\omega(B)}/(rB)\sum_{s>x^{.21}}s^{-2})\).
It is negligible for fixed \(\epsilon\). Also \(a>1\) and
\(\omega(a)\le4\) because \(5\cdot.21>1\).

For \(y\in\mathcal U\), the hyperbola cofactor only has \(c=1\)
and pair/payer terms vanish, so
\[
 \mathcal R_0(y)
   =2\!\!\sum_{\substack{d\mid y,\ d>\sqrt y\\
                         \omega(d)\ {\rm even}}}\log(y/d).
\]
If \(\omega(a)=2\) or 4, choose \(a\) itself as an even base
divisor and adjoin any even subset of the prime factors of \(B\).
If \(\omega(a)=3\), take its largest two primes as the even base
divisor and again adjoin any even subset of \(B\).
Their product is at least \(a^{2/3}>\sqrt y\) since
\(a\gg x^{.978}\). If \(\omega(a)=1\), choose \(a\)
as the odd base, and adjoin any odd subset of \(B\).
In all cases the base divisor exceeds \(\sqrt y\), every
resulting divisor is distinct and even, and its complement
contains \(r\).
Since \(B>1\) there are exactly \(2^{\omega(B)-1}\) choices
of the stipulated parity, so
\[
                \mathcal R_0(y)\ge2^{\omega(B)}\log r
                          \ge .011 L\,2^{\omega(B)}.            \tag{8}
\]
Thus the weight in (7) is precisely available in the actual
score, rather than extra label multiplicity.

The unrestricted \(2^{\omega(B)}/B\) mass is
\(M_\epsilon=\prod_{2x^\epsilon<p\le x^\beta,\ p\nmid N}(1+2/p)\).
For fixed \(\epsilon\), Mertens gives
\(M_\epsilon=(1+o(1))(\beta/\epsilon)^2\), uniformly in \(N\):
the target-prime deletion changes the product by
\(1+O(L/x^\epsilon)\).
In its positive product law the mean of \(\log B/L\) is
\[
             \sum_{p} \frac{2}{p+2}\frac{\log p}{L}
                  \le3\beta
\]
for all sufficiently large \(x\), by the prime harmonic log
estimate. Markov loses at most \(3\beta/\nu=.3\) at
\(B>x^\nu\); omitting \(B=1\) costs 1.
For \(\epsilon<\beta/8\) the remaining mass is
\(\gg (\beta/\epsilon)^2\) with an absolute implied constant.
Also \(\sum_r1/\varphi(r)\) has a uniform positive lower
limit, since \(\log(.012/.011)>0\) and unit-prime removals
are negligible. Equations (7) and (8) prove (2) with
\(c\) independent of \(\epsilon\).

## 3. The exact remaining signed gate

In (1), the number of nonsmall factors is \(\le 2/\epsilon\)
for large \(x\) because each is at least \(x^\epsilon\).
In (2), the full rank is at most \(5+\nu/\epsilon\).
Hence the direct gap-to-own-square-root transfer for
every fixed rank applies on both actual classes, as well
as on all remaining \(k(y)\le1\) and \(\omega(y)\le4\) classes.
This uses a fixed \(\epsilon\) first, not a uniform
\(\epsilon\to0\) estimate with \(x\).
Dropping rough nonsquarefree \(y\) incurs only
\(O(xL^{O(1)}z^{-1/2})\) absolute error via Cauchy-Schwarz and a fixed
divisor moment, since their count is \(O(x/z)\).
All remaining low ranks or at-most-one-small cases are
nonnegative at their own square-root score.
Choose \(\epsilon\) small enough that the lower (2) beats
(1) by at least \(c/(2\epsilon^2)\).
Now insert the exact direct-gap identity; this proves (3).
No truncation of the high-rank gap is used.

For clarity, the payer may be moved out of the unknown only
with a compensating **actual** term. Write
\(\mathcal R_{\rm gap}=\mathcal B_{\rm gap}+A_+-A_-\),
where \(\mathcal B_{\rm gap}\) is the same raw and
\(c<C_y\) hyperbolic score, \(A_+\) is the missing-pair
completion, and \(A_-\) includes the exact coefficient
\(2^m\lambda_+(y)\) of the genuine odd \(m\)-label payer.
The direct calibration proves the total true-prime mean of
\(A_+-A_-\) is \(O_A(xL^{-A})\) for every fixed \(A\).
On squarefree rows it vanishes at \(k(y)\le1\) and equals
\(A_+\ge0\) at \(k(y)=2\). Consequently, at the same actual
fixed \(N\), with all displayed sums restricted to squarefree,
\(z\)-rough rows and true opposite primes,
\[
 \sum_{k(y)\ge3}\log P\,\mathcal R_{\rm gap}(y)
 =
 \sum_{k(y)\ge3}\log P\,\mathcal B_{\rm gap}(y)
 -
 \sum_{k(y)=2}\log P\,A_+(y)
 +O_A(xL^{-A}).                                                \tag{9}
\]
The squareful loss above is also smaller than every log
power. To apply (9) to precisely the residual of (3), remove
the actual rank-\(\le4\) portion from the left and correspondingly
from the right. Thus replacing the payer alone by a negligible
term is not justified. Neither (3) nor (9) resolves the
remaining many-small comparison at the natural Goldbach scale.

## Comparison with other approaches

The [November 2026 restricted Chen sieve preprint](https://www.preprints.org/manuscript/202611.0694/v1) uses parity-weighted cofactor minorants and factorable support tests, and retains an almost-all conclusion for its weighted construction. The [October 2026 signed-contamination reduction](https://www.preprints.org/manuscript/202610.0809) leaves a local signed Liouville bound together with a contamination estimate as hypotheses. Neither reformulation is the two-family true-prime comparison above. In this note the exactly-two-small negative contribution is controlled unconditionally, while a different, explicit many-small signed comparison remains open at each prescribed target.

The [leading-cancellation follow-up](../direct_many_small_renormalization/Proof.md) gives the explicit negative main of the actual many-small sum and an all-small-cofactor recentering with a known change of mean. Its remaining error is not small enough to establish positivity at the Goldbach scale.

A [fixed-rank further restriction](../direct_fixed_rank_smallest/Proof.md) pays the complete negative contribution up to any previously selected finite rank by choosing the odd payer rank higher and the small-factor exponent sufficiently small. It leaves the full higher-rank payer and signed comparison open.
