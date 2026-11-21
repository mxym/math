# A strictly positive subscale reservoir for the fixed-target smooth midpoint detector

Use the notation of the [midpoint theorem](../midpoint/Proof.md) and its
[actual positive-profile mover](../midpoint_mover/Proof.md). Thus \(I=[P/3,2P/3]\),
\(X=P/3,\ L=\log P,\ r=P-n,\ \langle A,B\rangle=\sum_{n\in I}A(n)B(r)\).
For a sufficiently large even target \(P\), \(V(n)=1_{n\ {\rm prime}}\log n\),
\(G=\langle V,V\rangle,\ {\cal F}(H)=\langle V,H\rangle-\langle H,H\rangle\),
and \(2J=V-U\) uses the smooth complementary-divisor cutoff \(f\) in the
midpoint theorem. The singular series is \(S=S(P)\gg1\).

There exist a **fixed** admissible \(f\), a number \(u<1/12\), and an
explicit nonnegative subweight \(T_P\le J_+1_{P^-\le P^u}\), for which
\[
 \begin{split}
 G/4&={\cal F}(J-T_P)+\langle T_P,T_P\rangle+O_{A,f}(PL^{-A})
                       &&\text{for every fixed }A,\\
 \langle T_P,T_P\rangle&\gg_f XS\,\frac{\log L}{L^3}.             \tag{1}
 \end{split}
\]
In particular this reservoir strictly exceeds the proven transfer error.
The pairs used to prove the lower bound have a genuine **squarefree
triprime** on one side and a **squareful** positive composite on the
other. This does *not* prove a positive reservoir of that size after
discarding all nonsquarefree composites, nor \({\cal F}(J-T_P)\ge0\).
Relative to \(XS\), the guaranteed reservoir goes to zero.

## 1. Two real positive templates

Fix \(\eta=.001\). Choose \(e>0\) sufficiently small, \(e<.00001\),
so the one-dimensional fundamental lemma below at \(s=\eta/(3e)\)
has relative error \(<1/2\); all parameters are then fixed. Use exponent
windows, in base \(P\),
\[
 {\cal L}=[.01e,.02e],\quad
 {\cal Q}=[1/2-.80e,\,1/2-.70e],\quad z=P^{3e}.
\]
As usual a prime in one of these windows means its \(\log_P\) belongs
to that interval. Choose the smooth midpoint \(f\) with transition on
\([.5-e,.5+e]\) so that on \(D=[.5-.82e,.5-.64e]\) we have
\(-f', f'',-f'''\ge c_f>0\). For instance take a nonnegative
smooth bump supported in the open lower half of the transition, equal
to \(\exp(-(x-.5)/e)\) on \(D\) (multiply by a plateau bump), add its
reflection about .5, and integrate this normalized even density from
\(x\) to infinity. This gives a complementary nonincreasing \(f\)
which is then extended compactly at the negative end as before.

Let \({\cal B}=\{b:\ b\text{ prime},\,4L<b\le 8L,\ b\nmid P\}\).
The first template consists of \(n=\ell q h\in I\) with
\(\ell\in{\cal L}, q\in{\cal Q}\) prime, and \(h\) prime. All the roles
are distinct and determined by size for large \(P\):
\(h=P^{1-\log_P q-\log_P\ell+O(1/L)}\) lies strictly above \(P^{1/2}\).
Impose \((n,P)=1\).
Use normalized coordinates \(x=\log_n q,\ y=\log_n\ell\). On these inputs
the exact triprime formula gives
\[
 J(n)/\log n=f(x)-f(x+y)\gg_f y\gg_f 1.
\]
Indeed \(f(y)=1\) and \(f(\log_n h)=1-f(x+y)\). The small fixed factor
in the last bound is allowed to depend on \(e\).

The second template consists of \(r=b^2\ell' q' k\in I\) with
\(b\in{\cal B}\), primes \(\ell'\in{\cal L}, q'\in{\cal Q}\),
\(P^-(k)>z\), \(q'\nmid k\), and \((r,P)=1\).
The first two factors \(b,\ell'\) are unique by roughness. The prime
\(q'\) is unique too: \(k>P^{1/2}\) eventually, whereas if \(k\)
contained another prime \(q''\in{\cal Q}\) then \(1<k/q''<z\).
Write \(x=\log_r q', w=\log_r b,y=\log_r\ell'\) and
\[
 B(t)=f(t)-f(t+w)-f(t+y)+f(t+w+y).
\]
The intervals from \(x\) to \(x+2w+y\) lie in \(D\) for large \(P\).
Every divisor involving \(q'\) and a nontrivial divisor of \(k\)
is above the upper transition. A divisor involving no \(q'\), a
proper divisor of \(k\), and any squarefree subset of the two small
primes has normalized log below the lower transition: a proper divisor
of \(k\) is \(\le k/z\) and \(w=o(1),\,y\le .021e\).
The sum over the two small divisibility bits in this last case cancels.
The two remaining cases \(q'\) alone or \(k\) alone, each times these
small bits, therefore give exactly
\[
 U(r)/\log r=-B(x)-\mu(k)B(x+w).                                  \tag{2}
\]
For the \(k\) term use \(\log_r k=1-x-2w-y\), complement symmetry,
and reverse the two small bits; its second difference is \(-B(x+w)\).
If \(k\) is nonsquarefree its full-divisor term is zero and the same
formula holds. The positive mixed difference \(B(t)\) integrates
\(f''(t+i+j)\) on \(0\le i\le w,\,0\le j\le y\). Hence
\(B(x+w)>0,\ B(x)-B(x+w)\ge c_f w^2 y\) by the third derivative.
Thus \(J(r)\gg_f(\log b)^2/L\) for **every** allowed cofactor, without
knowing its Möbius sign.

For a sufficiently small fixed \(c>0\) take \(T_P=cL\) on the first
template and \(T_P=c(\log b)^2/L\) on the second, zero elsewhere.
The templates are disjoint; these are literal nonnegative subweights
of the actual \(J\). They lie in \(P^-\le P^{.082}\). The constants
can for instance be taken below one tenth of the derivative bounds
above times the lower endpoint of \({\cal L}\).

## 2. Arbitrary-log midpoint precision

We need a more accurate error than \(o(XS)\) for this subscale statement.
For all \(n\in I\) Taylor-expand \(a f(v/a)\) at \(a=1\), with
\(a=1+\log(n/P)/L,\ v=(\log d)/L\). For each fixed integer \(K\) this gives
\[
 U(n)= L\sum_{j=0}^{K} L^{-j}\log^j(n/P)
        \sum_{d\mid n}\mu(d)f_j(\log_P d)+O_{K,f}(L^{-K}\tau(n)),
 \qquad f_j(v)=\frac1{j!}\partial_a^j[af(v/a)]_{a=1}.              \tag{3}
\]
The remainder is uniform on these physical divisors by compact
smoothness on a fixed neighborhood. Every \(f_j\) is flat on
\([0,.5-e]\), vanishes on \([.5+e,\infty)\), and is smooth (the
constant at the lower plateau need not be 1). Its derivative there
is zero. Mixed physical remainders cost at most \(O_{K,f}(PL^{4-K})\)
by the second divisor moment and the trivial pointwise
\(|U(n)|\ll L\tau(n)\), \(0\le T_P\ll L\). Choose \(K>A+10\).

First apply (3) on both sides of \(\langle U,U\rangle\). In each of
the finitely many fixed terms the weight
\(\log^j(n/P)\log^{j'}(1-n/P)\) is smooth on the central interval.
Multiply it by the same smoothed central cutoff as in the [gcd-split
Poisson argument](../midpoint/Proof.md) §3. The resulting compact
test still has fixed-log derivative bounds and bounded total
variation; restoring endpoints globally costs any prescribed log saving
before the gcd split. For the large \((d,d')\mid P\) part the earlier
power saving is unchanged. For the small gcd \(g\), Poisson is applied
at \(P/g\), with \(n/P=(n/g)/(P/g)\) and precisely this smooth coupled
weight. The coefficients \(\mu(d)f_j(\log_P d)\) separate after fixing
the gcd and have support \(\le P^{.50001}\) before division. The uniform
[Bettin–Chandee](https://arxiv.org/pdf/1502.00769) nonzero-mode
bounds and divisor-of-target summation in that proof have the same
strict margins. The zero mode saves arbitrary logs by coprime harmonic
Mertens, since each cutoff is an integral of its derivative supported
in the transition against *large* partial sums (the sign of the
derivative is immaterial). Thus \(\langle U,U\rangle=O_{A,f}(PL^{-A})\).

For \(\langle U,T_P\rangle\), the template input \(r\) is an actual
convolution of its short prime label in \({\cal L}\) with a bounded
long sequence: the remaining factor is the prime product \(qh\), or
\(b^2q' k\) subject to the stated prime, rough and squarefreeness-of-the-label
conditions (only \(q'\nmid k\), not \(\mu^2(k)=1\), is imposed).
Long-factor multiplicities are bounded independently of \(P\). In
fact \(q\) is the unique candidate in its size window: two such
factors cannot be a first-template factorization with \(h>P^{1/2}\);
in the second template, any extra \(q''\) dividing \(k\) contradicts
roughness as above. These size conclusions hold throughout the actual
centrally contributing product boxes; impose the implied bounds
\(P^{.5+.66e}<h,k<P^{.5+.82e}\) on each long coefficient if forming it
off support. The weight \((\log b)^2/L\) depends only on the long
coefficient. Remove target primes in each factor. Split \(b\)'s if desired:
even a cost \(O(L)\) is harmless.

In (3), \(\log^j(n/P)=\log^j(1-r/P)\) is a smooth *physical* weight.
To use the [macroscopic-residue transfer](../midpoint_mover/Proof.md)
§§1–2 exactly as stated, mesh the short and long factors independently
with ratio \(1+L^{-C}\), retaining boxes wholly within the actual
central product cut. The discarded strips have \(O(PL^{-C}+1)\)
physical inputs, not this many per box. Cauchy and divisor moments
give any needed log saving after normalization by the template weight.
In each retained box approximate the smooth physical weight by its
value at the product of its lower endpoints (error \(O_{j}(L^{-C})\)).
All prime and cofactor conditions above are individual long-factor
or short-factor conditions. If a long factor were represented twice
with a different \(\ell\), central tuples are in fact unique; bounded
divisor moments would also control discarded endpoints. The number
of boxes is polylogarithmic for the fixed parameters. Their product
of lower scales \(MC\) is at least \((1-o(1))P/3\), so the Fouvry
ambient \(4MC\) exceeds the actual residue \(P\).

For this tiny prime exponent \(\log_P\ell\in[.01e,.02e]\), the
large-residue [Fouvry Corollaire 1](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf)
covers all unit moduli through \(\sqrt P\). For larger moduli we
use the macroscopic large-residue [Fouvry–Radziwill prime-short-weight
variant](../PanPolynomiallyRoughSurvivors.md) §C, as audited in the mover:
it covers through \(P^{.502}\) here since
\(36(.02e)+33(.502)<17,\ 15(.02e+.502)<8\), and the short prime
still has fixed positive exponent and the required Siegel–Walfisz
property. This works for every bounded signed modulus weight, with
arbitrary additional log savings. The condition \(r\) unit to \(P\)
permits restricting the divisor moduli of \(n\) to \((d,P)=1\).
Apply the transfer for each \(f_j\) in (3). Its main term has the
inner coprime sum \(\sum_{(d,Pr)=1}\mu(d)f_j(\log_P d)/\phi(d)\),
\(O_{B,f,j}(L^{-B})\) for each fixed \(B\), by the
uniform Euler-product argument in the mover. The upper weight on
the remaining input is \(O_f(L)\). This proves
\(\langle U,T_P\rangle=O_{A,f}(PL^{-A})\), without appealing to a
limiting roughness error. The exact identities in the two earlier
notes now give the first equality of (1).

## 3. Positive count of *mixed* template pairs

Let \(a(n)\) be the unweighted first-template indicator. We have
\(A_0=\sum_{n\in I}a(n)\gg_e X/L\): for each eligible \(\ell,q\),
count primes \(h\) in \([P/(3\ell q),2P/(3\ell q)]\) by the PNT.
Its endpoints have fixed power sizes, the label roles are unique,
and both harmonic sums over the fixed exponent windows are bounded
below by positive constants. Removing triples sharing a prime with
\(P\) is negligible, since all three primes exceed \(P^{.01e}\).
For any modulus \(M\le P^{.502}\),
\(\sum a(n)1_{(n,M)=1}=A_0+O_e(P^{1-.01e}L)\), by the same
physical count of multiples of a prime of \(M\) in this size range.
The previous fine boxes and the same Fouvry/FR bounds give for
**any bounded coefficient** on \((M,P)=1,\ M\le P^{.502}\) an
arbitrary-log total discrepancy for \(a\) from its actual reduced
mean. Here \(a=\ell*(qh)\) with literal prime conditions.

For each \(b\in{\cal B}\), \(\ell'\in{\cal L},q'\in{\cal Q}\)
with \(m=b^2\ell' q'\) unit to \(P\), impose \(m\mid r=P-n\)
and sieve \(k=r/m\) against primes \(p\le z,\ p\nmid P\), using the
ordinary lower beta sieve of level \(D_0=P^\eta\). No \(p\mid P\)
can divide \(r\) because \(a(n)\ne0\) implies \((n,P)=1\).
The weights \(\lambda_d^-(m)\), supported on squarefree
\(d\le D_0,\ p\mid d\Rightarrow p\le z,\ p\nmid P\), are 1-bounded.
A sieve constraint \(d\mid k\) is \(md\mid r\), also for \(p\mid m\).
The exceptional \(q'\mid k\) costs \(O(P^{.5+.81e}L)\) even if one
drops the left primality: \(q'^2\mid r\), summation of \(P/q'^2+1\)
over \(q'\), with bounded choices of the polynomial \(\ell'\) factors
and of \(b\) when combined with the other masks (or crudely use
\(P^{o(1)}\)). This is a power saving.

After summing \(\ell',q',d\) for **fixed \(b\)**, the coefficient at
\(M=md\) is bounded in terms of \(e\): \(M\le P^{.502}\) for large
\(P\), hence it has at most one prime in the \(q'\) window, at most
\(O(1/e)\) distinct primes in the \(\ell'\) window, and once these
are specified \(d=M/m\) is unique. This applies regardless of the
sieve signs, any \(m\)-dependence, or overlaps of \(d\) with \(\ell'\).
Thus the complete signed discrepancy after this lower sieve is
\(O_{B,e}(PL^{-B})\) even after the \(O(L)\) different \(b\)'s.
Replacing the reduced numerator at each \(M\) by \(A_0\) costs a
power saving in total: the coefficients just bounded cost \(O_e(L)\)
over all \(b\), and \(\sum_{M\le P^{.502}}1/\phi(M)\ll L^{O(1)}\).

For a fixed \(m\) the remaining arithmetic main is
\[
 {A_0\over\phi(m)}\sum_d\lambda_d^-(m)\,g_m(d),\qquad
 g_m(p)=
 \begin{cases}
 0 &p\mid P,\\
 1/p &p\mid m,\\
 1/(p-1)&p\nmid mP .
 \end{cases}
\]
Indeed \(g_m(d)=\phi(m)/\phi(md)\) on the unit sieve support. In
particular \(p=2\) is excluded, since \(P\) is even. This dimension-one
sieve is uniform in \(m,P\): interval reciprocal products are bounded
by the complete odd-prime ones for \(1/(p-1)\). Its sifting product
is \(\gg S(P)/\log z\) uniformly. This follows from Mertens and
the standard twin-prime Euler product for \(p\nmid P\); primes \(p\mid m\)
only increase it, and omitting \(p\mid P\) with \(p>z\) from the
finite singular-factor product costs \(1+o_e(1)\).
The [fundamental lemma, e.g. Theorem 2.2 here](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/superscars-for-arithmetic-point-scatters-ii/3CCB969E058792C1803466AE0EF29136)
therefore makes the lower sum \(\gg S(P)/L\) at our choice of fixed \(e\).
There is no relative-error assertion about unsieved primes in an
individual progression.

Both \(\sum_{\ell'\in{\cal L},\,\ell'\nmid P}1/(\ell'-1)\) and the
analogous sum over \(q'\in{\cal Q}\) are bounded below by positive
constants, by PNT or Mertens on polynomial windows; target-prime losses
are power-small. This gives \(\gg_e XS(P)/(\phi(b^2)L^2)\) mixed
template pairs for each fixed \(b\), up to \(O_{B,e}(PL^{-B})\).
Labels are unique on retained actual pairs. Multiply by the genuine
product of the two positive subweights \(c^2(\log b)^2\) and sum over
\(b\). PNT on \((4L,8L]\) gives total prime log mass \((4+o(1))L\);
the primes dividing \(P\) account for at most \(L\). Hence there are
\(\gg L/\log L\) admissible primes, and
\[
 \sum_{b\in{\cal B}}\frac{(\log b)^2}{\phi(b^2)}
       \gg \frac{\log L}{L}.
\]
This proves the lower bound in (1) using only one orientation.
For targets omitting a fixed odd prime \(b_0\), augmenting the
template by that \(b_0\) instead gives \(\gg_{b_0,f} XS/L^2\).

**Why the square matters.** The extra copy of \(b\) in (2) shifts the
second difference by \(w\) while leaving the Möbius divisor bits
unchanged. Removing this repetition restores exact even-rank cancellation
and can give zero on the whole cofactor parity class. Thus this proof
cannot be read as a lower bound on pairs of two squarefree odd ranks.
The signed complementary functional in (1) could offset this entire
positive term. No positivity of the Goldbach count is concluded.

**Related work through November 21, 2026.** [Pham's October 30 v1](https://www.preprints.org/manuscript/202610.3061) gives a rough comparison and balanced rough-pair benchmarks, not the mixed-templates bound for this signed midpoint detector. [Jain's November 16 v1](https://arxiv.org/abs/2611.21136) supplies a different representation with two smooth summands, not a genuine triprime and a specifically positive squareful summand. The present lower bound is on a subscale positive term only; the complementary functional and the ordinary binary Goldbach question are not settled.
