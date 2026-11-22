# Deleting the opposite short divisor after the giant-prime switch

Use the notation of [the reverse giant Type I deletion](ReverseTypeI.md):
\(N\) is prescribed and even, \(L=\log N\),
\(S=\exp((\log L)^4)\), \(B=N/S\), \(J\subset J_0\Subset(0,1)\),
\(T_y=y/B\), and \(Q_y(m)=\sum_{d\mid m,d<T_y}\mu(d)\). Keep the same
\(C_I\) and \(Q=\sqrt N/L^{D}\) as in that result. Fix \(\varepsilon>0\)
and restrict the actual giant interval to
\(I\subset [N^{1/2+\varepsilon},B]\). All estimates below are uniform
in these literal intervals and in the even target.

**Theorem.** For every fixed \(A>0\), take \(D=D(A)\) from the first
switch and choose another fixed \(D_1=D_1(A,\varepsilon)\). For
\(X=N/(mk)\) write
\[
 H=\exp((\log L)^3),\qquad Z(X)=\frac{\sqrt{X/H}}{L^{D_1}}.
\]
Then
\[
\begin{split}
 C_I={}& \sum_{\substack{b j+a m k=N,\ b j\in NJ\\
          (a m k,N)=1,\ a k\in I,\ a m>Q\\ b>Z(N/(mk))}}
     \mu(a)\mu(b)\,(\log j)(\log k)\,Q_{a m k}(m)\\
       &\qquad+O_{A,\varepsilon,J_0}(NL^{-A}).                       \tag{1}
\end{split}
\]
The tuple is of positive integers. In particular both original prime
slots have been turned into literal signed sums, and no ordinary
prime or Möbius distribution is assumed for the retained \(b\)'s. The
statement is not a bound for the double signed remainder in (1).
There is no small-radical restriction on \(N\).

This is related to [the reverse Vaughan double residual](../ReverseVaughanDoubleResidual.md),
which starts from a separately tagged semiprime source. Here the two
short deletions are for the original untagged giant divisor term, the
second uses a cutoff at the actual Möbius length \(X=N/(mk)\), and its
only distribution input is classical Möbius BV.

## 1. Classical BV with the actual target-unit mask

For \(N^{\varepsilon/2}\le X\le N\), we need the uniform estimate
\[
 \sum_{\substack{b\le Z(X)\\(b,N)=1}}
 \max_{(c,b)=1}\max_{t\le X}
 \left|\sum_{\substack{a\le t,\ a\equiv c\pmod b\\(a,N)=1}}
          \mu(a)\right|\ll_{A,\varepsilon}X L^{-A}.                  \tag{2}
\]
Use the exact convolution
\[
 \mu(a)1_{(a,N)=1}=\sum_{h\mid a,\ \operatorname{rad}(h)\mid N}\mu(a/h),
\]
where the condition on \(h\) means that **every** prime factor of \(h\)
divides \(N\), and includes \(h=1\). At \(b\) in (2) every \(h\) is a
unit modulo \(b\), so the congruence for \(a/h\) is the actual reduced
class \(c\overline h\pmod b\).
For \(h\le H\) use [Siebert–Wolke’s Möbius BV, Corollary 1](https://link.springer.com/article/10.1007/BF01110168), in the maximal-prefix formulation of [Murty–Vatwani, Proposition 3](https://www.mathjournals.org/jrms/2018-033-002/2018-033-002-001.html)
at length \(X/h\). The modulus bound is within its square-root log
reserve if \(D_1\) is large enough, uniformly since \(\log(X/H)\gg_
\varepsilon L\). The reciprocal sum of \(h\)'s is at most
\(\prod_{q\mid N}(1-1/q)^{-1}\ll\ell^{O(1)}\), where \(\ell=\log L\).

For large \(h>H\) sum the trivial progression bound \(X/(h b)+1\)
over \(b\le Z(X)\), uniformly in both maxima. The reciprocal harmonic
in \(b\) is \(O(L)\). At \(\sigma=1-1/(10\ell)\) the positive target
Euler product \(\prod_{q\mid N}(1-q^{-\sigma})^{-1}\) is
\(\ell^{O(1)}\), as in the first switch. Thus the large-\(h\)
reciprocal harmonic is \(\ll H^{-(1-\sigma)}\ell^{O(1)}\), smaller
than every log power. For the floors, a separate Rankin estimate at
\(1/10\) gives
\[
 \#\{h\le X:\text{every prime factor of }h\text{ divides }N\}
 \le X^{1/10}\exp(O(L^{9/10})).
\]
Indeed split the target primes at \(L\), using
\(\sum_{q\le L}q^{-1/10}\ll L^{9/10}\) and at most \(O(L)\) primes
above it. Multiplying the count by \(Z(X)\le\sqrt X\) is power-small
relative to \(X\) for the stated polynomial range. This pays the sum
of all literal floors and proves (2). No restricted-to-units Möbius
estimate is assumed for a modulus sharing a prime with \(N\).

## 2. Applying (2) at the true residual length

Start from the right side of the first reverse switch. The target
unit condition can be retained as \((a m k,N)=1\): it holds on all
original central primes except \(p\mid N\), which cost \(N^{o(1)}\).
Replace the true opposite \(p\) by \(\Lambda(P)\) for all \(P\in NJ\)
with this mask, at cost \(N^{1/2+o(1)}\) from proper powers. The
absolute tuple weight attached to each \(y=N-P\) is at most
\(L^{O(1)}\tau(y)^{O(1)}\), which pays that replacement. Expand the
literal identity \(\Lambda(P)=\sum_{b j=P}\mu(b)\log j\).

For fixed \(m,k\), set \(X=N/(mk)\). Every retained \(a\) is of size
\(X\) up to the fixed central ratios and satisfies
\[
 a>Q/m\gg N^{\varepsilon}/L^D,
 \qquad m=y/(ak)\le N^{1/2-\varepsilon}.
\]
Hence \(X\ge N^{\varepsilon/2}\) for all sufficiently large \(N\);
smaller \(X\)'s support no row. The condition \(b\mid P\) gives
\(a\equiv N\overline{mk}\pmod b\). The inverse exists: \((b,N)=1\)
since \(b\mid P\), and any common prime of \(b,mk\) would divide
\(N\); discard those \(b\)'s before forming the congruence. Its
right side is a unit. The extra mask is precisely \((a,N)=1\).

Open \(Q_{a m k}(m)\) at each literal \(d\mid m\). Its condition is
\(a>Bd/(mk)\), an additional lower endpoint. The real central
interval, \(ak\in I\), and \(am>Q\) give only more interval endpoints
in \(a\). The weight
\(\log j=\log((N-a m k)/b)\) has supremum and total variation \(O(L)\)
there, so (2), by partial summation, removes the full sum over
\(b\le Z(X)\) at \(O_{A'}(X L^{-A'})\) for each \(d\). This does not
replace either log by a constant. Restore all \(d,m,k\) with the
absolute harmonic cost
\[
 \sum_{m,k\le N}\frac{\tau(m)\log k}{mk}\ll L^4.
\]
Choosing the input log reserves first proves (1). The actual remaining
constraints \(am>Q\) and \(b>Z(N/(mk))\) are simultaneous, and neither
is relaxed to a statistical parity model.
