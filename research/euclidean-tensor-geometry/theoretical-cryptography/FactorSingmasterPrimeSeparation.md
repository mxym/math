# Equal binomial shifts eventually occur only near the two opposite edges

Consider integer solutions with \(d\ge2,\ k\ge1,\ n\ge k+2d\) to
\[
                        {n\choose k}={n-d\choose k+d}.
\tag{1}
\]
Put \(u=n-k,\ N=n-d,\ s=u-2d\). The reflected index of the second binomial coefficient is \(s\), so that \(N=(n+k+s)/2\) and the right side of (1) is \({N\choose s}\).

**Theorem.** There is an absolute \(n_0\) such that every solution of (1) with \(n>n_0\) satisfies
\[
 k+2\le s,\qquad k+s<\sqrt{2n},\qquad
 s-k=\frac{k\log 2}{\log(n/k)}
                  \bigl(1+O(1/\log n)\bigr).
\tag{2}
\]
In particular there are **only finitely many** solutions with both displayed positions on the left half of Pascal's triangle, although \(d\) is not fixed. Any unbounded family must have the second position on the right half, with \(n/2-\sqrt{n/2}<d<n/2\) and
\(\liminf k/\log n\ge 2/\log 2\) along that family. In the case \(s=k+1\), the equation does not hold for **any** \(d\ge1,\ k\ge1\).

This leaves the residual reflected family with \(s-k\ge2\) open and does not settle the unrestricted Singmaster conjecture. The threshold \(n_0\) is not evaluated here. In particular, finiteness within the left half does not equate to an exhaustive list of all its finite exceptions. The \(d=1\) Lind–Singmaster family is not included in (2).

[Hugo Jenkins, §2 and §4](https://math.colgate.edu/~integers/q69/q69.pdf) gives the slope localization and treats fixed offsets, proving the finiteness for unequal fixed offsets and discussing the equal direction separately. The [previous equal-offset uniform estimate](FactorSingmasterBalancedShiftDrift.md) controls the row for a given \(d\), with an exact replay through \(d=256\). It does not alone rule out families with unbounded \(d\). The new step is to compare the abundance of large prime factors in an interval of square-root length with the smaller number that can hit both sides of (1). No claim is made about arbitrary pairs of shifts, the [global multiplicity bound](FactorSingmasterSharperProjection.md), or the [interior theorem](https://arxiv.org/abs/2106.03335).

## 1. Abundant large prime factors in a square-root interval

Set \(H=\sqrt X\), \(I=(X,X+H]\), and \(N_I(m)=\#\{t\in I\cap\mathbb Z:m\mid t\}\). For a fixed sufficiently small \(0<\epsilon<1/100\) put \(\beta=3/5-\epsilon\). [Baker–Harman, Acta Arith. 73 (1995), §1 (1.6) and Corollary 2](https://doi.org/10.4064/aa-73-2-119-145) gives the estimate
\[
 \sum_{m<X^\beta}\Lambda(m)N_I(m)=\beta H\log X+O_\epsilon(H).
\]
We only use this auxiliary estimate, not the more elaborate maximum-prime-factor bound in that paper. The unrestricted sum is \(\sum_{t\in I}\log t=H\log X+O(H)\). The contribution of all prime powers of exponent at least two, even without a lower cutoff, is \(O(H)\): for \(p^a\le 2X\) the count is at most \(H/p^a+1\), the weighted \(H/p^a\) contributions converge absolutely after dividing by \(H\), and
\[
            \sum_{2\le a\le\log_2(2X)}\ \sum_{p\le(2X)^{1/a}}\log p
                       \ll \sqrt X+X^{1/3}\log X.
\]
Here the Chebyshev upper bound suffices. An exact endpoint \(m=X^\beta\) changes the sum only by \(O(\log X)\) because \(X^\beta>H\). It follows that primes \(p>X^\beta\) contribute \((1-\beta)H\log X+O_\epsilon(H)\). At most one of these primes divides any given \(t\), since \(X^{2\beta}>X+H\) for large \(X\). Each such prime contributes at most \(\log(2X)\). Thus **at least a positive constant times \(\sqrt X\) distinct integers of \(I\)** have a prime factor \(>X^\beta\), uniformly for all sufficiently large real \(X\).

## 2. Elimination when the shifts are moderately sized

Cancelling factorials in (1) gives
\[
 \prod_{i=0}^{d-1}(u+k-i)\prod_{j=1}^{d}(k+j)
                           =\prod_{r=0}^{2d-1}(u-r).
\tag{3}
\]
On pairing \((u+k-i)(k+i+1)\), the difference from its \(i=0\) value is \(i(u-1)-i^2\ge0\) since \(u\ge 2d\). Therefore \((u+k)(k+1)\le u^2\), giving \(k<u\) and \(n<2u\). The previous [signed bound](FactorSingmasterBalancedShiftDrift.md) applies to (1) without a half-row restriction. It states that \(u-d+1/2<\max(8d,7d^2/10)\) for \(d\ge8\), with a finite bound for each \(2\le d<8\). Consequently, along any solutions with \(u\) sufficiently large,
\[
                                 \sqrt u<d.
\tag{4}
\]
Indeed \(d\to\infty\), and for large \(d\) the stated upper bound gives \(u<7d^2/10+d<d^2\).

Now suppose \(d\le u^{53/100}\). Let \(\alpha=(\sqrt5-1)/2\). The upper bound on \((u+k)(k+1)\) and the factor-wise lower bound \((u-2d+1)^2\le (u+k)(k+d)\) from (3) give
\[
                        k/u=\alpha+O(d/u).
\tag{5}
\]
In detail the function \(h(q)=q(1+q)\) at \(q=k/u\in[0,1]\) is at most 1 and at least \(1-O(d/u)\) by these two inequalities, and \(h'\ge1\). This estimate does not require \(k>d\) or that the shifted position be on either specified half.

Consider an integer \(t\in(u-2d,u]\) with a prime factor \(p>u^{29/50}\), and write \(t=jp\), \(1\le j\le u^{21/50}\). For the equality (3) to hold, \(p\) must also divide at least one left-hand factor, of the form \(k+O(d)\) or \(u+k+O(d)\). Any such factor is \(mp\) for an integer \(m\), and after dividing by \(jp=t=u+O(d)\), (5) implies
\[
                           \|j\alpha\|\ll dj/u
\tag{6}
\]
in both cases, since the two centers differ by an integer. The constants in (5)–(6) are absolute. The quadratic conjugate of \(\alpha\) gives
\[
                               \|h\alpha\|\ge\frac1{3h}\quad(h\ge1):
\]
if \(m\) is a nearest integer to \(h\alpha\), the product \((h\alpha-m)(h\alpha'-m)=m^2+hm-h^2\) is a nonzero integer and \(|h\alpha'-m|<3h\).

For a dyadic range \(J\le j<2J\), distinct \(\{j\alpha\}\) in the circle have spacing at least \(1/(3J)\). By (6) they must lie on an arc of length \(O(dJ/u)\), so there are \(O(1+dJ^2/u)\) eligible multipliers in this range. Also (6) and the individual lower bound show \(j\gg\sqrt{u/d}\), so no smaller dyadic range contributes apart from a constant factor at the endpoint. For each eligible \(j\), the number of possibilities for \(p\) is at most \(2d/J+1=O(d/J)\) by (4) and \(J\le u^{21/50}\), even if one counts all integers rather than just primes. Each pair \((j,p)\) supplies one \(t\). Summing the two geometric series across dyadic ranges bounds the total number of eligible right-hand integers by
\[
               O\!\left(\frac{d^{3/2}}{\sqrt u}+d^2u^{-29/50}\right)
               =O(u^{48/100}).
\tag{7}
\]
This includes multiplicities harmlessly if an integer has several admissible descriptions.

In contrast, take \(X=u-\lceil\sqrt u\rceil\). For large \(u\) the square-root interval from §1 lies in \((u-2d,u]\) by (4), has \(\sqrt X\asymp\sqrt u\), and \(X^\beta>u^{29/50}\). It supplies \(\gg\sqrt u\) integers that would all have to satisfy (6) if (3) held. This contradicts (7). Hence no sufficiently large solution has \(d\le u^{53/100}\).

## 3. Large shifts force an edge-to-edge collision

For the remaining case \(d>u^{53/100}\), \(d>n^{21/40}\) for all sufficiently large \(u\), as \(n<2u\). [Baker–Harman–Pintz, Theorem 1](https://doi.org/10.1112/plms/83.3.532) gives a prime in \([n-n^{21/40},n]\). If \(k>n^{21/40}\), this prime is both \(>u=n-k\) and \(>n-d\). It divides the first product of (3) and none of its right-hand factors. Thus
\[
                              k\le n^{21/40}.
\tag{8}
\]
Since \(N=n-d=u/2+k+s/2\ge u/2\), for large \(n\) we have \(k<N/2\). If \(s\le k\), then \({N\choose s}\le{N\choose k}<{n\choose k}\), impossible. If \(s\ge3k\), then \(N-s=k+d\ge3k\) also, since \(d\) grows faster than the bound (8). Therefore
\[
 {N\choose s}\ge {N\choose 3k}\ge (N/(3k))^{3k}>n^k\ge {n\choose k}
\]
for all sufficiently large \(u\): the exponent \(3(1-21/40)=57/40>1\) absorbs the fixed constants. We have \(k<s<3k\).

Rewriting the binomial equality with the reflected index gives the exact product identity
\[
          \prod_{j=0}^{s-1}(N-j)
             =\prod_{i=0}^{k-1}(n-i)\cdot\prod_{j=k+1}^{s}j.
\tag{9}
\]
Suppose \(k+s\ge\sqrt{2n}\). With \(X=n/2\), the square-root interval in §1 lies in \((N-s,N]\): indeed \(N-s=X-(s-k)/2<X\), and \(N-X=(k+s)/2\ge\sqrt X\). Take \(t\) in this interval with prime factor \(p>X^\beta>n^{29/50}\). It cannot divide a factor of the last product of (9), since \(s=O(n^{21/40})\). If it divided \(n-i\) in the first product, it would divide \(2t-(n-i)\). This difference is positive since \(2t>n\), and is at most \(2k+s-1=O(n^{21/40})\), hence strictly less than \(p\). Thus (9) is impossible. We obtain the second bound in (2), \(k+s<\sqrt{2n}\).

In particular \(d=(n-k-s)/2>n/2-\sqrt{n/2}\); the second displayed position on the left half would require \(k+d\le s\), which is impossible for large \(n\). To derive the asymptotic formula, use
\[
 \log{n\choose k}=k\log n-\log k!+O(k^2/n),
 \qquad
 \log{N\choose s}=s(\log n-\log 2)-\log s!+O(k^2/n),
\]
since \(s<3k\) and \(N=(n+k+s)/2\). Also
\(\log(s!/k!)=(s-k)\log k+O(s-k)\). With \(\Delta=s-k>0\) this gives
\[
 \Delta\log(n/k)=k\log2+O(\Delta+k^2/n).
\]
As \(k<\sqrt{n/2}\), moving the \(O(\Delta)\) term into the denominator proves the relative \(O(1/\log n)\) error in (2).

## 4. Exact exclusion of \(s=k+1\)

Here \(n=2k+2d+1\) and \(N=(n+2k+1)/2\). Equality is equivalent to
\[
 R_k(n):=\frac{\prod_{j=0}^{k}(n+2j+1)}
                {\prod_{j=0}^{k-1}(n-j)}=L,\qquad L=(k+1)2^{k+1}.
\tag{10}
\]
For \(k=1\) the two formal solutions are \(n=1,3\), not in the domain \(d\ge1\). For \(k\ge2\), \(R_k(2k+3)<L\): the quotient by \(L\) there equals \((k+3)(k+2)/[(2k+3)(k+1)]<1\). The sign of the logarithmic derivative of \(R_k(n)\) on \(n>k\) is the sign of
\[
 1-\sum_{j=0}^{k-1}\frac{(n+2k+1)(3j+1)}{(n+2j+1)(n-j)} .
\]
It is strictly increasing, because \((n+2k+1)/(n+2j+1)\) and \(1/(n-j)\) are positive decreasing functions. It tends to 1. Hence there is exactly one real solution of (10) above \(2k+3\): the graph, already below \(L\) there, eventually increases to infinity with at most one turning point.

Write \(S=(3k^2-k)/2\), \(C=2k+1+S\), and \(n_*=L-C\). The identity
\[
 R_k(n)=(n+2k+1)\prod_{j=0}^{k-1}
                           \left(1+\frac{3j+1}{n-j}\right)
\]
gives \(R_k(n)>n+C\). If \(n\ge2k+1\) and \(S/(n-k)\le1\), use \(e^v\le1+v+v^2\) for \(0\le v\le1\). The resulting upper bound is
\[
 0<R_k(n)-(n+C)\le
       \frac{2S(3k+1)+8S^2}{n}\le\frac{21k^4}{n}
       \qquad(k\ge4).
\]
Indeed use \(v=\sum_j(3j+1)/(n-j)\le S/(n-k)\) and \(n+2k+1\le 2n\). For \(k\ge20\), \(C+1\le2(k+1)^2\le L/2\) and this last bound on \(L/2\) also exceeds \(S+k\) and \(2k+3\). Hence the hypotheses hold at \(n=n_*-1\ge L/2\), and the error is \(<42k^3/2^{k+1}<1\). The last ratio decreases for \(k\ge4\), and is below 1 at 20. Thus \(R_k(n_*-1)<L<R_k(n_*)\): its unique root in the domain is not an integer. For \(2\le k\le19\), exact product comparisons give the same strict opposition at a pair of consecutive integers, checked by the companion script.

It follows that \(s-k\ge2\) in §3. The asymptotic formula in (2) then gives
\(\liminf k/\log n\ge2/\log2\): if \(k/\log n\) stays bounded on a subsequence, \(\log(n/k)=\log n-O(\log\log n)\); if it does not, this lower bound is automatic.

**Replay.** Run `python3 verify_singmaster_prime_separation.py` for the finite \(s=k+1\) root brackets and integer constants. This complements the proofs and does not attempt to evaluate \(n_0\) or independently prove the cited theorems about primes.
