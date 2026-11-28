# Uniform finiteness of nonadjacent repetitions on Pascal antidiagonals

**Theorem.** There are only finitely many triples of integers \((n,k,d)\) with \(k\ge1,\ d\ge2,\ n\ge k+2d\) such that
\[
                              {n\choose k}={n-d\choose k+d}.
\tag{1}
\]
The finiteness is uniform in the equal offset \(d\), and neither displayed index is required to lie on the left half of its row. The proof does not enumerate the finite exceptional set.

In particular, on all sufficiently large antidiagonals \(n+k=T\), any repetition of a value \(>1\) is between adjacent entries. The [Lind–Singmaster classification](https://www.fq.math.ca/Scanned/13-4/singmaster.pdf) already describes those adjacent repeats and supplies infinitely many of them. The new finiteness result does not address repetitions at different \(n+k\), and is not a bound on global Singmaster multiplicity.

## Proof

Use \(u=n-k,\ N=n-d,\ s=u-2d\). Then \({N\choose k+d}={N\choose s}\) and \(N=(n+k+s)/2\). The [prime-separation argument](FactorSingmasterPrimeSeparation.md), §2 and the first part of §3, proves that every sufficiently large solution of (1) obeys
\[
                        k\le n^{21/40},\qquad k<s<3k.
\tag{2}
\]
For clarity, its dependencies at this point are the [previous uniform row bound](FactorSingmasterBalancedShiftDrift.md) to ensure \(d>\sqrt u\) for large solutions, Baker–Harman's square-root-interval weighted prime-factor estimate and the golden-ratio counting argument to eliminate \(d\le u^{53/100}\), and Baker–Harman–Pintz to force \(k\le n^{21/40}\) in the remaining regime. The binomial size comparison then gives \(k<s<3k\). We do not need the sharper square-root bound on \(k+s\) or the separate exact exclusion of \(s=k+1\) proved later in that note.

If a sequence of solutions has \(n\to\infty\), then \(k\to\infty\) along it. Otherwise a subsequence would have fixed \(k,s\) with \(s>k\) by (2), but \({N\choose s}\) grows as a positive constant times \(n^s\) and \({n\choose k}\) has degree \(k\). Thus it suffices to exclude the case \(n\to\infty\), \(k\to\infty\) under (2).

Cancelling \(s!\) and \(k!\) in \({n\choose k}={N\choose s}\) gives
\[
          \prod_{j=0}^{s-1}(N-j)
            =\prod_{i=0}^{k-1}(n-i)\cdot\prod_{j=k+1}^{s}j .
\tag{3}
\]
Focus just on the factors of the left side strictly above \(n/2\). They are the consecutive interval
\[
                  X,X+1,\ldots,X+h-1=N,\qquad
                  X=\lfloor n/2\rfloor+1,\quad h=N-\lfloor n/2\rfloor.
\]
Indeed \(N-s=n/2-(s-k)/2<n/2\). We have \(k<h\le2k\) from \(k<s<3k\) and the integral endpoints; also \(k+s\le 2h\). In particular \(h\to\infty\) and \(X\ge h^{3/2}\) for large \(n\), since \(h\le2n^{21/40}\) and \((3/2)(21/40)=63/80<1\).

We use the following elementary form of the classical prime-deletion argument of Erdős (also used by [Shorey–Tijdeman, §1.4](https://www.math.leidenuniv.nl/~tijdeman/shoretij.pdf)). For all sufficiently large \(h\), a block of \(h\) consecutive integers starting at \(X\ge h^{3/2}\) has a prime divisor \(>3h\). To see it, suppose all its prime divisors were \(\le3h\), and for each such prime \(p\) remove one term containing the highest power of \(p\) attained in the block. At most \(\pi(3h)=o(h)\) terms are removed by the Chebyshev bound. For each \(a\ge1\), the original number of multiples of \(p^a\) is at most \(1+\lfloor(h-1)/p^a\rfloor\); if this number is positive, at least one such multiple is removed. Hence the remaining product divides \((h-1)!\) by the ordinary valuation formula. But its size is at least \(X^{h-o(h)}\ge h^{(3/2)(h-o(h))}>h^h\), a contradiction.

Take a prime \(p>3h\) given by this argument and a term \(t\in[X,N]\) that it divides. The small factors \(k+1,\ldots,s\) on the right side of (3) are all \(<2h<p\). If \(p\) divided \(n-i\) for \(0\le i<k\), it would divide the positive integer \(2t-(n-i)\) because \(t>n/2\). But
\[
              0<2t-(n-i)\le 2N-n+k-1=k+s+k-1<3h<p .
\]
This also is impossible, contradicting (3). Thus (1) has no unbounded sequence of solutions. For any fixed \(n\) its domain for \(k,d\) is finite, establishing the stated finiteness.

The result resolves the qualitative question for \(d\ge2\) without fixing the offset. It does not claim that the finite set is empty. The previous exact computation covers \(2\le d\le256\) only. Case \(k=0\), which can give boundary values \(1\) for every \(d\), is deliberately excluded.
