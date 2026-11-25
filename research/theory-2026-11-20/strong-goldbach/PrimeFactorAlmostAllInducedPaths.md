# Almost-all induced factor paths in logarithmically separated layers

Companion to the [all-target multiscale result](PrimeFactorMultiscaleDisjointPaths.md). This is an application of the additive large sieve and Hall matching to actual factor arcs. It gives no estimate for a prescribed sparse target, for terminal components, or for Goldbach pairs, and makes no priority claim.

**Theorem.** Fix \(h\ge1\), \(A\ge2\), and \(0<\alpha<1\). Given a large block parameter \(T\), put
\[
 L=\log T,\quad B=A+h+2,\quad X_i=T^\alpha/L^{Bi}\quad(0\le i\le h).
\]
For all even \(N\in[T,2T]\) apart from \(O_{A,h,\alpha}(T/L^A)\), there are \((1+o(1))X_h/\log X_h\) pairwise vertex-disjoint true directed paths \(p_0\to\cdots\to p_h\) with \(X_i<p_i\le2X_i\). Here \(q\to r\) means \(r\mid N-q\), the reverse of the orientation in [Bożek's graph](https://arxiv.org/abs/1909.09900). Each edge has \(v_{p_{i+1}}(N-p_i)=1\) and is a proper divisor edge; on each individual path's vertices there are no additional arrows. There may be arcs between different paths in the matching. In particular \(\alpha=1/2\) keeps all layers at square-root exponent even for arbitrarily large fixed depth.

## Raw incoming degree in the actual residue

For one adjacent pair write \(X=X_{i-1}\), \(R=X_i\), \(\Theta=\sum_{X<p\le2X}\log p\), and \(F(\xi)=\sum_{X<p\le2X}(\log p)e(p\xi)\). If \(r\in(R,2R]\) is prime, exact finite Fourier Parseval gives
\[
 \sum_{a\bmod r}\left|\sum_{\substack{X<p\le2X\\p\equiv a\bmod r}}\log p-\Theta/r\right|^2
    =\frac1r\sum_{j=1}^{r-1}|F(j/r)|^2.
\]
All these nonzero fractions across the prime moduli are distinct and have circular spacing at least \(1/(4R^2)\). The [Montgomery–Vaughan additive large sieve](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf) and the prime number theorem show that the sum of these squared deviations over all prime \(r\) is
\[
 \ll \frac{X+R^2}{R}\sum_{X<p\le2X}(\log p)^2
 \ll XR L.
\]
Here \(R=X/L^B\gg\sqrt X\), and \(\log X\asymp L\). This is a direct proof for the needed prime bands, with no unproved pointwise distribution or use of a small-modulus extension.

Each actual residue \(a=N\bmod r\) is sampled at most \(T/r+1\ll T/R\) times in the block (restricting to even \(N\) does not increase this). For any fixed \(N\), call its prime child label bad if the deviation exceeds \(X/(8R)\). All nonbad children have \(\gg X/(RL)\) genuine parents by \(\Theta\sim X\). The sum of bad counts over the target block is
\[
 \ll (T/R)(R/X)^2 XR L = T R^2L/X.
\]
Consequently the number of targets with more than \(R/L^{h+1}\) bad labels in this layer is \(O(T L^{h+2}R/X)=O(T/L^A)\). Take the union over the fixed \(h\) layers. Remove the \(O(L)\) primes dividing \(N\) separately in each layer; any such exclusions are negligible at the polynomial scales.

## Simultaneous pruning and induced Hall matching

For a remaining target let \(G_0\) be the unit primes of layer zero. Suppose excluded parents from layer \(i-1\) number \(O(X_{i-1}/L^{h+3-i})\). Each such parent can lose only \(O_\alpha(1)\) edges into the child band: the product of distinct polynomial-sized prime divisors of \(N-p\le2T\) cannot have unbounded rank. Remove children losing more than half the fixed guaranteed incoming degree. Their number is \(O(X_i/L^{h+2-i})\), found by dividing the total number of lost incidences by a constant times \(X_{i-1}/(X_iL)\). Combine these removed children with the raw bad set and nonunits. This proves inductively that \(G_i\) has at most \(O(X_i/L^{h+2-i})\) omissions from its prime band and that every retained child has \(\gg L^{B-1}\) parents in \(G_{i-1}\). In particular \(|G_h|\sim X_h/\log X_h\).

Start with one suffix per retained bottom vertex. At an upward step, a parent \(p\) for the start \(r\) of a suffix must satisfy \(p\equiv N\bmod r\). For any strictly later label \(s\) in the suffix a forward chord \(p\to s\) imposes \(p\equiv N\bmod rs\), excluding \(O(X/(rs)+1)\) candidates. A reverse arrow \(s\to p\), including \(s=r\), excludes only \(O_\alpha(1)\) candidate divisors of \(N-s\). The repeated-child test \(r^2\mid N-p\) excludes \(O(X/r^2+1)\). Since every label in play exceeds \(T^{\alpha/2}\) and \(X/R=L^B\), these losses are \(o(X/(RL))\) for the fixed depth. Each suffix still has \(\gg L^{B-1}\) eligible incoming parents, with all possible new chords and repeated marked factors removed. Each parent serves only \(O_\alpha(1)\) different suffix starts (which are distinct actual factors), so double-counting gives Hall's condition for matching all suffixes simultaneously. The layers are disjoint, the vertices are units (hence no loops), and all labels are \(o(N)\) (hence the marked factors are proper). Repeat to the top; the result follows.

The same final deletion and matching also apply to the already-retained incoming degrees in the [fixed-target theorem](PrimeFactorMultiscaleDisjointPaths.md), whenever the given exponents satisfy its hypotheses. There the ratio of a parent scale \(X\) to its child scale \(R\) grows as a positive power, and all labels are bounded below by a fixed positive power of \(N\); the very same loss estimates are negligible. This upgrades its existing exponent ranges to individual induced paths and exact child valuation one without any average over \(N\).
