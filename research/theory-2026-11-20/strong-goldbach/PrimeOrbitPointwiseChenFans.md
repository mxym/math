# A pointwise common-target alternative on rough Chen representations

Use arcs \(a\to b\) when the primes satisfy \(b\mid N-a\), the reversal of [Bożek's Definition 2.1](https://arxiv.org/abs/1909.09900). The statements below concern a *single arbitrary sufficiently large even* \(N\); no exceptional set of centers is discarded. Put \(L=\log\log N\), \(R=\lfloor L/(1000\log(2L))\rfloor\).

**Prime-or-fork alternative.** For some absolute \(c>0\), either \(N\) has at least \(cN/\log^2N\) genuine binary Goldbach representations (ordered choice of the first prime), or at least \(cN/\log^2N\) distinct primes \(x\) have all the following properties:
* \(N-x=qk\) with different unit primes \(q,k\ge N^{1/10}\), and \(x\) is a unit prime. Thus there are precisely the two distinct choices \(x\to q,k\).
* Each child \(a=q,k\) has at least \(L/5\) distinct prime successors \(t\) in \([\exp(L^2),N^{1/1000}]\) which are **not successors of the other child**.
* For *every* odd prime \(r\le R\) not dividing \(N\), each child has at least \(L/(5(r-1))\) such private successors \(t\) with \(t\equiv N\bmod r\). Thus, whichever of the two factors is selected first, there are many actual paths \(x\to a\to t\to r\). The lists for different targets need not be disjoint. The unconditional lower bound \(L/5\) is meaningful even if all small target primes divide \(N\).

In particular the displayed structure is compulsory at every sufficiently large hypothetical Goldbach exception. Its paths point **from the Chen witnesses into small targets**, not in reverse, and give no claim that a distinguished small seed reaches the displayed forks or a prime pair.

**Small-input interval variant.** Fix \(0<\eta\le1\). For every \(e^{(\log N)^\eta}\le H\le N\), all but \(o_\eta(H/\log H)\) prime inputs \(2\le a\le\min(H,N-2)\) have at least \((\log\log H)/(5(r-1))\) routes \(a\to t\to r\) with different intermediate primes, simultaneously for all odd prime targets \(r\nmid N\) up to \(\eta L/(1000\log(2L))\). This is uniform in \(N,H\) in the stated ranges, not an averaged conclusion about centers. Prime inputs dividing N may be discarded. It describes access *to* a given small target, not outward access from that target.

## The quantitative input

In [H. Halberstam, “A proof of Chen's theorem”, Astérisque 24–25 (1975), pp. 281–293](https://www.numdam.org/article/AST_1975__24-25__281_0.pdf), the theorem and footnote on p. 281 specialize \(a=-1,\ h=x=N\) to the Goldbach case. The lower-bound expression is a weighted sum with \((N-p,P(N^{1/10}))=1\), and the positive weights described on pp. 281–282 are at most one and supported on \(P_2\) complements. The prime factors of N excluded from \(P(\cdot)\) do not affect unit inputs. Thus \(\gg N/\log^2N\) input primes have complement prime or a product of two primes at least \(N^{1/10}\). A complement 1 costs at most one. The roughness is a property of the *proof's positive-weight support*, not a consequence of unweighted Chen existence. See also [AMS, Sieve Methods, Theorem 12.11 and the following sentence, p. 193](https://www.ams.org/bookstore/pspdf/gsm-134-prev.pdf) for an explicit statement of the rough version.

If there are fewer than half this certified number of genuine prime complements, there are \(\gg N/\log^2N\) semiprime witnesses. We may discard \(O(\sqrt N+\log N+N^{1/1000})\) rows with square complement, nonunit parent, or \(x\le N^{1/1000}\). The remaining children are automatically units, since \(\gcd(N,N-x)=1\).

## Upper sieve with optional bridge classes

Consider one choice of child q, holding the other prime k fixed. Write \(H=N/k\), \(w=N^{1/1000}\), \(E=\exp(L^2)\). Now \(N^{1/10}\le H\le N\). The prime variables being sifted are \(q\le H\) and \(x=N-kq>w\); also \(q>w\). Ignore primes dividing \(M=6Nk(k-1)(N-k)\). For every remaining prime \(\ell\le w\), two residue classes of q are forbidden, namely 0 and \(Nk^{-1}\bmod\ell\), and they are distinct. At each additional bridge prime \(t\in[E,w]\), \(t\nmid M\), offer an optional third exclusion \(q\ne N\bmod t\). For a specified target r, offer this only for \(t=N\bmod r\); for the uncolored count offer it for every such t. Because \(t\nmid Nk(k-1)\), the three residue classes are distinct, and \(t\nmid N-k\) means a bridge \(t\mid N-q\) is private to q rather than also dividing \(N-k\). The bridge size separates t from q,k,r, it does not divide N, and \(r\mid N-t\) in the colored case. Both asserted arcs therefore exist.

Let \(\mathcal T\) be the offered primes and take any subset \(J\subseteq\mathcal T\) of third exclusions. With \(\nu_\ell=2+1_{\ell\in J}\) at the good primes just described, the arithmetic large sieve bounds the count of indices surviving all exclusions by
\[
   \ll H\prod_{\substack{5\le\ell\le w\\\ell\nmid M}}(1-2/\ell)
               \prod_{t\in J}\big(1-1/(t-2)\big).                 \tag{1}
\]
For completeness take the large-sieve denominator summing squarefree \(d\le z=H^{1/3}\) supported on these good primes with weights \(\prod_{\ell\mid d}\nu_\ell/(\ell-\nu_\ell)\). Under the unrestricted normalized Euler mass the mean \(\log d\) is at most \(3\sum_{\ell\le w}(\log\ell)/\ell\le3\log w+O(1)\), less than half \(\log z\). At least half the mass is within \(d\le z\), and the numerator \(H+O(1)+z^2\) is \(O(H)\). The product form (1) follows, with constant independent of r, k, N and the random subset used below. This is the usual [Montgomery–Vaughan arithmetic large sieve, Ch. 19](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf).

Uniformly the first product is \(\ll L^3/\log^2N\). Indeed Mertens gives the unrestricted size \(O(1/\log^2 w)\), and for \(\ell\ge5\) a removed factor costs at most \((1-1/\ell)^{-3}\). The product of \((1-1/\ell)^{-1}\) over \(\ell\mid M\) is \(O(\log\log(3M))=O(L)\) as \(1\le M\ll N^4\); this also follows by splitting the product at \((\log(3M))^2\).

Write \(\mu=L/(r-1)\) for the colored case and \(\mu=L\) for the uncolored case. By [Siegel–Walfisz](https://personal.science.psu.edu/rcv4/Bombieri.pdf) and partial summation (or Mertens in the uncolored case),
\[
                 \sum_{t\in\mathcal T}1/t\ \ge\ 0.8\,\mu.         \tag{2}
\]
Indeed before removing primes of M the sum for target r is \((L-2\log L+O(1))/(r-1)+o(1)\) uniformly: the distribution theorem applies for each upper endpoint \(v\ge E\) since \(r\le\log v\), and the integrated exponential error is \(o(1)\). The class \(N\bmod r\) is reduced. The large factors of M removed here cost at most \(\log M/(E\log2)=o(1)\), *not* an r-dependent singular factor. The same calculation without \(r-1\) applies to the uncolored set; throughout the required ranges \(\mu\to\infty\).

Include each \(t\in\mathcal T\) in J independently with probability \(1/2\). This is only a proof device for a deterministic counting bound. If a true row has fewer than \(\mu/5\) private bridge primes from \(\mathcal T\) dividing \(N-q\), it survives with probability at least \(2^{-\mu/5}\). The mean of the last product in (1) is at most \(\exp(-\tfrac12\sum_{t\in\mathcal T}1/t)\). Equations (1) and (2) therefore bound the number of such deficient q at fixed k and target by
\[
       \ll \frac{N}{k\log^2 N}\, L^3\,
            \exp\{-(0.4-(\log2)/5)\mu\}
       \ll \frac{N}{k\log^2 N}\, L^3 e^{-\mu/4}.               \tag{3}
\]
This bound uses primality of q and of \(N-kq\); it does not posit independence of those primality tests.

For either designated child, the other prime k lies in \([N^{1/10},N^{9/10}]\). Its reciprocal-prime sum is \(O(1)\), which matters in (3); summing over all integers would lose a factor of order \(\log N\). Union over both ordered child choices, the uncolored count and the at most R target primes. For all colored targets \(\mu\ge1000\log(2L)\). Thus the total number of deficient witnesses is \(o(N/\log^2N)\). Subtracting from the rough Chen lower bound proves the first assertion and its pointwise dichotomy.

## Small input intervals without a Chen parent

For \(a\le H\) write \(L_H=\log\log H\ge\eta L\); take \(w=H^{1/1000}\), \(E=\exp(L^2)\). For each prime \(\ell\le w\) forbid the class \(a=0\bmod\ell\) for input primes \(a>w\), and for potential bridge primes \(E\le t\le w\) with \(t=N\bmod r\), \(t\nmid N\), offer the third-class analogue \(a\ne N\bmod t\), distinct from 0. Here there is just one base exclusion at each prime. The uniform truncated-denominator proof of (1) is the same with at most two local classes and \(z=H^{1/3}\), while Mertens gives the base product \(O(1/\log H)\) with no N-divisor loss. The bridge reciprocal mass is at least \(0.8 L_H/(r-1)\) for large N depending on \(\eta\): before removing factors of N its numerator is \(L_H-2\log L+O(1)\) by the same Siegel–Walfisz calculation. Apply the random-subset argument to obtain at most
\[
        O_\eta\!\left(\frac H{\log H}
               \exp\{-L_H/(4(r-1))\}\right)
\]
inputs with fewer than \(L_H/(5(r-1))\) bridges for target r. The union in the stated range is \(o_\eta(H/\log H)\). Tiny inputs \(a\le w\), primes dividing N, and the possible vertex \(N-1\) cost \(O(w+\log N+1)=o_\eta(H/\log H)\). Since \(t\nmid N\), a bridge cannot equal a when \(t\mid N-a\), and since \(t>r\) it does not equal the target. Even if \(a=r\), a counted return route has two genuine edges; allowing a zero-length path is not needed. This completes the proof in a fixed center.

The [density theorem for accessible genuine pairs](PrimeOrbitCommonGoldbachSink.md) runs in a different direction and on a restricted set of centers. Neither theorem upgrades the incoming Chen paths to outgoing paths from arbitrary specified integer seeds.

**Related work.** The [October 2026 TCDC notes](https://amral.evemisslab.com/en/goldbach/tcdc/) also use Chen-type information and describe conditional closure questions for rough configurations. The assertion here is the unconditional one-directional abundance of actual private two-step bridges for each child after a rough Chen fork, not a closure theorem. No priority claim is made.
