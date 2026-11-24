# Square-root Fourier models that miss every target in two fixed small-radical families

A restriction of the same-scale signed-minor black-box obstruction to preassigned target families, based on a component size estimate. It is not a counterexample to actual Goldbach, GRH, or a theorem about the true signed minor arcs. The two families below have **different** model weights.

## Theorem

Let \(w(k)=(\log k)\mathbf1_{\{k\ {\rm prime}\}}\), zero at \(0,1\), and let \(e(t)=\exp(2\pi i t)\). For each one of the target sets
\[
\mathcal N_2=\{2^j:j\ge1\},\qquad \mathcal N_3=\{2\cdot3^j:j\ge0\},
\]
there exists one fixed \(v\), zero off primes and \(v(p)\in\{0,2\log p\}\) on primes, such that
\[
(v*v)(N)=0\quad\text{for every }N\in\mathcal N_i,\qquad
\sup_{\alpha\in\mathbf R}\left|\sum_{k\le X}(v(k)-w(k))e(k\alpha)\right|
\ll\sqrt X\log(2X)
\tag{1}
\]
for every real \(X\ge2\). The implicit constant is independent of \(X,\alpha\), and the same \(v\) works at every scale for its specified family.

Consequently \(v\) preserves the ordinary global \(X\)-scale AP discrepancy and standard minor-frequency modulus controls of \(w\) up to this additive error. As in [the companion signed-minor obstruction](SignedMinorFourierObstruction.md), it preserves the exact project sharp-arc major floor, **if** \(A_w(N)\ge cN\) holds for all sufficiently large evens, where the input uses the genuine logarithmic prime weight, target truncation and the same arcs. The estimate is \(|A_v(N)-A_w(N)|\ll\sqrt N\log^5(2N)\). Thus \(B_v(N)=-A_v(N)\le-cN/2\) for every sufficiently large \(N\in\mathcal N_i\). The comparison of signed minor coefficients satisfies \(\sum_{n\le X}|B_v(n)-B_w(n)|^2\ll X^2\log^{10}(2X)\), preserving a bound of order \(X^3\log^{-A}X\) for each fixed \(A\), not preserving an \(X^2\)-scale bound in general.

## 1. Unique parents, roots, and selected exponents

Fix a target set. Take the graph on actual primes greater than \(5\), with an edge between distinct \(p,q\) if \(p+q\) is in that set. The graph has no loop: \(2p=2^j\) forces \(p=2\) if prime; \(2p=2\cdot3^j\) forces \(p=3\) if prime. Set \(v(2)=v(3)=v(5)=0\) at the end, costing only an absolute constant in any linear discrepancy.

For either sequence (successive ratio at least \(2\)), every vertex \(q\) has at most one smaller neighbor \(p\), since its target must lie strictly in \((q,2q)\). There is at most one target in an open factor-two interval, even if the ratio is exactly two. Declare such a neighbor to be the parent of \(q\), if it exists. The graph is a forest: the maximum vertex in any finite cycle would have two smaller cycle neighbors. Even if a component is infinite, each vertex reaches a root under its strictly decreasing parent chain, and the two ends of every edge reach the same root. As vertices connected in an infinite graph are connected by finite paths, each component has a unique root \(r\), its least vertex, and each vertex has a unique root-to-vertex upward path.

Along any upward path, the sequence of target exponents is strictly increasing, because the next target is the current vertex plus a larger vertex, strictly larger than the preceding target. If the endpoint is at most \(X\), every path vertex lies in \([r,X]\), so its targets lie in \((2r,2X]\). For fixed root \(r\), choosing the increasing list of exponents determines the path and vertex uniquely by the successive reflections \(p\mapsto N_j-p\) (some lists are invalid and need only be upper-bounded). The root itself corresponds to the empty list. Thus a finite state automaton over residue classes can upper-bound the number \(m_r(X)\) of vertices from the component of \(r\) in \([1,X]\).

## 2. Two useful automata, each with an exponent strictly below one half

For a sequence of centres \(c_j=N_j\bmod 5\), track the current vertex's residue in \((\mathbf Z/5\mathbf Z)^\times\); all graph vertices exceed \(5\). At each available exponent, skip it or select it. In the latter case the state reflects \(a\mapsto c_j-a\bmod5\), which is forbidden if its value is \(0\). Do not impose any additional primality or size constraints when counting such words. Starting with the unit vector of all ones on the four nonzero residues, the backward operation for appending an available centre to the left is
\[
(L_c d)[a]=d[a]+d[c-a\bmod5]\quad (a\in\{1,2,3,4\}),\qquad d[0]=0.
\tag{2}
\]
This is a nonnegative \(4\times4\) matrix (if \(c-a=a\), both actions are distinct words and contribute twice). The vector \(L_{c_1}\cdots L_{c_m}\mathbf1\) counts valid selection patterns over the chronological centres \(c_1,\ldots,c_m\). Its maximum entry is the product matrix's maximum absolute row sum, hence its \(\ell^\infty\) operator norm. Consecutive blocks multiply these norms, regardless of the residue on entry to a later block. Scaling every centre by a unit \(c\) conjugates the matrices by the residue permutation \(a\mapsto ca\), so maximum row sums are unchanged.

**Powers of two.** For an edge \(p+q=2^j\) with \(p,q>5\), their residues mod \(3\) are both nonzero and must be equal, since \(2^j\not\equiv0\bmod3\). In each component this common residue is fixed, and it forces a single parity of \(j\) (because \(2^j\equiv(-1)^j\)). Thus available centres form a factor-four geometric progression. Modulo \(5\) any four consecutive available centres normalize by a unit to \((1,4,1,4)\). Starting from \(d=(1,1,1,1)\), two centres in this order give \(d=(2,3,4,3)\) via the backward recurrence, and all four give \((6,9,12,9)\). Accordingly every four-centre block has maximum row sum \(12\), including any starting parity or centre. At most \(O(1)+\log_4(X/r)\) centres lie in \((2r,2X]\); the at most three remaining steps each have row norm at most 2. Therefore
\[
m_r(X)\ll(X/r)^{\theta_2},\qquad \theta_2=\frac{\log12}{4\log4}<\tfrac12.
\tag{3}
\]

**Twice powers of three.** With no need for a mod-3 restriction, the successive centres modulo \(5\) are \((2,1,3,4)\) repeated, and starting \(j\) exponents later scales all centres by \(3^j\bmod5\). Applying (2) in backward order to the chronological blocks \((2,1,3,4)^\nu\) gives these exact vectors:
\[
\begin{array}{c|rrrr}
 m &a=1&a=2&a=3&a=4\\\hline
0&1&1&1&1\\
4&8&6&10&10\\
8&60&50&86&86\\
12&492&418&710&710
\end{array}
\]
For reproducibility: with array d[0]=0, d[1..4]=1, traverse the listed centre string in reverse order and replace the entire array simultaneously by new[0]=0, new[a]=d[a]+d[(c-a+5)%5] for a=1..4. The table can equally be obtained by applying the same four-step matrix repeatedly. Every chronological twelve-centre block therefore has norm at most \(710<729=3^6\), by the scaling conjugacy for arbitrary \(j\). At most \(O(1)+\log_3(X/r)\) centres are available, so
\[
m_r(X)\ll(X/r)^{\theta_3},\qquad \theta_3=\frac{\log710}{12\log3}<\tfrac12.
\tag{4}
\]
The crude factor-three spacing argument without residues would only give exponent \(\log_3 2>1/2\); the mod-5 calculation is what repairs it.

## 3. Random components, a single exact sequence, uniform square-root scale

On the component of \(r\), color each prime by \(\varepsilon(p)=(-1)^{\text{depth from }r}\). Independently for each component choose a fair sign \(\xi_r\), and put \(v(p)=(1+\xi_r\varepsilon(p))w(p)\). Coordinates off the graph are as above. Every edge has opposite colors, hence at most one of its weights is nonzero. Any target pair not consisting of two graph vertices contains one of the finitely many excluded primes, whose new weight is zero. Thus all cancellations of target pair products are exact for *every* outcome, not a high-probability statement.

For either \(\theta=\theta_i<1/2\), (3)–(4) and Chebyshev give
\[
\sum_r m_r(X)^2\ll X^{2\theta}\sum_{\substack{r\le X\\r\ {\rm prime}}}r^{-2\theta}
\ll_\theta X/\log(2X).
\tag{5}
\]
The first sum is over component roots, and the second enlarges it to all primes. To see the final estimate, roots below \(\sqrt X\) contribute \(O_\theta(X^{(1-2\theta)/2})\) to the reciprocal-power sum by counting all integers; above \(\sqrt X\) use dyadic intervals, \(\pi(Y)\ll Y/\log Y\), and a geometric sum of ratio \(2^{-(1-2\theta)}<1\). Multiply by \(X^{2\theta}\). This is where the strict inequality in both exponents is needed.

For fixed integer \(X\) and \(\alpha\), the random part of the Fourier discrepancy is a finite sum over components
\[
\sum_r \xi_r A_r,\qquad A_r=\sum_{\substack{p\le X\\p\text{ in component }r}}
 \varepsilon(p)w(p)e(p\alpha),
\]
with \(\sum_r|A_r|^2\ll X\log(2X)\) by (5) and \(|A_r|\le m_r(X)\log X\). A prefix truncates each component's coefficient but does not divide its sign or create fake independent signs. A standard Rademacher exponential moment applied to the two real parts gives tail \(O(\exp(-c u^2/(X\log(2X))))\), uniformly in \(X,\alpha\). Put \(u=C\sqrt X\log(2X)\) and use a grid of \(O(X^3)\) equally spaced torus frequencies. For large absolute \(C\), summing all grid failure probabilities over all integer \(X\ge2\) is \(<1\); some single outcome passes every test, without independence across \(X\). The derivative in \(\alpha\) is \(O(X^2)\) by Chebyshev and \(|v-w|\le w\), so interpolation adds only \(O(X^{-1})\) and proves (1). Finite deleted primes add \(O(1)\).

The same variance bound applies for any fixed bounded deterministic test \(\beta_p\) of modulus at most one in place of \(e(p\alpha)\), and a polynomially sized family of such tests at each scale can be added to the union bound (constant depending on its polynomial exponent). The displayed AP consequence requires no extra net: average the additive Fourier functions at \(j/q\) with the residue phases, and subtract two prefixes for an interval. This gives the global upper-endpoint error \(O(\sqrt X\log(2X))\), not the finer local \(\sqrt{\log(2X)\sum_{k\in I}w(k)^2}\) from genuinely independent reflection pairs. Those pair signs are now correlated within each forest component.

## 4. Signed minor transfer and related work

Use the precise definitions of \(A_u,B_u,Q_N,\mathcal M_N\) in [the companion signed-minor paper](SignedMinorFourierObstruction.md): they concern target-specific Fourier cutoff \(N\), genuine prime-log \(w\), and sharp arcs of length \(O(Q_N^2/N)\), \(Q_N=\lfloor\log_2(N+2)\rfloor^2\). Equation (1) and \(\|S_N^u\|_\infty=O(N)\) for \(u=v,w\) give the claimed \(O(\sqrt N\log^5(2N))\) major difference. Both weights satisfy the exact split \(A_u+B_u=(u*u)(N)\). For the square-summed difference of total correlations up to \(X\), hold the Fourier cutoff \(X\) fixed and use Parseval with (1), obtaining \(O(X^2\log^3(2X))\) from \(\|S_X^v+S_X^w\|_2^2\ll X\log(2X)\). Adding the square-summed error for the target-dependent major difference gives \(O(X^2\log^{10}(2X))\) for the actual signed minor comparison. No assertion is made that the model inherits the identity \(w(p)=\log p\) at every prime, mixed divisor/prime correlations, or any fixed-scale positivity.

Important precedent: Vladimir Shevelev's [OEIS A152451 (2008)](https://oeis.org/A152451) and [A156284 (2009)](https://oeis.org/A156284) already delete primes so that every power of two is omitted from the sumset, with \(A(x)=\pi(x)-O(x/\log^2x)\) in the latter entry. Thus avoiding all powers of two with a large subset of actual primes is **not new**. The distinction here is the doubled/zero weighted component coloring with simultaneous square-root-scale additive Fourier/AP comparison, and hence the same fixed-arc numerical consequence; it also treats a separate \(2\cdot3^j\) family via a nontrivial residue automaton. [Tao's parity-obstruction discussion](https://terrytao.wordpress.com/2014/07/09/the-parity-problem-obstruction-for-the-binary-goldbach-problem-with-bounded-error/) predates the graph viewpoint used here; [Salazar, arXiv:2611.10059v1, §6](https://arxiv.org/html/2611.10059v1#S6) studies minimum prime covers for each power of two in a different problem. The cited results do not assert the precise simultaneous Fourier inequalities here; a full priority search is not complete.
