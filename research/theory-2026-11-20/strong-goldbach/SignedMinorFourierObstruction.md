# A prime-supported Fourier model with large negative signed minor arcs

This is an unconditional construction about a *different* nonnegative weight supported on genuine primes. Its comparison to a positive major-arc floor is a conditional transfer of that floor from the genuine logarithmic prime weight, not a theorem that its genuine signed minor arcs fail. This model preserves named numerical estimates, not the prime indicator identity.

## 1. A single strongly indistinguishable linear model

Write \(w(k)=(\log k)\mathbf1_{\{k\ {\rm prime}\}}\), taking \(w(0)=w(1)=0\), and \(e(t)=e^{2\pi i t}\). There exist a single weight \(v\), with \(v(p)\in\{0,2\log p\}\) on primes and zero elsewhere, and even \(N_j\to\infty\), such that
\[
(v*v)(N_j)=0\quad(j\ge1).
\tag{1}
\]
For every integer \(X\ge2\), every integer interval \(I\subseteq[0,X]\) restricted to one residue class modulo any \(q\ge1\), and every real \(\alpha\),
\[
\left|\sum_{k\in I}(v(k)-w(k))e(k\alpha)\right|
\ll \sqrt{\log(2X)\sum_{k\in I} w(k)^2}.
\tag{2}
\]
The right side is zero when \(w|_I=0\). In particular, for \(S_X^u(\alpha)=\sum_{0\le k\le X}u(k)e(k\alpha)\),
\[
\|S_X^v-S_X^w\|_\infty\ll \sqrt X\log(2X);
\tag{3}
\]
indeed \(\sum_{k\le X}w(k)^2\le\log X\sum_{p\le X}\log p\ll X\log X\) by the elementary Chebyshev estimate. The same notation (2) gives \(\ll\sqrt{|I|}\log^{3/2}(2X)\) for a short interval/AP \(I\), or better if \(\sum_I w^2\) is smaller.

**Intervals and signs.** Take \(N_0=4\); choose each \(N_j\) divisible by 4 and by all primes \(\le N_{j-1}\), and large enough that \(N_j>2N_{j-1}+4\). Put \(v=w\) on \([0,N_0]\). Partition the rest into the disjoint blocks \([N_{j-1}+1,N_j]\). The central part
\[
C_j=[N_{j-1}+1,N_j-N_{j-1}-1]\cap\mathbf Z
\]
is invariant under \(k\mapsto N_j-k\). For each unordered two-element pair \(\{k,\ell\}\subset C_j\) with \(k+\ell=N_j\), independently choose a fair sign \(\xi_{\{k,\ell\}}\). If \(k<\ell\), put \(v(k)=(1+\xi_{\{k,\ell\}})w(k)\) and \(v(\ell)=(1-\xi_{\{k,\ell\}})w(\ell)\). This remains well-defined when either is composite. On the midpoint \(N_j/2\) and the last part \([N_j-N_{j-1},N_j]\), leave \(v=w\). The midpoint is even and \(>2\), so has weight zero. If an input \(k\le N_{j-1}\) in a potential \(N_j\)-pair has positive weight, it is prime and \(N_j-k>k\) is a multiple of \(k\), hence composite. If instead it has zero weight the pair is already killed. A term outside \(C_j\) always has at least one input \(\le N_{j-1}\); inside \(C_j\) the two opposite signs kill the product. Nonnegativity or the individual vanishing even gives (1) for every random outcome. Assignments never overwrite earlier blocks. The divisibility choice removes the deterministic deletions that would otherwise occur at the edges of arbitrary target blocks.

**All intervals, all frequencies, all truncations.** Fix \(X,I,\alpha\). Set \(a_k=w(k)e(k\alpha)\mathbf1_I(k)\). For every pair \(k<\ell\), its contribution to the discrepancy is \(\xi_{\{k,\ell\}}(a_k-a_\ell)\). A partner outside \(I\), including outside the prefix \([0,X]\), has coefficient zero, so a partial pair is still one summand with its original independent sign. Unchanged coordinates have zero discrepancy. Exactly one coefficient occurs per pair, and different pairs, even across blocks, have independent signs. In particular the sum of squared complex coefficient moduli is at most \(2E_I\), where \(E_I=\sum_I w(k)^2\).

For \(E_I>0\), the Rademacher bound is
\[
\mathbb P\Big(\Big|\sum_k(v(k)-w(k))\mathbf1_I(k)e(k\alpha)\Big|>u\Big)
\le 4\exp\big(-u^2/(8E_I)\big).
\]
Indeed \(\cosh(sx)\le e^{s^2x^2/2}\), apply the exponential Markov estimate to both tails of each real component, and use that one component of a complex number of modulus \(>u\) has absolute value \(>u/\sqrt2\). If \(E_I=0\) the sum is identically zero.

For fixed \(X\), there are \(O(X^4)\) different \(I\)'s to consider: \(O(X^2)\) integer endpoint choices and \(O(X^2)\) pairs \((q,a)\) with \(q\le X\); for \(q>X\) every nonempty \(I\) is a singleton. Sample \(O(X^3)\) equispaced frequencies on the torus. Take \(u=K\sqrt{E_I\log(2X)}\) and use a union bound over all those tests. For sufficiently large absolute \(K\), the sum over \(X\ge2\) of all grid failure probabilities is \(<1\). Thus one fixed outcome succeeds at all integer \(X\) simultaneously (alternatively use Borel–Cantelli and absorb finitely many exceptions). No inter-prefix independence is claimed or used. For interpolation, the derivative modulus of the discrepancy polynomial in \(\alpha\) is at most
\(2\pi X\sum_{p\le X}\log p\ll X^2\), since \(|v(k)-w(k)|\le w(k)\). The grid costs \(O(X^{-1})\) in the modulus; for \(E_I>0\), \(E_I\ge(\log2)^2\), and this error is absorbed. This proves (2). All real truncation endpoints follow by flooring.

## 2. The exact major/minor split survives on the major side

For arbitrary measurable arcs \(\mathcal M_N\subseteq[0,1]\), use their actual (possibly \(N\)-dependent) complements, and set
\[
A_u(N)=\Re\int_{\mathcal M_N}S_N^u(\alpha)^2e(-N\alpha)\,d\alpha,\qquad
B_u(N)=\Re\int_{[0,1]\setminus\mathcal M_N}S_N^u(\alpha)^2e(-N\alpha)\,d\alpha.
\]
Termwise Fourier orthogonality gives \(A_u(N)+B_u(N)=(u*u)(N)\) exactly. For comparison, take the sharp major arcs used by the public Goldbach reference project:
\[
Q_N=(\lfloor\log_2(N+2)\rfloor)^2,\quad
\mathcal M_N=[0,1]\cap\bigcup_{\substack{1\le q\le Q_N,\ 0\le a\le q\\(a,q)=1}}
\{\alpha:|\alpha-a/q|\le Q_N/(qN)\}.
\]
The floor in \(\log_2\) expresses the project's natural-number logarithm. Their length satisfies \(|\mathcal M_N|\ll Q_N^2/N\), since for each \(q\) at most \(q+1\) intervals have length \(\le 2Q_N/(qN)\); neither disjointness nor rational-centre separation is needed. The sup norms of both \(S_N^w\) and \(S_N^v\) are \(O(N)\) by \(0\le v\le2w\) and Chebyshev. From (3),
\[
|A_v(N)-A_w(N)|
\le|\mathcal M_N|\|S_N^v-S_N^w\|_\infty\|S_N^v+S_N^w\|_\infty
\ll Q_N^2\sqrt N\log(2N)=o(N).
\tag{4}
\]
Consequently, if the genuine prime-log major floor \(A_w(N)\ge cN\) for sufficiently large evens holds for some \(c>0\), then the same arcs and cutoffs give \(A_v(N)\ge cN/2\) for all large evens. In particular at the infinitely many (sufficiently large) selected targets
\[
B_v(N_j)=-A_v(N_j)\le -cN_j/2.
\tag{5}
\]
This defeats an eventually uniform bound \(B_v(N)\ge-\epsilon N\) for every \(\epsilon>0\). The transfer works even for a uniform main asymptotic for \(A_w\), with the explicit additional error (4). More generally the same proof goes through for smooth arc weights in \([0,1]\) of \(L^1\)-mass \(o((\sqrt N\log N)^{-1})\). The precise sharp-arc source for comparison is [the public Goldbach registry](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/main/research/gaps.json), under arc-major-floor and arc-minor-saving. The major floor is the *real Fourier integral of the true prime logarithmic weight*; no prime-count estimate in a target interval is substituted for it.

## 3. Some genuinely quadratic averaged controls also survive

Equation (2) preserves any usual single-variable cumulative AP estimate to an additional \(O(\sqrt X\log(2X))\), uniformly in \(q,a\). In particular, if the true weight obeys an AP square-root error with \(\log^2(2qX)\) as in a standard GRH estimate, the model inherits it. Similarly any true single-frequency minor-arc modulus bound is inherited with the explicit added term in (3), negligible on usual \(X(\log X)^{-A}\) scales for fixed \(A\). This only concerns those bound forms, not arbitrary sharp short-interval or modulus averages such as full Bombieri–Vinogradov over an expanding range.

Here is a stability statement for strong averages of *binary* estimates. For any integer \(X\ge2\), using ordinary Parseval and retaining the \(X\)-truncation for all \(0\le n\le X\),
\[
\begin{split}
\sum_{0\le n\le X}|(v*v)(n)-(w*w)(n)|^2
&\le\int_0^1|(S_X^v)^2-(S_X^w)^2|^2\,d\alpha\\
&\le\|S_X^v-S_X^w\|_\infty^2\,\|S_X^v+S_X^w\|_2^2\\
&\ll X^2\log^3(2X).
\end{split}
\]
Indeed the Fourier coefficient at \(n\le X\) sees only inputs \(\le X\); \(\|S_X^v+S_X^w\|_2^2\le9\sum_{k\le X}w(k)^2\). In the exact sharp-arc problem above, (4) gives the additional estimate
\(\sum_{2\le n\le X}|A_v(n)-A_w(n)|^2\ll X^2\log^{10}(2X)\).
Subtracting from total correlations proves
\[
\sum_{2\le n\le X}|B_v(n)-B_w(n)|^2\ll X^2\log^{10}(2X).
\tag{6}
\]
In particular any estimate of order \(X^3\log^{-A}X\) for fixed \(A\) against a shared reference minor term survives, including on dyadic blocks, but the negative values in (5) persist. (6) need not preserve sharper estimates such as an error \(o(X^2)\). If arcs and truncation are fixed on the block rather than varying with \(n\), the \(X^2\log^3 X\) difference follows directly by multiplying by the bounded minor indicator before applying Parseval.

## 4. Precise scope and adjacent work

The model cannot satisfy the original definition \(w(p)=\log p\) at every prime, or a prime-specific identity like the multiplicative/convolution identities from which analytic information might be derived. It does not disprove a signed minor estimate for \(w\), GRH, the central criterion, or Goldbach. What it excludes is deducing the required universal signed estimate **for generic nonnegative prime-supported weights** from the listed major floor, single-frequency and AP comparability, plus stable averaged controls. Nor is the failure a changing-target trick: the same \(v\) and its same estimates hold at every scale. The selected \(N_j\) are specially chosen and highly sparse, not arbitrary fixed-residue targets. A weaker variant for prescribed very lacunary even targets replaces the upper edge of each block by zero and forces the midpoint zero; with \(N_j\ge16(N_{j-1}+1)^2\) the \(\ll\sqrt X\) cumulative number of edge deletions preserves (3), but in general not the local form (2).

This is related to Terence Tao's [2014 parity-obstruction article](https://terrytao.wordpress.com/2014/07/09/the-parity-problem-obstruction-for-the-binary-goldbach-problem-with-bounded-error/). The article's main weight is a product of reflected/translational Liouville factors for bounded error, with preservation of discrepancies conjectural in that argument; Tao also explicitly notes graph bipartiteness as a guiding obstruction in the comments, with the relevant passage also findable by searching the page for “2-colourable”. His [additive-combinatorics lectures](https://terrytao.wordpress.com/wp-content/uploads/2008/04/whatsnew_onlineversion1.pdf), §3.3, already note why one-free-parameter even Goldbach is beyond the analogous ordinary Fourier-uniformity argument. [Gowers's course notes](https://www.math.cmu.edu/~af1p/Teaching/AdditiveCombinatorics/notes-acnt.pdf), §4 around Lemma 4.20, discuss Fourier closeness to a sifted model and explicitly caution that binary Goldbach does not follow. The distinction here is the specific fixed infinite prime-supported random-pair model and the unconditional numerical comparison (2)–(6) to the genuine logarithmic prime sequence. Searches for random reflection masks, Fourier-uniform Goldbach obstructions, and pseudoprime models did not find these exact simultaneous bounds; this is a preliminary priority check, not a novelty claim.
