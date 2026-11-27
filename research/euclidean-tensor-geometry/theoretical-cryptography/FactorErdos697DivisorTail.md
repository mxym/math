# Polynomial tail rates in Hall's divisor-in-a-residue-class problem

## Statement and scope

For an integer \(m\ge 2\) and real \(\alpha>0\), let \(D_\alpha(m)\) be the natural density of integers divisible by some \(1<d<\exp(m^\alpha)\) with \(d\equiv1\pmod m\). Put
\[
 b_0=\frac1{\log2},\qquad I_\alpha(b)=b\log(b/\alpha)-b+\alpha
 \quad (b\ge0),\qquad I_\alpha(0)=\alpha.
\]
All logarithms except \(\log_2\) applied to a single number in this note are natural; here \(\log_2 x=\log x/\log 2\). The notation \(m^{-\kappa}(\log m)^{\pm O_\alpha(1)}\) means bounded above and below by \(m^{-\kappa}\) times fixed powers of \(\log m\), with constants allowed to depend on fixed \(\alpha\).

**Theorem.** Uniformly over integer moduli \(m\to\infty\), the following hold unconditionally.

1. For \(0<\alpha<b_0\),
   \[
   D_\alpha(m)=m^{-\kappa_-(\alpha)}(\log m)^{\pm O_\alpha(1)},\qquad
   \kappa_-(\alpha)=
   \begin{cases}
   1-\alpha,&0<\alpha\le b_0/2,\\
   I_\alpha(b_0),&b_0/2\le\alpha<b_0.
   \end{cases}
   \]
2. For \(b_0<\alpha\le2b_0\),
   \[
   1-D_\alpha(m)=m^{-I_\alpha(b_0)}(\log m)^{\pm O_\alpha(1)}.
   \]
3. For \(\alpha>2b_0\), the same proof gives the (not generally matching) bounds
   \[
   m^{-I_\alpha(b_0)}(\log m)^{-O_\alpha(1)}
   \ \le\ 1-D_\alpha(m)\ \le\
   m^{-(\alpha/2-1)}(\log m)^{O_\alpha(1)}.
   \]

For example the rate at \(\alpha=1\) is \(I_1(b_0)=0.086071\ldots\), so \(D_1(m)=m^{-0.086071\ldots+o(1)}\), with the decimal shorthand for the exact constant. At \(\alpha=2\), \(1-D_2(m)=m^{-I_2(b_0)+o(1)}\). The extra breakpoint at \(b_0/2\) comes from the change in which prime-factor counts dominate the success probability, not from a change in the original zero–one limit.

The [original question of Erdős](https://www.numdam.org/item/AST_1979__61__73_0/) is [#697](https://www.erdosproblems.com/forum/thread/697?embed=1). [Hall (1992)](https://doi.org/10.1016/0022-314X(92)90096-8) already proved the zero–one law and determined \(b_0\). [Erdős–Tenenbaum (1999), Theorem 4](https://tenenb.perso.math.cnrs.fr/PPP/Suites_finies.pdf) addresses simultaneous reduced-class coverage in the Gaussian window, and [de la Bretèche (2000), Theorems 1–2](https://doi.org/10.1112/S0024609399006773) proves the relevant single-class Gaussian transition and further simultaneous coverage results. Their absolute \(o(1)\) transition formulas do not themselves give the logarithmic tail rates here. [Banks–Friedlander–Luca](https://arxiv.org/abs/math/0604036) treats a different limit: a fixed prime modulus, an integer sampled up to \(x\), and no separate cutoff on its divisors. This note gives a self-contained rate refinement of the growing-modulus natural-density problem; it makes no priority claim about every earlier quantitative inequality, no new claim for the Gaussian limit, and no sharp claim for the far upper tail in part 3.

## 1. Exact probability space and size truncation

Write \(L=\log m\), \(Y=\exp(m^\alpha)\), \(P=\exp(L^3)\) and \(G=(\mathbb Z/m\mathbb Z)^\times\), \(g=|G|=\varphi(m)\). Only sufficiently large \(m\) is relevant. Use independent random variables \(V_p\), for the finitely many primes \(p\le Y\), with \(\Pr(V_p\ge j)=p^{-j}\). The divisibility event is the same as for the random integer \(\prod_{p\le Y}p^{V_p}\). Indeed, it is decided by the valuations truncated at \(\lfloor\log Y/\log p\rfloor\), and the Chinese remainder theorem makes these truncated valuations independent under the exact uniform distribution modulo the product of the prime powers used. The same assertion gives existence of the natural density.

Let \(M=\prod_{p\le P}p^{V_p}\) and, for \(P<R\le Y\), let \(Q_R=\#\{P<p\le R:V_p\ge1\}\). We will use only \(R=Y\) and \(R=Z=Y^{1/(2BL)}\), with a sufficiently large fixed \(B>2b_0+2\) depending on \(\alpha\). For either \(R\), Mertens's theorem gives
\[
 \lambda_R=\mathbf E Q_R=\sum_{P<p\le R}p^{-1}
 = \alpha L+O_\alpha(\log L),\qquad
 \Pr(Q_R>BL)\le m^{-A}
 \tag{1}
\]
for any prescribed fixed \(A>0\), by taking \(B\) large enough. For the latter claim,
\(\mathbf E e^{Q_R}\le\exp((e-1)\lambda_R)\) already suffices. The notation \(Z\) here depends on the chosen \(B\). If \(Q_Z\le BL\), the product of all supported primes from \((P,Z]\), each used once, is at most \(Y^{1/2}<Y\). Thus any nonempty subset of these primes giving residue \(1\) is an admissible divisor for the **lower** bound for success, or equivalently the **upper** bound for failure. In the reverse directions we may ignore the size cutoff while using primes up to \(Y\).

We use \(O_A(m^{-A})\) error estimates for any fixed \(A\) unless a specific smaller error is listed. In particular the probability that any \(P<p\le Y\) has \(V_p\ge2\) is at most \(\sum_{p>P}p^{-2}\ll P^{-1}\). This is an *unconditional* additive error, so there is no conditioning on an atypical squarefree event.

## 2. Uniform comparison with an independently labeled Poisson sample

Conditional on \(Q_R=q\), a uniformly ordered list of the distinct supported primes has probability proportional to the product of \(w_p=(p-1)^{-1}\) over the list. In fact, for a set of Bernoulli successes the product of the odds \(w_p\) gives its weight after factoring out the probability of no successes. This is the same ordered law as \(q\) independent draws with probabilities \(w_p/W_R\), \(W_R=\sum_{P<p\le R}w_p\), conditioned on the draws being distinct. Dropping that conditioning costs at most \(O(q^2/(P W_R))\) in total variation, since two draws coincide with probability at most \(\max_p w_p/W_R\).

For \(q\le BL\), the resulting residues are within \(O_A(m^{-A})\) in total variation of independent uniform elements of \(G\). For this, the classical Siegel–Walfisz prime number theorem (e.g. [Koukoulopoulos, Theorem 12.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf)) applies at every \(t\ge P\): already \(m\le(\log t)^1\) for large \(m\). Partial summation gives, uniformly in \(a\in G\),
\[
 \sum_{\substack{P<p\le R\\p\equiv a\bmod m}}\frac1{p-1}
 =\frac1{\varphi(m)}\int_P^R\frac{dt}{(t-1)\log t}
    +O\!\big(e^{-c\sqrt{\log P}}\big).
 \tag{2}
\]
Here the endpoint error is \(O(e^{-c_0\sqrt{\log P}})\) and the integrated error is bounded by a constant times \(\int_{\log P}^\infty e^{-c_0\sqrt u}\,du=O(e^{-c\sqrt{\log P}})\) after decreasing \(c>0\). Summing over at most \(m\) classes, dividing by \(W_R\asymp_\alpha L\), and taking a \(q\)-fold product preserves the stated superpolynomial error, since \(\sqrt{\log P}=L^{3/2}\). This approximation is independent of \(M\).

Also \(Q_R\) differs in total variation from \(\operatorname{Pois}(\lambda_R)\) by \(O(P^{-1})\) ([Le Cam's Poisson approximation](https://msp.org/pjm/1960/10-4/pjm-v10-n4-p11-p.pdf), or couple each Bernoulli of parameter \(p^{-1}\) to a Poisson of the same mean with error \(O(p^{-2})\)). Thus for computations involving \(q\le BL\) both the law of the count and the conditional law of the labels have errors negligible compared to any fixed power of \(m^{-1}\).

## 3. Counting group hits and controlling small primes

Let \(U_1,\ldots,U_q\) be independent uniform elements of a finite abelian group of size \(g\). The products labeled by two distinct nonempty subsets of indices are individually uniform and pairwise independent: if neither subset contains the other use one index exclusive to each; if one contains the other use one index in the smaller subset and one exclusive to the larger one. Once the remaining variables are fixed, the two chosen variables map bijectively to the two products. For any specified target, the number \(H\) of nonempty subset hits therefore satisfies \(\mathbf EH=(2^q-1)/g\) and \(\operatorname{Var}H\le\mathbf EH\). For \(q\ge1\), Cauchy–Schwarz, the union bound, and Chebyshev give
\[
 \begin{split}
 c\,\min(1,2^q/g)&\le \Pr(H>0)\le \min(1,2^q/g),\\
 \Pr(H=0)&\le C\,\min(1,g2^{-q}).
 \end{split}\tag{3}
\]
Absolute constants work, e.g. \(c=1/4,C=2\); for the second inequality also allow \(q=0\). It matters that the identity at the empty subset is *excluded*. The easy bounds \(c_1 m/L\le g\le m\) follow from
\(\prod_{p\mid m}(1-1/p)\ge\prod_{p\le m}(1-1/p)\) and Mertens's product theorem.

On the complement of the repeated-prime event, any admissible divisor using a prime \(>P\) consists of a nonempty large-prime subset times some \(u\mid M\). Only \(u\) coprime to \(m\) is relevant. Condition on \(M\) and \(q\), so each \(u\) supplies at most one group target. By the union bound and \(\min(1,kx)\le k\min(1,x)\) for \(k\ge1\), their combined hit probability in the uniform-label model is at most \(\tau(M)\min(1,2^q/g)\). The coupling error is charged **once** for the union event, not once per \(u\). Since
\[
 \mathbf E\tau(M)=\prod_{p\le P}(1-1/p)^{-1}\asymp \log P=L^3,
 \tag{4}
\]
averaging this bound loses at most a power of \(L\).

All-small witnesses also contribute negligibly in the subcritical estimate below. Fix any \(\epsilon>0\) and set \(s=1/\log P\). By independence,
\[
 \mathbf E M^s=\prod_{p\le P}\frac{1-p^{-1}}{1-p^{s-1}}\ll1.
\]
Indeed, each logarithm is \(O((p^s-1)/p)\) for \(s\le 1/2\), and \(p^s-1\le es\log p\), so \(\sum_{p\le P}(\log p)/p\ll\log P\) suffices. This puts \(\Pr(\log M>m^\epsilon)\ll \exp(-m^\epsilon/L^3)\). For \(\log M\le m^\epsilon\), the probability of any nontrivial all-small divisor congruent to \(1\) is at most
\[
 \sum_{\substack{1<d\le \exp(m^\epsilon)\\d\equiv1\bmod m}}\frac1d
 \le \frac{1+m^\epsilon}{m},
 \tag{5}
\]
using a union bound, \(d=1+jm\), \(j\ge1\), and \(\Pr(d\mid M)=1/d\) if \(d\) is \(P\)-smooth (zero otherwise). This avoids treating \(d=1\) as a hit.

## 4. The optimizations and matching sides

For either \(R\), uniformly at integers \(0\le q\le BL\), Stirling's formula in the Poisson model gives
\[
 \Pr(\operatorname{Pois}(\lambda_R)=q)
 =m^{-I_\alpha(q/L)}L^{\pm O_{\alpha,B}(1)}.
 \tag{6}
\]
Use \(\log(q!)=q\log q-q+O(\log(q+2))\), with the zero convention; the difference between \(\lambda_R\) and \(\alpha L\) affects the log probability by \(O_{\alpha,B}(\log L)\). Fixed examples of \(q/L\) used below are positive; rounding \(q\) then affects the log probability by \(O_\alpha(1)\). Since \(g\) differs from \(m\) by at most a factor \(O(L)\), the two weights in (3), up to logarithmic factors, are
\[
 m^{-(1-(q/L)\log2)_+}\quad\text{and}\quad
 m^{-((q/L)\log2-1)_+}.
 \tag{7}
\]
Sums over \(q\le BL\) incur only another factor \(O(L)\).

For subcritical \(\alpha\), apply (4), (5), and the union over \(q\le BL\) with \(R=Y\) for the upper bound; the exponent from (6)–(7) is the minimum of
\[
 I_\alpha(b)+(1-b\log2)_+,\qquad b\ge0.
\]
Below \(b_0\), its derivative in \(b\) is \(\log(b/(2\alpha))\); above \(b_0\) the derivative is \(\log(b/\alpha)>0\). The minimizer is \(b=\min(2\alpha,b_0)\). This gives \(\kappa_-(\alpha)\) in the statement; it is strictly less than \(1\), so (5) is negligible with a suitably small fixed \(\epsilon>0\). For the lower bound use \(R=Z\) and restrict to \(q\) nearest this minimizing \(bL\). The first inequality of (3) supplies the probability of an admissible divisor containing only large primes, by the strict \(Y^{1/2}\) size bound. All coupling and discarded-count errors may be chosen negligible relative to the main estimates. This proves part 1.

For supercritical \(\alpha\), the probability of failure is upper bounded using \(R=Z\) and the second inequality of (3). The rate is the minimum of
\[
 I_\alpha(b)+(b\log2-1)_+,\qquad b\ge0.
\]
The function decreases up to \(b_0\) on the left; the right-hand derivative is \(\log(2b/\alpha)\), so the minimizer is \(\max(b_0,\alpha/2)\). The resulting exponent is \(I_\alpha(b_0)\) if \(\alpha\le2b_0\), and \(\alpha/2-1\) otherwise. For the lower bound for failure, take \(R=Y\), require \(M=1\) (probability \(\asymp L^{-3}\) by Mertens), and require
\[
 Q_Y=\lfloor \log_2 g\rfloor-2=b_0 L+O(\log L).
\]
For large \(m\), this is a positive integer. This event is independent of \(M\) and has probability \(m^{-I_\alpha(b_0)}L^{\pm O_\alpha(1)}\) by (6). Given these events, (3)'s union bound with the actual \(g\) says that even without a size cap the nonempty squarefree subsets hit identity with probability at most \(1/4+O_A(m^{-A})\). The previously charged unconditional repeated-prime error is negligible. Hence the lower bound for failure holds with exponent \(I_\alpha(b_0)\), proving parts 2 and 3. In particular we did not convert an absolute Gaussian approximation error into a relative tail estimate.

## Scope of exact checks

Run `node verify_erdos697_divisor_tail.js`. It exhaustively checks finite uniform-group hit moments/bounds, small periodic density examples versus the independently weighted valuations, and the conditional prime-set odds identity. The analytic estimates and the continuous minimizations are justified by the proof, not by this finite script.
