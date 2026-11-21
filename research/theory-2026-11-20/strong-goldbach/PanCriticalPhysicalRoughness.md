# Physical roughness localization of the full asymmetric Pan remainder at its original cutoff

Let \(P\) be a sufficiently large even target, \(L=\log P\), \(I=[P/3,2P/3]\), \(X=P/3\), and fix the actual cutoff \(Q=P^{1/2}L^{-20}\). Write \(r=P-n\), \(S(P)=2 C_2\prod_{\ell\mid P,\ell>2}(\ell-1)/(\ell-2)\) for the even Goldbach singular series, and let
\[
 A(n)=\sum_{d\mid n,d>Q}\mu(d)\log d,\qquad
 A^*(r)=\sum_{d\mid r,d>Q,(d,P)=1}\mu(d)\log d.
\]
These are the two coefficients, with their different unit rules, of [Pan's remainder as stated in Huang–Li (6)](https://arxiv.org/html/2005.03811v2#S1). For a set \(\mathcal E\) of primes put \(W=\prod_{\ell\in\mathcal E}\ell\), and let \(G_I\) count the true prime pairs in this interval with both log weights.

**Theorem.** Uniformly for **every** subset of the primes up to \(z=(\log L)^{5/2}\),
\[
 \sum_{n\in I,(nr,W)=1}A(n)A^*(r)
      =G_I-X S(P)+O(P L^{-1/5}).                                  \tag{1}
\]
In particular taking the difference with \(\mathcal E=\varnothing\) removes the entire complementary physical set with signed error \(O(P L^{-1/5})\). For the full choice of primes, at most \(O(P/\log z)\) physical integers survive, uniformly even for primorial-type targets: there is at least one forbidden class at each prime, and exact counting of classes modulo \(W\) costs at most \(W=\exp(O(z))=P^{o(1)}\). No restriction to marked divisors, individual moduli, common factors of the target, or a substituted square-root split is present. This is cancellation of the **sum**, not an estimate for the sum of absolute local coefficients. The remaining signed sum need not have either sign by this proof.

Put \(B(n)=-\sum_{d\mid n,d\le Q}\mu(d)\log d\), and define \(B^*\) by imposing \((d,P)=1\) also. If \(r_c\) is the largest divisor of \(r\) coprime to \(P\), then \(A=B-\Lambda\), \(A^*=B^*-\Lambda(r_c)\) exactly. We prove that the three rough sums for \(BB^*,\Lambda B^*,B\Lambda(r_c)\) are each \(XS(P)+O(PL^{-1/5})\). The remaining rough sum of \(\Lambda(n)\Lambda(r_c)\) equals \(G_I+O(P^{1/2+o(1)})\): large true prime inputs not dividing \(P\) force \((r,P)=1\), and all true pairs have both primes above \(z\). A true prime dividing \(P\) costs \(P^{o(1)}\) in all prime-input calculations. Actual higher prime powers \(n\) cost \(P^{1/2+o(1)}\) against a short-divisor sum, as do \(r=g p^j\), \(j\ge2\), \(g\mid P^\infty\): sum \(\sqrt{P/g}\,O(L)\) over \(g\mid P^\infty\), using \(\prod_{\ell\mid P}(1-\ell^{-1/2})^{-1}=P^{o(1)}\). This product bound follows e.g. by separating primes below and above \(\sqrt L\). All coefficients of an individual integer are \(P^{o(1)}\).

## 1. Uniform elementary sieve and short means

For prime inputs let \(V_1=\prod_{\ell\in\mathcal E,\ell\nmid P}(1-1/(\ell-1))\); for the two-integer input let
\[
 V_2=\prod_{\ell\in\mathcal E,\ell\nmid P}(1-2/\ell)
      \prod_{\ell\in\mathcal E,\ell\mid P}(1-1/\ell).
\]
There is no zero factor since \(2\mid P\). In all the sieves below the local densities \(0\le g(\ell)\le2/\ell\) or \(1/(\ell-1)\) at nondivisors of \(P\) have total \(O(1+\log\log z)\), uniformly in the target. With level \(D=L^b\), take adjacent even/odd integers \(J_+,J_-\) just below \(\log D/\log z\). Inclusion–exclusion through each gives upper/lower pointwise Bonferroni inequalities for the count *before* its possibly signed divisor weight. All represented squarefree products \(w\) of excluded primes satisfy \(w\le D\), with coefficients \(\mu(w)\) or zero. In the independent density model the error is at most a factorial moment
\[
 \frac{(\sum g(\ell))^J}{J!}\le L^{-2b/5+o(1)}.                 \tag{2}
\]
Indeed \(J=(2b/5+o(1))\log L/\log\log L\), and \(\log(J/(e\sum g))=(1-o(1))\log\log L\). This is an **absolute** error in the local density, not a presumed relative uniform approximation in a sparse class. No distribution theorem for all moduli as large as the full primorial \(W\) is used.

We use the uniform Euler estimates proved by convolution with the classical Möbius PNT in [the global rough transfer §1, (2)](PanGlobalRoughTransfer.md). Uniformly for the cut \(T\) between two fixed powers of \(P\) and \(m\le P^{O(1)}\), the \(\mu(f)\log f/f\) sum through \(T\) on \((f,m)=1\) is \(-m/\phi(m)+O_H(L^{-H})\); the no-log counterpart is \(O_H(L^{-H})\). For even modulus parameter \(m\), replacing denominator \(f\) by \(\phi(f)\) gives \(-S(m)+O_H(L^{-H})\) and zero main without log. Here and below union of the prime factors of \(P,W\) can be encoded by the even integer \(m=PW=P^{1+o(1)}\). Its Euler product satisfies **exactly** \(S(PW)=S(P)/V_1\). Two elementary relations we use are \(V_2 W/\phi(W)=V_1\) and \(\sum_{f\le P}1/\phi(f)\ll L\). Also \(P/\phi(P)\ll\log L\).

**Short–short.** The divisors \(d\mid n,e\mid r\) in this sum must be coprime to \(W\). Impose \((e,P)=1\), whence compatibility forces \((d,e)=1\). For each compatible pair the sieve density is \(V_2\): modulo a small prime, respectively two or one classes of \(n\) are forbidden. For the term \(w\mid nr\) in Bonferroni, counting by CRT gives the local density times \(X/(de)\), with an additive error \(O(2^{\omega(w)})\). Take \(b=16\). Summing the latter errors with both logs costs \(\ll Q^2 L^2 D(1+\log D)=P L^{-22+o(1)}\); the absolute factor multiplying (2) is \(O(PL^4)\). For the signed principal sum apply the first Euler estimate to \(d\) with \(m=eW\), then the second to \(e\) with \(m=PW\). The answer is \(X V_2 (W/\phi(W)) S(PW)=X S(P)\) with an arbitrary-log Euler error. All signed-weight sums here and below follow by summing the absolute errors of the positive sandwiches, not by multiplying one-sided inequalities by unspecified signs.

**Prime–short.** For the true prime \(p=n\), a short divisor \(f\mid P-p\) is coprime to \(PW\); for excluded small primes not dividing \(P\) sieve the single forbidden unit class. The modulus is \(fw\), and the representation as rough \(f\) (coprime to \(W\)) times \(w\mid W\) is unique. Use \(b=6\) and the explicit standard maximal-residue BV estimate in [R. C. Vaughan, *The Bombieri–Vinogradov theorem*, §1, pp. 2–3](https://personal.science.psu.edu/rcv4/Bombieri.pdf),
\[
 E(x,Y)\ll_H x(\log x)^{-H}+\sqrt{x}\,Y(\log(2xY))^6.          \tag{3}
\]
It applies to log-weighted primes, partial endpoints and the maximum reduced residue. Thus the summed arithmetic error with the log divisor weight is \(\ll L E(P,QD)\ll P L^{-7}\). The absolute coefficient of (2) is \(O(PL^2)\) at this step. The signed main is \(X V_1 S(PW)=XS(P)\).

## 2. The asymmetric prime factor, including large target-supported parts

In \(B(n)\Lambda(r_c)\) let \(r=g p\), \(g\mid P^\infty\), \(p\nmid P\) prime. Both roughness conditions force \((g,W)=1\), and \(p>z\) on the retained range. Drop \(g>P^{.05}\) at cost \(P^{.975+o(1)}\): the number of physical inputs is at most \(P\sum_{g>P^{.05},g\mid P^\infty}1/g\le P^{.975+o(1)}\) by the same tilted Euler product used above. Split a squarefree \(d\mid n\), \((d,W)=1\), uniquely as \(d=e f\) with \(e\mid\operatorname{rad}P\), \((f,PW)=1\). For \(n=P-gp\), the condition \(e\mid n\) is exactly \(e\mid g\). Write \(g=e t\); then \(t\mid P^\infty\), \((et,W)=1\), and \(f\mid n\) is precisely \(tp\equiv P/e\pmod f\). To sieve \(n\) against \(\mathcal E\), primes dividing \(P\) need not be included: \(g,p\) avoid every such small prime. Every remaining sieve divisor \(w\mid W\) is coprime to \(P f\), and the congruence becomes \(tp\equiv P/e\pmod{fw}\), a unit class. Its principal density over the prime and its independent local sieve density are \(1/\phi(f)\) and \(1/\phi(w)\). For fixed \(e,f\), we apply the positive sieve to the pooled nonnegative \((t,p)\) count, before taking the signed \(-\mu(ef)\log(ef)\) coefficient. This does **not** replace a sum of absolute BV errors at each large \(t\) by a smaller signed error.

Here is a quantitative justification of the simultaneous principal replacement at \(D=L^6\). For each \(e\le P^{.05}\), the unique split of every modulus \(q=fw\) noted above allows us to bound the accumulated arithmetic error by \(L\) times the sum over \(q\le Y=QD/e\), \((q,P)=1\), of the absolute progression errors of the pooled \((t,p)\) count. Its principal asymptotic is \(X/(e\phi(q))\sum_t1/t\). Permitted \(t\mid P^\infty\) satisfy \(et\le P^{.05}\), \((t,W)=1\); retain these restrictions literally. For \(t\le L^{13}\) use (3) at scale \(P/(et)\) with residue \((P/e)t^{-1}\bmod q\). Summing \(t^{-1/2}\) trivially up to \(L^{13}\), and \(e^{-3/2}\) over squarefree divisors of \(P\), costs only \(O(P L^{-13+6+13/2})=O(P L^{-1/2})\) in the second term of (3), already including the outer \(L\). The first term accepts arbitrary log losses. Removing the prime divisors of \(P\) does not in fact cost anything on this range for sufficiently large \(P\) except possibly a bounded number of large primes in \(P\): more generally removing them from the BV counts costs \(O(L)\) per modulus per small \(t,e\), a power saving. For the pooled large-\(t\) estimates below one can instead simply retain \(p\nmid P\) in every prime sum.

For \(t>L^{13}\) partition into dyadic bands \(t\asymp T\) with the exact endpoints retained. Put \(X_e=P/e\), \(U=X_e/T\); the prime lies in a fixed union of dyads \(p\asymp U\), \(U\gg P^{.95}\), because \(e t\le P^{.05}\) (enlarge constants at the last band). All these \(p\) exceed \(Y\), hence \((tp,q)=1\) automatically for every modulus under consideration, even after inducing characters. The principal character contributes \(X/(e\phi(q))\sum_t1/t\) by ordinary PNT at \(P/(e t)\), uniformly with arbitrary-log precision in aggregate; omit \(p\mid P\) at \(O(L)\) per \(t\) before dividing by \(\phi(q)\), still negligible. For the nonprincipal characters modulo \(q\), pass to their primitive conductors \(k\mid q\), \(k>1\), with cost
\(\sum_{l\le Y/k}1/\phi(kl)\ll L/\phi(k)\). At \(k\le L^{12}\) use Siegel–Walfisz in the prime at fixed \(t\), including both exact endpoints of \(etp\in I\); dropping prime divisors of \(P\) costs \(O(L)\) per \(t\). Multiplicity from all those characters, coinductions, \(e\), and harmonic \(t\) is at most a fixed log power in the \(P/e\) scale, so this is negligible.

For \(k\asymp H>L^{12}/2\), separate the sharp product interval by truncated Perron (use half-integer unscaled endpoints for the integer \(tp\), height \(P^5\), real part \(1/L\)). The coefficient \(L^1\)-norm of the separated integral is \(O(L)\); the pointwise cutoff error is \(O(P^{-3})\) on the dyads, since an endpoint is separated from an integer by at least \(1/2\), and summing even over characters and original terms is harmless. The twists have bounded amplitude. The multiplicative large sieve for primitive characters and Cauchy–Schwarz give on a \((T,H)\) block, with weight \(1/\phi(k)\), before Perron and coinduction costs,
\[
 \ll \frac{\sqrt{(T+H^2)(U+H^2)}}{H}\sqrt{T U L}
 \ll L^{1/2}\left( X_e/H+X_e/\sqrt T+X_e/\sqrt U+H\sqrt{X_e}\right).     \tag{4}
\]
The two squared coefficient norms are at most \(T\) and \(O(U L)\), by boundedness of the sparse target-supported indicator and Chebyshev for the prime log weight. No Siegel–Walfisz property of this indicator is presumed. Charge \(L^{11/2}\) altogether: the \(L^{1/2}\) in (4), a factor \(L\) each for the log-divisor coefficient, coinduction, Perron, and each of the two dyad sums. Thus with \(T\gg L^{13}, H\gg L^{12}, H\le Y\), the sum over \(e\mid\operatorname{rad}P\) is \(O(P L^{-1+o(1)})\): \(\sum_{e\mid\operatorname{rad}P}1/e\ll\log L\), and \(Y\sqrt{X_e}\le P L^{-14}/e^{3/2}\). These estimates verify the claimed principal replacement without using prime BV at scale \(P/(et)\) when \(t\) is too large for it.

The absolute principal mass against the sieve error (2) is at most \(O(P L^2(\log L)^2)\): use \(\sum_{e\mid\operatorname{rad}P}1/e\ll\log L\), \(\sum_{t\mid P^\infty}1/t=P/\phi(P)\), and \(\sum_{f\le Q/e}\log(ef)/\phi(f)\ll L^2\). This costs \(P L^{-2/5+o(1)}\). The signed principal expression becomes
\[
 -X V_1\sum_{g\le P^{.05},\ g\mid P^\infty,(g,W)=1}\frac1g
       \sum_{e\mid\operatorname{rad}g}\mu(e)
       \sum_{f\le Q/e,(f,PW)=1}\frac{\mu(f)\log(ef)}{\phi(f)} .
\]
The last sum is \(-S(PW)+O_H(L^{-H})\) uniformly, since \(Q/e>P^{.44}\) and the constant \(\log e\) multiplies a vanishing no-log mean. Every \(g>1\) is now annihilated by its **complete** \(e\)-sum. The errors summed with \(\sum_{g\mid P^\infty}2^{\omega(g)}/g\ll(\log L)^2\) stay negligible. The only main is \(XS(P)\) at \(g=1\). This finishes (1).

**Scope and antecedents.** Pan's original decomposition and unrestricted main terms precede this note. The [fixed subcritical rough transfer](PanGlobalRoughTransfer.md) reaches a fixed power for the roughness cutoff at the price of changing the divisor cutoff to \(P^v\), \(v<1/2\); that proof does not imply (1) at the original split. Results for a triangular Möbius switch with the roles of the factors changed do not give this physical claim for \(A A^*\). Here the ordinary, not GRH, large sieve repairs the target-supported factor in the asymmetric coefficient at the critical split. The result detects no positive prime-pair surplus, including on the remaining rough set.

## Related 2026 work

[Pham's October v1](https://www.preprints.org/manuscript/202610.3061) contains separate mixed-rough and balanced rough benchmarks. The [Li–Liu formalization overview](https://subfish-zhou.github.io/goldbach-lean/report/index.html) uses Pan-type convolution distribution for an almost-prime sieve, not this physical mask on the asymmetric remainder. The present result is specifically the signed removal of the complementary physical points at the original divisor cutoff, with a small rough cutoff; it makes no claim about parity balance on what remains.
