# A fixed-target signed rough-cofactor statistic for two genuine prime slots

Let \(P\) tend to infinity through even integers, \(C=[P/3,2P/3]\), \(L=\log P\), \(H=\log L\), and
\[
 {\mathfrak S}(P)=2\prod_{\ell>2}\left(1-\frac1{(\ell-1)^2}\right)
                 \prod_{\ell\mid P,\ \ell>2}\frac{\ell-1}{\ell-2},
 \qquad U=\mathfrak S(P)|C|/L^2 .
\]
Products indexed by \(\ell\) are over primes. Put \(w=H^3\), \(z_v=P^{1/v}\) for \(v=w,2w\), and take either a fixed \(0<\alpha<1/2\) or
\[
       \alpha=\tfrac12-\sigma,\qquad \sigma=H^{-7/4}.
\]
The least prime factor of 1 is infinity. With two **actual prime** slots define
\[
 T_v=\sum_{\substack{p+s q=P,\ p\in C,\ p,q\ {\rm prime}\\q>P^\alpha,\ P^-(s)>z_v}}
                 \frac{\log q}{L}.
\]
All sums are for the individual prescribed target \(P\), not a dyadic average.

**Theorem.** In either regime,
\[
 T_v=e^{-\gamma} U\{(1-\alpha)v+1\}+o(U),\qquad
 2T_w-T_{2w}=(e^{-\gamma}+o(1))U.
\]
For the displayed moving \(\alpha\), the same statements hold if \(q\) is required to be the only prime factor of \(P-p\) exceeding \(P^\alpha\); in particular it is the largest one. They also hold if one just takes \(q=P^+(P-p)>P^\alpha\). We do not replace the moving cutoff by exactly \(\sqrt P\).

On \(s=1\) the signed statistic counts the actual ordered central prime pairs with weights \(\log(P-p)/L\). A composite row with \(s>1\) carries the same positive weight if \(P^-(s)>z_w\), its negative if \(z_{2w}<P^-(s)\le z_w\), and zero otherwise. The theorem does **not** bound the signed excess of the first composite population over the second by less than \(e^{-\gamma}U\). Such a strict upper with a fixed margin at every sufficiently large even target would give a Goldbach representation; positivity of the signed statistic alone does not.

## Evaluating the term of order \(U\)

The few central primes \(p\mid P\) can be discarded throughout each physical statistic at cost \(O(\omega(P))\), since the sum of log-prime-factor weights is at most 1 per \(p\). On all remaining rows \(m=P-p\) is a unit modulo \(P\). In \(T_v\) the rough condition is equivalent to \(P^-(m)>z=z_v\), since the marked \(q>P^\alpha>z\). The total cost of replacing prime divisors by prime powers on these rows is \(O(P/z)\): a nonsquarefree rough \(m\le P\) is counted by \(\sum_{r>z}\lfloor P/r^2\rfloor\ll P/z\), and all prime-power log weights sum to \(\log m/L\le1\). This estimate also allows discarding prime squares in our near-half comparison.

Write \(X_0=\int_C dt/\log t=|C|/L\{1+O(1/L)\}\), and
\[
 V=\prod_{\ell\le z,\ \ell\nmid P}\left(1-\frac1{\ell-1}\right).
\]
We need the rough count \(R\) of central primes and the corresponding rough counts \(R_r\) with \(r\mid P-p\), for \(z<r\le P^\alpha\), \(r\nmid P\). In the latter case the unconditional prime-density multiplier is exactly \(1/(r-1)\); \(r\) is disjoint from all sieving primes. Here and below the rough counts mean the roughness of \(P-p\), not of \(p\); prime target-divisors may temporarily be kept in applying the prime theorem. Their contribution to any squarefree-divisor count of genuinely rough rows with the stated log weights is negligible. More directly, sift only primes not dividing \(P\); their sieve detects exactly the required rough indicator apart from the discarded prime target-divisors \(p\mid P\), and their aggregate log mass is as bounded above.

For either empty mark or the positive weighted sum of marks, truncate inclusion-exclusion at adjacent even/odd orders around \(12H\). For a model local prime use \(x_\ell=1/(\ell-1)\); its total is at most \(H+O(1)\). The difference of principal Bonferroni sums is at most \((H+O(1))^J/J!\) with \(J=12H+O(1)\), hence \(O(e^{-10H})\) by Stirling. Relative to \(V\gg1/L\) this is \(O(e^{-8H})\). Every physical progression is \(p\equiv P\bmod d\) or \(p\equiv P\bmod dr\), with reduced residue. The maximum modulus is
\[
              P^{\alpha+(12H+2)/v} < \sqrt P/L^B
\]
for each fixed \(B\) and sufficiently large \(P\); in the moving case \((12H+2)/v=o(\sigma)\). The moduli without a mark are shorter still. Ordinary maximal-residue Bombieri--Vinogradov and partial summation therefore give an arbitrary fixed-log total saving. Indeed a modulus in a marked sum has at most \(\tau(n)\) choices of its prime mark (in fact the unique factor exceeding \(z\)), and \(\log r/L\le1\); the usual divisor-weighted corollary follows by Cauchy with arbitrarily strong BV and the crude maximum \(O(P/n+1)\) times fixed divisor moments. Thus
\[
 \begin{split}
 R &= X_0V\{1+O(e^{-8H})\}+O_M(P/L^M),\\
 \sum_{z<r\le P^\alpha,\ r\nmid P}\frac{\log r}{L}R_r
 &=X_0V\{1+O(e^{-8H})\}
       \sum_{z<r\le P^\alpha,\ r\nmid P}\frac{\log r}{L(r-1)}
       +O_M(P/L^M).
 \end{split}
\]
Here the second display uses nonnegative mark weights when summing the separate lower and upper main terms. Adding or removing the excluded \(p\mid P\) costs \(O(\omega(P))\) outside the displayed analytic error. All these estimates are target-uniform.

On the central compact interval \(\log m/L=1+O(1/L)\). The **actual integer identity** \(\log m=\sum_{r^j\mid m}\log r\) now gives \(T_v\) from the first display minus the marked one, with extra error \(O(R/L+P/z+\omega(P))\). By Mertens, or the prime number theorem with classical error,
\[
     \sum_{z<r\le P^\alpha,\ r\nmid P}\frac{\log r}{r-1}
                 =\alpha L-\log z+O(1+L/z).
\]
For the deleted target primes use \(\sum_{r\mid P}\log r\le L\) and \(r>z\). Also, uniformly,
\[
 V=\frac{e^{-\gamma}\mathfrak S(P)}{\log z}
     \{1+O(1/\log z+1/z+L/z)\}.
\]
To see this divide by \(\prod_{\ell\le z}(1-1/\ell)\): the unrestricted correction is the absolutely convergent twin-prime product, and omitting the remaining target Euler factors costs \(O(\sum_{\ell\mid P,\ell>z}1/\ell)\). The relative error displayed is \(o(1/v)\), not just \(o(1)\). Combining these estimates leaves the term \(+\log z/L=+1/v\) inside \(T_v/(X_0V)\); all other errors there are \(o(1/v)\). This gives the asserted secondary term at the natural scale, with no averaging of \(P\).

## The near-half marked prime really is the largest, up to \(o(U)\)

If there are two distinct \(q_1,q_2>P^\alpha\) on a rough row, write \(P-p=b q_1q_2\), where \(b\le P^{2\sigma}\) and \(P^-(b)>z\). The marked \(q_1\) is in \([P^{1/2-\sigma},P^{1/2+\sigma}]\); there cannot be three primes above the cutoff. For each \(b,q_1\) with \((b q_1,P)=1\), apply the ordinary dimension-two Selberg upper-bound sieve to the two linear forms \(h,P-bq_1h\), with \(h=q_2\) in the actual interval \([P/(3bq_1),2P/(3bq_1)]\). This interval has length \(Y\asymp P/(bq_1)\ge P^{1/2-3\sigma}/3\). Its upper bound is
\[
  \ll \frac{P}{bq_1 L^2}\,\mathfrak S(P)\frac{bq_1}{\phi(bq_1)} .
\]
Indeed each squarefree sieve modulus has at most \(2^{\omega(j)}\) roots and error of that size; a fixed small power of \(Y\) is a valid sifting cutoff, with a power-saving total interval-remainder. At a prime dividing the target or the coefficient just one root replaces two; the ratio for an odd coefficient-prime is \((r-1)/(r-2)\), dominated multiplicatively by a constant times \(bq_1/\phi(bq_1)\). The factor at 2 is already included and \(b,q_1\) are odd. Both actual primes exceed the sieve cutoff.

The \(q_1\) reciprocal sum (including its totient ratio) is \(O(\sigma)\) by PNT uniformly in this logarithmically wide band. The remaining sum is bounded by \(O(1+\sigma v)\), by the Euler product for \(\sum_{P^-(b)>z,\,b\le P^{2\sigma}}1/\phi(b)\), including \(b=1\). Thus the total double-eligible cost is \(O(U\sigma(1+\sigma v))=o(U)\). Squared eligible primes were already removed. This does not discard rows with a *single* largest prime between \(P^\alpha\) and \(\sqrt P\).

## Interpretation and antecedents

The inputs are classical: [Bombieri, On the large sieve](https://doi.org/10.1112/S0025579300005313), elementary Bonferroni, Mertens, and the dimension-two upper-bound sieve. The large-factor method of [Goldfeld, On the number of primes \(p\) for which \(p+a\) has a large prime factor](https://www.math.columbia.edu/~goldfeld/PrimeShifts.pdf) is a direct antecedent of using a whole logarithm minus the small-prime logarithms, for fixed shift. Our statistic uses a prescribed macroscopic reflection, a varying rough cutoff, and the signed secondary term. The earlier [rough shifted-prime profiles](https://github.com/mxym/math/commit/63162fabe834dcb46efa6e34b57eecb05220c4f6) use first-moment inequalities for high- and low-largest-factor profiles; the present secondary term needs the finer absolute error \(o(U)\). No priority is claimed over the classical rough-number or shifted-prime methods.

Unlike just keeping the low-rank counts in the [true-prime masking benchmark](https://github.com/mxym/math/commit/0377f919d80825ba2d0740f8c902108de8b6f5b9), the signed statistic tests the literal log-divisor identity on the actual primes. In that construction the neutral deleted rows have at least one factor \(\le\exp(L/H^4)<z_{2w}\); they contribute zero. A deleted central prime cannot be the \(q\)-slot of any nontrivial cofactor here: \(P-p\le2P/3\), so an odd multiple \(s q\) with \(s>1,\ q\ge P/3\) is too large. Consequently on Goldbach-rich targets the two masks differ in this statistic on the whole prime-pair scale, even though their prescribed small-modulus, low-rank and auxiliary ledgers match. This distinguishes the statistic, not the sign of the remaining physical composite surplus.

