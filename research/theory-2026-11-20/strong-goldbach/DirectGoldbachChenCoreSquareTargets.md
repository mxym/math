# Both weighted Chen cores saturate on almost every even square

This extends the [dense-target computation](DirectGoldbachChenCoreSaturation.md) to targets \(N=4k^2\). The two upper caps from the [Chen discriminator](DirectGoldbachRepairedChenSemiprimeDiscriminator.md) still fail on relative density one of this thin arithmetic family. This is not an asymptotic at an individually prescribed square or at powers of two, and is not conditioned on the actual prime-pair count being small.

For either core weight \(c\), with \(H_c,I_c\) as in the dense-target note, and every fixed \(A>0\), all but \(O_A(\sqrt X/(\log X)^A)\) targets \(N=4k^2\in[X,2X]\) satisfy
\[
 H_c(N)=(I_c+o(1))\frac{\mathfrak S(N)N}{(\log N)^2}.
\]
In particular the constants \(I_W=1.421763588\ldots\) and \(I_C=1.394166883\ldots\) exceed the respective proposed caps \(0.6199\) and \(0.095\).

Use the same frozen angular weights, boundary cut \(Y=X/(\log X)^{10}\), and major arcs with denominator cap \(P=(\log X)^D\) as in the dense-target proof. Write \(F(\alpha)\) for the actual prime exponential sum and \(G_\pm(\alpha)\) for the two actual frozen semiprime sums. Both satisfy \(L^2\) norm \(O(\sqrt X)\), by Parseval; for the latter use the unique factorization with its smaller label below the upper cutoff and the larger label strictly larger on every retained row. The uniform major evaluation supplies
\[
 (\mathfrak S_P(N))(f*g_\pm)(N)+O(X/(\log X)^3)
\]
for *every* \(N\in[X,2X]\) by choosing \(D\) large enough. Here \(f,g_\pm\) are the continuous profiles and \((f*g_\pm)(N)=(I_c+o(1))N/(\log X)^2\) uniformly, as previously proved. No exponential estimate for the target sequence is used on major arcs.

## Signed selectors on squares

Write \(H=\sqrt X\). For arbitrary real \(|b_k|\le1\) supported on \(4k^2\in[X,2X]\), set
\[
 T(\alpha)=\sum_k b_k e(-4k^2\alpha).
\]
Then \(\|T\|_4^4\ll H^2(\log X)^2\). Indeed expand the fourth moment and take absolute values, reducing to the additive energy of the relevant squares. If \(r(m)\) counts differences \(x^2-y^2=m\) in this range then \(r(0)=O(H)\), and \(r(m)\le\tau(|m|)\) for \(m\ne0\) because the factorization \((x-y)(x+y)\) uniquely determines \(x,y\). Thus the nonzero energy is at most a constant times
\[
 \sum_{x>y}\tau(x^2-y^2)
 \le \sum_{x>y}\tau(x-y)\tau(x+y)
 \ll H^2(\log X)^2,
\]
using the injective change to difference and sum and the divisor harmonic bound.

For arbitrary \(M\), the prime exponential sum has \(\sup_{\rm minor}|F|\ll_M X(\log X)^{-M}\) when \(D\) is chosen large enough, by the same Vaughan estimate as in the dense theorem. Extracting half this sup and applying Hölder with exponents \(4,2,4\) to the other factors gives
\[
 \left|\int_{\rm minor} F G_\pm T\right|
 \le (\sup_{\rm minor}|F|)^{1/2}\|F\|_2^{1/2}\|G_\pm\|_2\|T\|_4
 \ll_M XH(\log X)^{1/2-M/2}.
\]
Take the selector signs equal to the signs of the real minor coefficients (these are real by symmetric arcs and real coefficients), supported on targets whose minor integral has magnitude greater than \(X/(\log X)^3\). The last bound makes their number \(O_A(H/(\log X)^A)\), after choosing \(M,D\) large enough.

## Singularity tails along squares

Only squarefree \(d\) occur in the singular series. For such \(d\), \(c_d(4k^2)=c_d(4k)\), since the relevant common prime divisors are the same and the Ramanujan divisor formula depends only on \((d,N)\). The total absolute tail for \(k\ll H\) is \(O(HP^{-1/2})\): an odd divisor \(e\) in that formula divides \(k\) in at most \(O(H/e)\) cases; an even squarefree \(e\) changes this bound by at most a factor of two. Sum the \(\tau(d)/\varphi(d)^2\) tail as in the dense-target proof. Markov at size \(1/\log X\) gives \(O(H\log X/\sqrt P)\) exceptional squares.

Combining the two estimates and squeezing between the frozen upper and lower convolutions proves the assertion. The fixed polynomial sequence [prime–prime exceptional-set results of Althöfer, Chen, Perelli and Pintz](https://arxiv.org/html/2611.09386v1) concern a different correlation; here both actual \(p+sr=N\) angular charges are treated with the same cutoffs as the Chen budgets. The argument supplies no pointwise control of the genuinely coupled prime-pair-deficit problem.
