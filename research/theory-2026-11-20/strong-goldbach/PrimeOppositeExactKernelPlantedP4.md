# Exact prescribed small-factor profiles in the smaller P4 windows

Written corollary, 2026-11-24. This combines the [full asymmetric-kernel window theorem](PrimeOppositeExactAsymmetricP4Kernel.md) with the [existing exact-profile transfer](PrimeOppositePlantedSubSquareRootShortP4.md), keeping the genuine arithmetic progression on each source window.

Fix \(0<a<b\) and \(A>0\), and for each large even \(N\) set \(L=\log N\). Take \(I=(aN^{.4832},bN^{.4832}]\), or \(I=(x,x+N^{.4916}]\) for any \(x\in[a\sqrt N,b\sqrt N]\). Let \(Y=|I|\), \(X=\int_I du/\log u\). For positive integers \(d,m\) with \(M=dm\le L^A\), \(\operatorname{rad}(d)\mid m\), take \(r\bmod m\) with \((r,m)=(N-dr,M)=1\). Put
\[
 S_1=S_N\prod_{\substack{\ell\mid m\\\ell\nmid N}}(1-1/(\ell-1))^{-1},
 \qquad B_0=2XS_1/(\varphi(M)L).
\]
Then at least \((.005+o(1))B_0\) genuine primes \(p\in I\), \(p\equiv N-dr\pmod M\), have squarefree \(Q=(N-p)/d\) with all prime factors at least \(N^{.0393}\) and at most four of them. In particular \(Q\equiv r\pmod m\) and \(v_\ell(N-p)=v_\ell(d)\) for every \(\ell\mid m\). Uniformity is for fixed \(a,b,A\). The four-factor statement is for the quotient, not the full complement including \(d\).

**Proof.** For a squarefree quotient divisor \(e\) with \((e,m)=1\), the tests \(p\equiv N-dr\pmod M\), \(e\mid Q\) are the single class \(p\equiv N-dr\pmod M,\ p\equiv N\pmod e\); if a prime of \(e\) divides \(N\), exclude the source primes dividing \(N\) as before. Since every prime of \(d\) divides \(m\), the two moduli \(e,M\) are coprime. Combined test moduli are bounded by \(MD\) with \(D=N^{.24159}\), including the \(qe\) tests for small marked primes. This is still below the effective levels \(N^{.2416}\) and \(N^{.241595}\) minus logarithmic factors from the two source theorems. For fixed \(M\) the combined map is injective, and the estimates take the maximum over reduced classes; enlarging fixed logarithmic losses covers \(\varphi(M)\), arbitrary fixed divisor weights, and prime-power removal. The one-dimensional main mass becomes \(X/\varphi(M)\); primes of \(m\) never divide \(Q\) and are omitted from its sieve product, giving the factor \(S_1/S_N\).

Above the small-mark split, switch \(Q=qj\) and write \(j=j_0+mt\), \(j_0\equiv rq^{-1}\pmod m\). The physical \(t\)-interval has length \(Y/(Mq)\). All primes dividing \(M\) are at most \(L^A\), hence below \(z=N^{.0393}\) for large \(N\), and both tested forms \(j\) and \(p=N-dqj\) are nonzero at these primes by construction. At every other sieve prime the true roots have exactly the prior count, including collision at \(\ell\mid N\). The full two-root comparison Euler product consequently has singular factor
\[
 S_2=S_N\prod_{\ell\mid m}(1-\nu(\ell)/\ell)^{-1},
 \quad
 \nu(\ell)=\begin{cases}1&\ell\mid N,\\2&\ell\nmid N.\end{cases}
\]
The global full-denominator formula used for the kernel remains uniform: its Euler convolution proof now has exceptional primes only among divisors of \(NM\), for which the same absolute logarithmic moment bound holds since \(\log(NM)=O(L)\). The omitted primes are **all below \(z\)**, so none of the high-prime transition coefficients in the exact convolution changes. Thus the full switched denominator has the same kernel \(J(v)\), with normalization \((\log z)^2/S_2\). The earlier exact local identity \((\varphi(M)/M)(S_2/S_1)=1\) cancels the change in affine interval length versus the base \(B_0\), prime by prime. The large-mark factor \(\theta/(2\mu^2J(v))\) and the directed arithmetic margin stay unchanged. The aggregate Selberg floor is still \(O(N^{\rho-.00002}L^C)=o(B_0)\) since \(B_0\gg Y/L^{A+2}\).

Finally \(Q\) varies in an actual interval of length \(Y/d\) at scale \(N/d\). For a square divisor \(s^2\mid Q\), \(z\le s\le N^{1/3}\) costs \(O(Y/(dz)+N^{1/3})\). Above \(N^{1/3}\), use \(Q=cs^2\) with \(c\le N^{1/3}/d\): sum the \(s\)-lengths \(O(Y/\sqrt{Ndc})\) and unit floors to obtain \(O(Y/(dN^{1/3})+N^{1/3}/d)\). Both bounds are \(o(B_0)\). The original Richert inequality on squarefree \(Q\le N\) and the unchanged positive margin finish the proof. This preserves exact small profiles at the new window sizes, without implying P3.
