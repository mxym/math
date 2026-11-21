# Joint square-part and small-factor projection for the actual prime–composite row

Use the same \(P,I,X,L,Q=\sqrt P L^{-20}, B,B^*,S(P)\) as in [the critical physical roughness result](PanCriticalPhysicalRoughness.md). Write \(s(r)=\prod_{\ell}\ell^{\lfloor v_\ell(r)/2\rfloor}\), the positive root of the largest square dividing \(r\). For any subset \(\mathcal E\) of primes \(\le z=(\log L)^{5/2}\), put \(W=\prod_{\ell\in\mathcal E}\ell\). Define the signed mass
\[
 T_k=\sum_{p\in I,\ p\ {\rm prime},\ r=P-p,\ (r,W)=1,\ s(r)=k} (\log p) B(r).
\]
Then at **every** sufficiently large even target, uniformly in \(\mathcal E\),
\[
 |T_1-X S(P)|+\sum_{k>1}|T_k|\ll P L^{-1/8}.                  \tag{1}
\]
In either true physical prime–composite orientation of \(A(n)A^*(P-n)\) the sign reverses; the errors from genuine higher prime powers and prime inputs dividing \(P\) are negligible even in total variation. The statement permits *arbitrary bounded tests of the whole square part*, varying with the target and the small-factor filter. It does not take absolute values separately at each physical prime input.

The unmasked squarefree principal term itself is a direct antecedent: [Huang–Li, (12)–(15), §3.1](https://arxiv.org/html/2005.03811v2#S3.SS1) explicitly remove the squarefree mask from their short-divisor main using a square-divisor expansion and a prime distribution hypothesis, and credit Murty–Vatwani for the switch. Here the new scope is the square-part total variation together with the simultaneous prime-subset sieve at the **specified** fixed critical log cutoff, with its log losses charged.

**Proof.** Let \(|F(k)|\le1\) be arbitrary, \(h=\mu*F\) (Dirichlet convolution). Exactly \(F(s(r))=\sum_{t^2\mid r}h(t)\), \(|h(t)|\le\tau(t)\), \(h(1)=F(1)\). Drop prime labels \(p\mid P\) at total \(P^{o(1)}\), so \((r,P)=1\) and \(B^*(r)=B(r)\) thereafter. These exceptions can also be discarded *after* expansion at the same cost, by the maximal divisor bound. Put \(T=L^{13/4}\).

For \(t>T\) we now **only in the absolute tail** drop primality of \(P-r\), bound both log weights by \(L\), and drop roughness. Since \(\tau(t^2 u)\le\tau(t^2)\tau(u)\),
\[
 \sum_{t>T}|h(t)|\sum_{t^2\mid r,\ r\le P}L^2\tau(r)
 \ll P L^3\sum_{t>T}\frac{\tau(t)\tau(t^2)}{t^2}
 \ll P L^{-1/4+o(1)}.
\]
For the last bound, the elementary divisor estimate \(\tau(t)\tau(t^2)\ll_\xi t^\xi\) for each fixed \(\xi>0\) suffices. No such omission of the prime condition is made in the retained mass.

For \(t\le T\) necessarily \((t,PW)=1\). In the short sum over \(z\)-sieved divisors (i.e. \((d,W)=1\), not exclusion of additional primes outside \(\mathcal E\)) split \(d=jf\), where \(j\mid\operatorname{rad}t\), \((f,tPW)=1\), \(f\le Q/j\). The large prime input must satisfy \(p\equiv P\pmod{t^2 f}\). Sieve \(r\) by the excluded small primes not dividing \(P\) with the two Bonferroni truncations of §1 of the critical roughness proof at \(D=L^6\). Positive counts are sandwiched before the signed coefficient. Each small sieve divisor \(w\) is coprime to \(t f P\). The exact joint modulus is
\[
 q=[t^2,dw]=t^2 f w;
\]
primes of \(j\mid\operatorname{rad}t\) add no exponent. Both \(f,w\) are squarefree and coprime to each other, so **the full square part of the modulus recovers \(t=s(q)\)**, including when \(t\) itself is not squarefree. The factors outside \(t^2\) from \(\mathcal E\) recover \(w\) uniquely. Only \(j\) can vary, among at most \(\tau(t)\) choices. With \(|h(t)|\le\tau(t)\) the total multiplicity loss is \(L^{o(1)}\) since \(t\le T\), not a power of \(T\). The progression \(p\equiv P\pmod q\) is reduced. The explicit maximal BV inequality (3) of the critical roughness proof now bounds both truncations' arithmetic errors, including the actual divisor log, by
\[
 L^{1+o(1)} E(P,Q T^2D)\ll P L^{-1/2+o(1)}.
\]
Here \(QT^2D=\sqrt P\,L^{-7.5}\); the explicit \(L^6\) cost of BV matters. Dropping the exceptional \(p\mid P\) inside those finite sieve sums is also harmless, since any such prime in the original physical interval has at most \(P^{o(1)}\) compatible divisors of \(r=P-p\), including all \(t,j,f,w\). One may equivalently keep these primes in the unrestricted progression count and pay that error after expansion.

The independent model has the sieve factor \(V_1=\prod_{\ell\in\mathcal E,\ell\nmid P}(1-1/(\ell-1))\), up to absolute error \(L^{-12/5+o(1)}\) by the finite factorial estimate (2) of the critical roughness proof. Its aggregate unsigned prefactor is
\[
 \ll X\left(\sum_{t\ge1}\frac{\tau(t)^2}{\phi(t^2)}\right)L^2\ll PL^2,
\]
since \(\sum_{f\le P}1/\phi(f)\ll L\) and the \(t\)-series converges absolutely. Consequently the post-sieve signed main is
\[
 -X V_1\sum_{t\le T,(t,PW)=1}\frac{h(t)}{\phi(t^2)}
 \sum_{j\mid\operatorname{rad}t}\mu(j)
 \sum_{f\le Q/j,(f,tPW)=1}\frac{\mu(f)\log(jf)}{\phi(f)}.
\]
Uniformly the inner Euler mean is \(-S(tPW)+O_H(L^{-H})\), independent of \(j\), by the uniform Euler estimates in the linked proof; \(Q/j\) remains between fixed powers of \(P\), and \(tPW=P^{1+o(1)}\). Every \(t>1\) main thus vanishes. At \(t=1\) we get \(X F(1)V_1 S(PW)=X F(1) S(P)\). This establishes the claimed uniform dual bounded-test estimate, hence its equivalent total variation form (1) by choosing the signs of the finitely many coordinates.

Finally a large prime partner \(r\) has \(B(r)=0\); on a composite which is not a prime power \(A(r)=B(r)\). Proper powers have total \(P^{1/2+o(1)}\) absolute correction, and the starred orientation is identical on \((r,P)=1\). This verifies exactly the sign and physical row interpretation. Formula (1) does not assert the relative abundance of either Möbius sign among the squarefree partners or any inequality for the surviving prime-pair atom.

[Pham's October v1](https://www.preprints.org/manuscript/202610.3061) also treats a repeated-prime correction in the variance of a different sharp boundary component. This note is a total-variation statement on the actual square part of the complete mixed row. It does not estimate the squarefree row with an additional Möbius sign or yield a prime-pair count.
