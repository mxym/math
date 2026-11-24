# Möbius extension of the small-radical rough-layer parity bound

Use the notation and analytic inputs of [the companion rough Liouville proof](SmallRadicalRoughLiouville.md); in particular \(L=\log P,\ R=\operatorname{rad}(P)\le L^B,\ y=\exp(L^\delta)\) with fixed \(0<\delta<.1\), and a fixed compact interior interval \(I=PJ\). In addition to the Liouville result, the same relative estimate holds for Möbius:
\[
\left|\sum_{\substack{p\in I,\ p\ {\rm prime}\\ P^-(P-p)>y}}
          (\log p)\mu(P-p)\right|
\ll_{B,J,\delta} P V_y(P)/\sqrt{\log L}.
\tag{1}
\]
In the notation of [the earlier parity proof](small_radical_projection/Parity.md), use its unconditional Möbius BV estimate (3) and the same arbitrary-\(|b(h)|\le1\) reflected projection. The ordinary true-prime rough layer mass and relative mark variance are exactly those proved in §§1,3 of the Liouville proof. Here is the additional signed Type I argument, including the two squareful issues.

## 1. At the tag product \(u\)

Each tag \(u\) is squarefree (\(K\) distinct prime bands), and its primes are at least \(\exp(L^{.1})\), above \(y\). In \(P-n=uh\) the equality \(\mu(uh)=(-1)^K\mu(h)\) can fail only when some tag prime \(\ell\) divides \(h\), and then \(\ell^2\mid P-n\). The number of *all* \(n<P\) with this property is at most \(P\sum_{k\ge\exp(L^{.1})}k^{-2}\ll P\exp(-L^{.1})\). Before any Vaughan expansion the original and replaced marked sums differ by at most this count times \(L^{O_K(1)}\), as the tag weight bounds the total tag multiplicity for each \(n\) and \(\Lambda(n)\le L\). The extra rough mask only reduces that bound. Thus we may use the bounded residual \(\mu(h)1_{\{(h,R)=1,\ P^-(h)>y\}}\) in the marked sum, with arbitrary log-small error. The Type II estimate remains unchanged.

## 2. At the small divisor \(v\) in the second Bonferroni truncation

Apply the same two bounded-error Bonferroni replacements from the Liouville proof. They only require a residual of modulus at most one; in particular all their factorial and floor errors are unchanged for \(\mu\). After the retained substitution \(h=v h'\), the modulus \(v\) is squarefree, supported on primes \(\le y\), with \(\omega(v)\le h_0+1\), \(h_0=\lfloor L^{.1}\rfloor\), and \((v,deR)=1\). Instead of pretending complete multiplicativity use
\[
\mu(vh')=\mu(v)\mu(h')1_{\{(h',v)=1\}}
      =\mu(v)\sum_{t\mid h'}g_v(t)\mu(h'/t),\qquad
g_v(t)=\mathbf1_{\{\text{all primes dividing }t\text{ divide }v\}}.
\tag{2}
\]
The convolution identity is exact: at \(\ell\mid v\) the Euler factor \(1-\ell^{-s}\) of \(\mu\) is canceled by the geometric series, and at other primes it is unchanged. This identity can equally be verified prime-power by prime-power and multiplied; it does not mean \(h'\) itself is squarefree before projection.

Since \(t\) is supported on the primes of \(v\), \((t,deR)=1\) automatically. Substitute \(h'=t j\). The congruence for \(j\) is \(j\equiv P(uvt)^{-1}\pmod {de}\), with \((j,R)=1\). No inverse modulo \(de\) is invoked on a nonempty nonunit term.

Truncate the \(t\)-sum at \(H=\exp(L^{.4})\). The tail reciprocal cost, uniformly in all allowed \(v\), is
\[
\sum_{t>H}\frac{g_v(t)}t
\le H^{-1/4}\prod_{\ell\mid v}(1-\ell^{-3/4})^{-1}
\le\exp(-\tfrac14 L^{.4}+O(L^{.1})).
\tag{3}
\]
The last bound uses just the \(O(L^{.1})\) possible factors of \(v\), each factor in the product at most \((1-2^{-3/4})^{-1}\). For each fixed \(u,d,e,v,t\), the exact admissible \(j\)-count is bounded by \(O(P/(uvtde)+1)\), dropping the extra unit condition modulo \(R\). In the first part sum (3) against \(\sum_d1/d\), \(\sum_e1/e\), \(\sum_v1/v\) and the normalized \(\sum_u1/u\), all at most fixed powers of \(L\). Total coefficient and \(\log k\) losses are also fixed powers. In the floor part no such reciprocal factors are available, so count possible \(t\)'s: for each \(v\), \(t\le P\) can have at most \(1+\lfloor L/\log2\rfloor\) exponent choices at each of \(\omega(v)\) primes, giving \(\exp(O(L^{.1}\log L))=P^{o(1)}\) possibilities. The number of tuples including \(d,e,u,v\) is therefore still only \(P^{.4+o(1)}\). Both parts of the discarded signed expansion are \(O_A(P L^{-A})\).

For retained \(t\), for each fixed \(u,v,t\) the actual common \(j\)-endpoints are \(\asymp_J P/(uvt)=P^{1-o(1)}\) and the reduced modulus \(deR\) remains \(\le P^{.4+o(1)}\). The same finite sum over the at most \(R\) target-unit classes and distinct \(de\)'s is below the known \(x^{.46}\) Möbius BV range. In the logarithmic term partial summation uses \(\log(P-uvt j)-\log d\), whose nonconstant part has total variation \(O_J(1)\). Thus the error for this \(u,v,t\) is \(O_A((P/(uvt))L^{-A})\) after arbitrary fixed log losses. Sum in \(t\) using \(\sum_tg_v(t)/t=\prod_{\ell\mid v}(1-1/\ell)^{-1}\ll\log y\), in \(v\) using \(\sum_v1/v\ll\log y\), and in \(u\) using the tag normalizer. The marked Möbius sum is \(O_A(P L^{-A})\). The unmarking Cauchy argument on the same rough layer uses only \(|\mu|\le1\) and therefore yields (1).

## 3. Signs, and the remaining restriction

On the rough layer \(P^-(P-p)>y\), any violation of squarefreeness requires a prime \(\ell>y\) with \(\ell^2\mid P-p\). Its total \(\log p\)-mass is \(O(P L/y)\) by counting all integers, so the Möbius nonzero mass differs from the total rough mass by that negligible amount. From (1) and the Liouville companion, the prime-log mass of **each sign** for either \(\mu\) or \(\lambda\) is
\[
\tfrac12 |I|V_y(P) + O_{B,J,\delta}\big(PV_y(P)/\sqrt{\log L}\big).
\]
As before this does not control the triangular divisor kernel, \(\mu\)-weighted progression families, or rank one versus rank three. Neither sign distribution can imply a Goldbach pair from the bounds shown here.
