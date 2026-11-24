# Liouville cancellation at each small-radical target within a specified rough complement layer

This extends the arithmetic conclusion of the repository's [small-radical parity proof, §§1–3](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/small_radical_projection/Parity.md), using its deep analytic inputs as prior theorems. The new operations are a second truncated sieve in the Type I terms and a relative unmarking variance on the *actual rough layer*. It proves a cancellation within that layer, not the full signed divisor kernel or binary Goldbach. The statement here is for Liouville only.

## 1. Statement and inputs

Fix \(B>0\), a nondegenerate compact interval \(J\subset(0,1)\), and \(0<\delta<1/10\). Let \(P\) be a sufficiently large prescribed even target, \(L=\log P,\ R=\operatorname{rad}(P)\le L^B\), \(I=PJ,\ y=\exp(L^\delta)\). Let \(P^-(1)=+\infty\) and let \(\lambda(n)=(-1)^{\Omega(n)}\). Set
\[
V_y(P)=\prod_{\substack{\ell\le y,\ \ell\ {\rm prime}\\\ell\nmid P}}\left(1-\frac1{\ell-1}\right).
\]
Then, uniformly in these individual targets,
\[
\begin{aligned}
\sum_{\substack{p\in I,\ p\ {\rm prime}\\ P^-(P-p)>y}}\log p
  &= |I| V_y(P)+O_{A,B,J,\delta}(P L^{-A}) \qquad(A>0),\\
\left|\sum_{\substack{p\in I,\ p\ {\rm prime}\\ P^-(P-p)>y}}
                 (\log p)\lambda(P-p)\right|
  &\ll_{B,J,\delta} P V_y(P)/\sqrt{\log L}.
\end{aligned}
\tag{1}
\]
Moreover \(V_y(P)=(1+o(1))e^{-\gamma}S(P)L^{-\delta}\) uniformly on this family, with the genuine target-dependent Goldbach singular series. Indeed \(R\le L^B<y\), and multiplying/dividing by the Mertens product over primes \(\le y\) gives the exact local factor \(p/(p-1)\) at each \(p\mid P\) and \(1-1/(p-1)^2\) at remaining \(p\le y\). The omitted latter factors have product \(1+O(1/y)\) by summing \(1/(p-1)^2\). In particular \(V_y\gg L^{-\delta}\); it is not in general equal to a target-independent constant times \(L^{-\delta}\) with ratio bounded above independently of \(P\).

Use the inputs already established in the earlier parity note: ordinary true-prime Bombieri–Vinogradov; the Liouville BV estimate (3) there to \(x^{.46}\) in reduced classes, including \(q=1\); and the bounded-residual Type II comparison used in (4). For precision, the last input is the explicit sentence in the [full-target projected minor theorem](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/target_slope_switch/Proof.md), §1, that a dyadic bilinear sum against an arbitrary residual \(|b(h)|\le1\) is bounded by \(O((X/Y)^{1/2})Q^{1/2}\). The companion [small-radical projected major estimate](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/small_radical_projection/Proof.md), §2, bounds that same comparison term for its \(\mu\)-slot and bounded other slot. The lead masks and the tag-band parameters used below are unchanged from the owner parity theorem.

## 2. Marked cancellation with the new layer

Set \(z=\exp(L^{.24})\). For any admissible fixed-\(K\) tag family \(\mathcal T\) from the earlier parity theorem, let \(\mathcal V=\sum_{u\in\mathcal T}1/u\) and \(W(h)=\mathcal V^{-1}\sum_{u\in\mathcal T,u\mid h}1\). The tag primes lie in bands strictly between \(\exp(L^{.1})\) and \(\exp(2L^{.2})\); in particular they exceed \(y\) and are coprime to \(P\). We prove
\[
\sum_{\substack{p\in I,\ p\ {\rm prime}\\ P^-(P-p)>y}}
             (\log p)\lambda(P-p)W(P-p)
=O_{A,B,J,\delta,K}(P L^{-A}),
\tag{2}
\]
for every prescribed \(A>0\), choosing a sufficiently large fixed \(K\) as in the Type II theorem, uniformly in all admissible families of that \(K\).

Replace the prime slot by \(\Lambda(n)1_{\{P^-(n)>z\}}\) on \(I\). It adds only proper prime powers, at cost \(P^{1/2+o(1)}\), since the pointwise tag multiplicity is \(L^{O_K(1)}\); it removes no actual prime in a fixed interior interval. For every resulting \(n\), target-unit condition follows from \(R<z\). In each expansion \(P-n=uh\), one has \((h,R)=1\), the new roughness condition becomes \(P^-(h)>y\), and \(\lambda(uh)=(-1)^K\lambda(h)\) by complete multiplicativity with no coprimality hypothesis. Thus the new residual is
\[
b(h)=\lambda(h)1_{\{(h,R)=1\}}1_{\{P^-(h)>y\}},
\]
whose absolute value is at most one. In the Type II part of the same Vaughan expansion at \(P^{1/5}\), no changes to the type of coefficients, required source roughness, separation or counting of \(h\) occur. The cited arbitrary-residual comparison and its small-radical major bound prove the same \(O_A(P L^{-A})\) as Parity.md §2, with the same smooth shells and endpoint approximation. The short supported Vaughan term is still absent in \(I\).

Here is the change in Type I. In the notation of the earlier proof, \(n=d k\), \(d\le P^{.4}\) is \(z\)-rough, the grouped coefficient is \(O(L)\), and the extra logarithmic multiplier on the first term is \(\log k\). Let \(h_0=\lfloor L^{.1}\rfloor\). First open the \(z\)-rough condition on \(k\) by Bonferroni inclusion–exclusion through \(h_0\) small prime factors, with modulus \(e\mid k\), \(e\) squarefree and \(e\le\exp(O(L^{.34}))\). Keep \(b(h)\) exact for this first replacement. The preceding proof bounds its error with only \(|b(h)|\le1\), after dropping the new roughness restriction. The retained equation is
\[
de\mid P-u h,\qquad (h,R)=1.
\]
Then open the \(y\)-rough condition on \(h\) through \(h_0\) small prime factors, using \(v\mid h\) squarefree, \(v\le\exp(O(L^{\delta+.1}))\), and setting \(h=v h'\). If a prime divides both \(v\) and \(de\), it divides \(P\) by the retained equation, contrary to \((h,R)=1\). Similarly \((de,R)=1\) follows from \(de\mid P-u h\) and \((u h,R)=1\), and \((de,u)=1\) since any common prime would divide \(P\) but \(u\) is a unit. Thus every nonempty term has \((de,uvR)=1\), \((v,R)=1\), and
\[
h'\equiv P(uv)^{-1}\pmod{de},\qquad (h',R)=1,\qquad \lambda(h)=\lambda(v)\lambda(h').
\tag{3}
\]

For detail at the second Bonferroni boundary, its absolute error after fixing \(u,d,e\) is bounded by the sum of \(O(P/(u d e v)+1)\) over squarefree products of exactly \(h_0+1\) primes \(\le y\); this count follows from the coprimality and the CRT just proved. There are at most \(P^{.4+o(1)}\) tuples of \(u,d,e,v\), even before dividing by the fixed tag normalizer, so all floor errors are negligible after fixed log losses. The other terms use \(\sum_d 1/d\ll L\), \(\sum_e1/e\ll\log z\), the exact \(\sum_u1/u=\mathcal V\), and
\[
\sum_{\omega(v)=h_0+1,\,p\mid v\Rightarrow p\le y}\frac1v
\le \frac{(C\log L)^{h_0+1}}{(h_0+1)!},
\]
which beats every fixed inverse log power. This second error is therefore \(O_A(P L^{-A})\) even after the first inclusion–exclusion's retained coefficients. The elementary Bonferroni bound used here holds pointwise: the difference between the exact zero-divisor indicator and the truncation at level \(h_0\) is bounded in modulus by the count of subsets of \(h_0+1\) distinct dividing primes.

For the finite retained sum in (3), impose \((h',R)=1\) by CRT, where \(deR\) is the resulting modulus and each of at most \(R\) classes is reduced. For each fixed \(u,v\), the actual endpoints for the \(h'\)-sum are determined by \(P-u v h'\in I\), hence on a scale \(x\asymp_J P/(uv)=P^{1-o(1)}\) common to all \(d,e\). The modulus bound \(deR\le P^{.4+o(1)}\le x^{.46}\) holds uniformly. From a modulus recover \(de\) by dividing by \(R\), and then \(d,e\) by their opposite prime ranges at \(z\); there is no hidden multiplicity. The Liouville BV theorem pays the summed progression error with arbitrary fixed powers of \(L\), absorbing the \(R\le L^B\) unit variants and coefficient size. For the \(\log k\) multiplier use
\[
\log k=\log((P-u v h')/d).
\]
Its endpoint size is \(O(L)\) and derivative \(O_J(uv/P)\) for all \(d,e\) on the common interval; equivalently split it as \(\log(P-uv h')-\log d\) before partial summation. Then the aggregate BV applies at each common endpoint, with total variation \(O_J(1)\) for the nonconstant part. Sum the resulting error over \(u,v\) by \(\mathcal V\) and \(\sum_v1/v\ll\log y\), respectively. This proves (2).

## 3. Relative unmarking: measure the variance on this same layer

Use the earlier construction of \(J_0\asymp_K\log L\) fully disjoint tag families, with \(W_j\) their normalized weights and \(\bar W=J_0^{-1}\sum_j W_j\). Define \(M_y(F)=\sum_{p\in I,\ p\ {\rm prime},\,P^-(P-p)>y}(\log p)F(P-p)\). The required bound is
\[
M_y(|\bar W-1|^2)\ll_{B,J,\delta,K}|I|V_y(P)/J_0+O_A(P L^{-A}).
\tag{4}
\]
Using the old unrestricted \(P/J_0\) bound without the extra \(V_y\) would lose a square root of the rough density and would not suffice for a relative saving.

Each nonnegative moment \(M_y(1),M_y(W_j),M_y(W_jW_k)\) expands into prime-log progression counts with modulus \(s=1\), a tag product, or the least common multiple of two tag products. All prime factors of \(s\) exceed \(y\) and are target units. The rough layer now adds divisibility tests at the primes \(\ell\le y\) not dividing \(P\); primes dividing \(P\) never divide \(P-p\) for actual \(p\in I\) since \(R\le L^B\). Apply the pair of consecutive upper/lower Bonferroni polynomials through \(h_0\) or \(h_0+1\) small prime factors. In the resulting terms \(e\) is squarefree supported below \(y\), and the actual prime progression is \(p\equiv P\bmod s e\). The modulus is \(P^{o(1)}\) and reduced. The small factor \(e\) is unique given \(s e\); the tag expansion multiplicity is bounded by \(2^K\) within one family and one across distinct families, as in the earlier second moment proof. After normalization the coefficients are \(O_K(1)\). Thus ordinary prime-log BV, applied to both ends of \(I\), pays the algebraic error by \(O_A(P L^{-A})\) for every such moment, uniformly in family indices. In the model \(\phi(s e)=\phi(s)\phi(e)\) exactly. Its successive Bonferroni bracket is a bracket for \(V_y(P)\) using independent probabilities \(1/(\ell-1)\). The truncation tails are \(O_A(L^{-A})\) by the factorial estimate with \(\sum_{\ell\le y}1/(\ell-1)=O(\log L)\). This proves
\[
\begin{aligned}
M_y(1)&=|I|V_y(P)+O_A(P L^{-A}),\\
M_y(W_j)&=|I|V_y(P)c_j+O_A(P L^{-A}),\\
M_y(W_jW_k)&=|I|V_y(P)c_{jk}+O_A(P L^{-A}),
\end{aligned}
\]
where \(c_j=\mathcal V_j^{-1}\sum_{u\in\mathcal T_j}1/\phi(u)=1+O_K(e^{-c L^{.1}})\), \(c_{jk}=c_j c_k\) if \(j\ne k\), and \(c_{jj}=O_K(1)\). The last bound follows by the same per-color lcm factor as in the earlier proof, \(\sum_r1/(r-1)+(\sum_r1/(r-1))^2\), divided by normalized reciprocal masses bounded below. The normalized second moment \(M_y(|\bar W-1|^2)\) therefore has only \(O(J_0^{-1})\) diagonal loss and negligible distinct-family errors, proving (4). This computation also proves the main mass estimate in (1).

Average (2) over \(j\); to remove the marks, Cauchy–Schwarz and \(|\lambda|=1\) give an error bounded by \(M_y(1)^{1/2}M_y(|\bar W-1|^2)^{1/2}\ll PV_y(P)/\sqrt{J_0}\), absorbing arbitrary log-small errors because \(V_y\gg L^{-\delta}\). This proves the relative cancellation in (1).

## 4. Scope

The sign cancellation here is for rough complements as a whole at each small-radical target, with any one fixed \(0<\delta<.1\). It is not a statement about the complementary Möbius sum on each arithmetic progression, or the full signed kernel in GlobalRoughLocalization.md or RoughLayerIteration.md. Multiplication by the signed/triangular divisor kernel or an \(O(L)\) factor would lose the asserted relative saving. Even a negative Liouville sign on rough rows can come from three or more prime factors. No claim of new Goldbach representations follows. In particular this note does not assert the Möbius variant: the reindexing \(\mu(v h')\) for squarefree \(v\) needs an extra \((v,h')=1\) analysis (or separate controlled local-inverse dilation tail), while \(\lambda(vh')=\lambda(v)\lambda(h')\) used here is exact.
