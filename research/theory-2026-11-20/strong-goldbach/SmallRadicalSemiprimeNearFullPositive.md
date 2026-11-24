# A true positive shifted high-term library: a semiprime plus tagged near-full prime

The statement proved here does not require translated coverage. It provides actual favorable rows for the unmarked shifted high coefficient, with genuine ranks and a quantitative lower bound. A marked coverage removal can be attempted separately. It does not pay any adverse same-parity library or prove Goldbach.

## 1. Statement

Fix \(B>0\), an interior interval \(I=PJ\) with fixed nondegenerate compact \(J\subset(0,1)\), sufficiently large prescribed even \(P\) with \(\operatorname{rad}(P)\le L^B,\ L=\log P\), and the usual \(S(P)>0\). Let \(\mathcal T\) be an admissible family of products of \(K\) true primes, one from each full tag band as in the small-radical reflected projection, with \(K\) a sufficiently large fixed **even** integer. Its reciprocal mass \(\mathcal V=\sum_{u\in\mathcal T}1/u\) lies between \((1/4)^K\) and \((1/2)^K\). Every tag's primes lie between \(\exp(L^{.1})\) and \(\exp(2L^{.2})\), coprime to \(P\).

There are \(\gg P S(P)/L^2\) distinct actual rows
\[
P=pq+u r,\quad pq\in I,\quad p,q,r\ {\rm genuine\ primes},\quad
P^{.32}\le p\le P^{.35},\quad q>p,\quad u\in\mathcal T,\quad r=P^{1-o(1)}.
\tag{1}
\]
No translated first-cover requirement is imposed in this theorem. On these rows \(n=pq\) is squarefree rank two with all factors \(>P^{1/4}\); \(m=ur\) is squarefree odd rank \(K+1\), with \(P^-(m)>\exp(L^\delta)\) for any fixed \(\delta<.1\). Consequently the genuine shifted high source coefficient \(T(n)=-\log n\) from [the smooth source proof](SmallRadicalShiftedHighChambers.md) has \(T(n)\lambda(m)=+\log n\), and the sum of these actual positive weights is \(\gg P S(P)/L\). This positivity does not invoke or establish any relation between separate source libraries.

## 2. Centering a genuine prime factor rather than claiming a \(\Lambda\) consequence of Möbius cancellation

Put \(z=\exp(L^{.24})\), \(R_z(n)=1_{\{P^-(n)>z\}}\), and \(\kappa_z=\prod_{\ell\le z}(1-1/\ell)\). On an interval contained in \([X,1.1X]\) with \(P^{\epsilon_0}\le X\le P^{1-\epsilon_0}\) for fixed \(\epsilon_0>0\), define
\[
\alpha(n)= w(n)-\kappa_z^{-1}R_z(n),
\qquad w(n)=(\log n)1_{\{n\ {\rm prime}\}},
\]
and set it zero off that interval. Thus \(\alpha\) has \(z\)-rough target-unit support and size \(O(L)\).

**Claim.** For all fixed \(A,D_0,C>0\), all characters \(\chi\) modulo \(Q=P d\) or \(4P d\) with \(d\le L^{D_0}\), all subintervals in the stated box, and all real \(|t|\le L^C\),
\[
\left|\sum_{n\in J_X}\alpha(n)\chi(n)n^{it}\right|\ll X L^{-A}.
\tag{2}
\]
In particular multiplying by any low conductor character through its lift, or conjugating the large character, stays in this family. The cutoff \(z\) is fixed by \(P\), not by a moving endpoint.

Here are the analytic inputs and the verification.

* **Genuine primes against nonprincipal characters.** The [small-radical projected proof, §1](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/small_radical_projection/Proof.md) uses Iwaniec's zero-free theorem at conductor \(f\mid Q\) with \(\operatorname{rad}(f)\le L^{B+D_0+O(1)}\), and proves in its reciprocal-bound argument the uniform estimate \(|L'/L(\sigma+it,\psi)|\ll\Theta\) for the inducing primitive nonprincipal \(\psi\), \(\sigma\in[1-\theta/2,1+\theta]\), \(|t|\le T=L^J\), where \(\Theta\asymp L^{3/4}(1+\log L)^2\), \(\theta=\Theta^{-1}\). Use that logarithmic-derivative estimate **on its own** for \(-L'/L\), not the earlier Möbius coefficient conclusion. There is no pole at 1 for nonprincipal \(\psi\). The possible exceptional real zero is excluded in this strip by the same ineffective argument: primitive real \(f\le4\operatorname{rad}(f)\), so \(f\) is polylogarithmic and Siegel's theorem with small fixed exponent keeps \(1-\beta\gg L^{-1/4}\). Thus no unproved or uniformly effective Siegel-zero input is used. At a half-integer \(x\asymp X\), truncate Perron for \(\Lambda\psi\) on \(1+1/\log x\) with error \(O(xL^2/T)\), by the standard Perron kernel and \(\Lambda(n)\le\log n\). Move to \(1-\theta/2\). The vertical segment is \(O(x\Theta\log(2T)e^{-\theta\log x/2})\); the horizontals are \(O(x\Theta/T)\). As \(\log x\gg L\), this is arbitrary log-small by choosing \(J\) large. Imprimitive corrections affect only powers of primes dividing \(Q\) and cost \(O(L^2)\); proper prime powers in the full \(\Lambda\)-sum cost \(O(\sqrt x\log^2 x)\). Thus the true prime \(w\)-sum against \(\chi\) is \(\ll_A XL^{-A}\) on arbitrary subintervals by subtracting endpoints.
* **Rough integers against nonprincipal characters.** Open \(R_z\) by Bonferroni through depth \(D_1\log L\) with fixed \(D_1\) chosen large after \(A\). The first omitted reciprocal shell is \(O_A(L^{-A})\) by the factorial bound, and all its integers \(e\) satisfy \(e\le\exp(O_{D_1}(L^{.24}\log L))\). The floor bill is subpower. In each retained dilation \(n=e k\) the \(k\)-length is \(P^{\epsilon_0-o(1)}\); if \((e,Q)>1\) the character term is zero. For the remaining \(e\), the same Iwaniec pure-character estimate as in the owner's Gram bound (4)–(5), or complete periods for the smallest primitive conductors, gives \(\sum\chi(k)\ll (X/e)P^{-c}\) on every interval in range. Indeed the primitive conductor has polylogarithmic radical, the endpoint is polynomial, and the effective exponent parameter \(\log(f(|t|+3))/\log (X/e)\) stays in a compact range at height zero once the trivial-period cases are excluded. Include–exclude the finitely many missing-prime factors of \(Q\) to transfer the primitive bound, as in the Gram proof. Sum the reciprocal dilations \(\ll\log z\); the omitted-shell error is already log-small. This proves arbitrary-log cancellation for \(R_z\chi\), including the harmless factor \(\kappa_z^{-1}=O(L^{.24})\).
* **Principal character and twists.** On both supports, the principal value is one since \(\operatorname{rad}(Q)<z\). Classical PNT gives \(\sum_{n\in J_X}w(n)=|J_X|+O_A(XL^{-A})\). The pure integer Bonferroni calculation with exact CRT floors gives \(\sum_{n\in J_X}R_z(n)=\kappa_z |J_X|+O_A(XL^{-A})\), with the same arbitrary saving by increasing \(D_1\). These two main terms cancel exactly at the coefficient \(\kappa_z^{-1}\). Finally partial summation extends all the estimates to \(n^{it}\), spending at most \(O(1+|t|)\), a fixed log power. All constants are uniform on polynomial \(X\) and for the stipulated lifts. This proves (2).

## 3. Applying the reflected comparison twice

In each physical prime-product rectangle \(I_1\times I_2\), take both relative widths at most .1, their product wholly inside \(I\), and polynomial scales \(X_1,X_2\) with \(X_1X_2\asymp P\). The weighted count is
\[
\mathcal C(I_1,I_2)
=\sum_{u\in\mathcal T}\sum_{\substack{x\in I_1,\;q\in I_2\\ u r=P-xq,\ r\in\mathbb N}}
    w(x)w(q)w(r).
\]
In the [full-target projected minor comparison](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/target_slope_switch/Proof.md), the minor input permits arbitrary bounded-polylog, \(z\)-rough target-unit coefficients on each of the two factors. Its companion [major proof, §2](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/small_radical_projection/Proof.md) uses the special Möbius factor only in (14): the exceptional tag-moment characters are treated by a uniform arbitrary-log individual bound on that slot after low-character twists and archimedean separation, together with the restricted Bessel bound on the other arbitrary slot. On the nonexceptional characters it uses only the divisor-square moment and coefficient sizes. Thus its proof applies verbatim with either slot replaced by the above \(\alpha\) satisfying (2), and the other an arbitrary bounded-polylog factor. There is no assertion of such cancellation for the uncentered prime coefficient on the principal character. The exchange of slots changes neither the minor comparison nor the major factorization.

For each relative-width tag shell \(u\asymp U\), use its prescribed smooth shell partition and relative cutoffs; there are \(O_K(L)\) shells, with uniform derivatives in the rescaled shell variable. The mean-square bound is \(O_R(PU L^{-R})\) for any requested fixed \(R\), taking \(K\) sufficiently large and even. Here \(w(r)/L\) is an arbitrary bounded residual depending on \(r\) **alone**, valid because the equation is \(P-xq=ur\), not a translated \(\lambda(ur-cP)\). Cauchy with \(O(P/U)\) possible \(r\) gives an \(O_R(P L^{1-R/2})\) unnormalized shell error; the tag normalizer is bounded in terms of \(K\). Sum shells. First replace \(w(x)\) by \(\kappa_z^{-1}R_z(x)\), then replace \(w(q)\) by \(\kappa_z^{-1}R_z(q)\) with the first rough integer coefficient fixed. The total error is \(O_A(P L^{-A})\) per rectangle if \(R,K\) were chosen with fixed extra slack. The theorem is not being invoked on any \(u\)-dependent weight.

## 4. Genuine last-prime Type I main term after both replacements

Choose the short \(I_1\) scale \(X_1\le P^{.35+o(1)}\) and write \(I_2=[q_-,q_+]\). Fix \(u\) and \(x\in I_1\) rough. All primes of \(u\) and \(P\) are below \(z\), hence \((x,uP)=1\). The actual last prime \(r\) belongs to
\[
[(P-xq_+)/u,(P-xq_-)/u]\subset[c_JP/u,C_JP/u],
\]
of length \(x|I_2|/u\), and \(q=(P-u r)/x\) must be an integer and rough. A small prime \(\ell\le z\) dividing \(u\) cannot divide \(q\), since \(P\) is a unit at it; an \(\ell\mid P\) could divide \(q\) only if it divides the actual prime \(r\), impossible since \(r\gg P/u\gg z\). Thus only \(\ell\nmid uP\) enters the Bonferroni rough test for \(q\). A squarefree such divisor \(d\) imposes precisely the reduced progression \(r\equiv P u^{-1}\pmod{x d}\). Here \(x,d\) are coprime (opposite prime ranges) and uniquely recovered from the modulus \(x d\).

Open \(q\)-roughness with the upper/lower Bonferroni cuts through \(D_1\log L\) factors, increasing \(D_1\) after the desired error. All moduli \(xd\le P^{.35+o(1)}\) are in ordinary **maximal** log-prime BV for the actual endpoint scale \(P/u=P^{1-o(1)}\). The two \(r\)-endpoints vary with \(x\) but are always bounded by the same \(P/u\); the maximal form handles them, and the uniqueness of \(x,d\) avoids multiplicity. Thus for each \(u\) the summed arithmetic error including omitted-shell estimates is \(O_A((P/u)L^{-A})\). In the model the totient separates, and the factorial tails multiply sums of \(1/\phi(d)\) with \(\sum_{\ell\le z}1/(\ell-1)=O(\log L)\). The resulting main per \(u\), before applying the outer \(\kappa_z^{-2}\), is
\[
\frac{|I_2|}{u}\,
\prod_{\substack{\ell\le z\\\ell\nmid uP}}\left(1-\frac1{\ell-1}\right)
\sum_{\substack{x\in I_1\\P^-(x)>z}}\frac{x}{\phi(x)}.
\]
As all prime factors of rough \(x\) exceed \(z\), uniformly \(x/\phi(x)=1+O(L/z)\), and its rough count is \(\kappa_z|I_1|+O_A(X_1L^{-A})\). After multiplying by \(\kappa_z^{-2}\), the local factor is
\[
\frac{1}{\kappa_z}
\prod_{\substack{\ell\le z\\\ell\nmid uP}}\left(1-\frac1{\ell-1}\right)
=S(P)\bigl(1+O_K(e^{-c L^{.1}})\bigr).
\]
Indeed at target primes it gives \(1/(1-1/\ell)\); at other ordinary primes it gives \(1-1/(\ell-1)^2\); and each tag prime contributes the extra factor \((\ell-1)/(\ell-2)=1+o(1)\). The omitted tail above \(z\) is \(1+O(1/z)\). Sum errors over \(u\) using \(\sum_u1/u=\mathcal V\); all \(\kappa_z^{-2}\) losses are fixed log powers. Therefore
\[
\mathcal C(I_1,I_2)= |I_1||I_2|\mathcal V S(P)+O_A(P L^{-A})
\]
uniformly on the chosen rectangles, with \(K\) chosen large fixed for the error target. Every \(r\) in this main calculation is an actual prime, not an abstract rough surrogate.

Finally take \(\asymp L\) disjoint short boxes \(I_1=[X,(1+\eta)X]\) with \(P^{.32}\le X\le P^{.35}/(1+\eta)\), for a fixed small \(\eta>0\). For each choose a long interval \(I_2=[cP/X,dP/X]\) of fixed small positive relative width, with every product in \(I\). Such fixed \(c,d,\eta\) exist since \(J\) is nondegenerate. The areas are uniformly \(\asymp P\); all weighted sums are nonnegative true sums, and their total is \(\gg PLS(P)\). Each \(n=pq\) uniquely determines its smaller genuine prime \(p\) and its box. For \(m=ur\), the near-full prime \(r\) is unique (two would multiply beyond \(P\)), and \(u=m/r\) then unique. Each row has log product weight at most \(L^3\), proving the count and weighted favorable mass in §1. The count and favorable signs are not inferred from angular marginals.
