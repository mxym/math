# Composite outer cofactors in the actual mixed column

Let \(N,J,B,L,\alpha,\beta\) have the hypotheses of the [prime-column proof](Proof.md). Write \(S_b(w)\) as there, but now let \(\mathcal B\) be **any set of integers** in \([N^\alpha,N^\beta]\), not necessarily primes or squarefree. It is enough to keep \((b,N)=1\): other \(b\)'s contribute no central true-prime row. For \(w=1\) or \(w=\exp(L^\gamma)\), \(0<\gamma\leq3/20\), put
\[
 d_b(r)=
  \begin{cases}1/r,&r\mid b,\\1/(r-1),&r\nmid b,\end{cases}
 \qquad
 E_{w,b}(N)=\prod_{\substack{r\leq w,\ r\ {\rm prime}\\r\nmid N}}(1-d_b(r)).
\]
There is a fixed \(\kappa>0\) such that, for arbitrary \(0\leq W_b\leq L\),
\[
 \sum_{b\in\mathcal B} W_b |S_b(w)|
 \ll N L^{-\kappa}
        \sum_{\substack{b\in\mathcal B\\(b,N)=1}}
              \frac{W_b E_{w,b}(N)}{\varphi(b)}+N L^{-10}.
 \tag{A}
\]
In particular, fix \(\eta>0\) and take the **entire** polynomial dyadic range \(Z\leq b\leq2Z\), \([Z,2Z]\subseteq[N^\alpha,N^\beta]\), subject to \(P^-(b)>N^\eta\). Then
\[
 \sum_{\substack{Z\leq b\leq2Z\\P^-(b)>N^\eta}}\log b
 \left|\sum_{a\geq1}\log a
        \sum_{\substack{a m+b n=N,\ am\in NJ\\(am,N)=1}}\mu(m)\mu(n)\right|
     \ll_{\eta} N L^{-\kappa}.
 \tag{B}
\]
No primality, squarefreeness or relative position restrictions are imposed on the factors of \(b\) beyond the displayed roughness. Thus (B) includes genuine balanced composite cofactors in the same physical column; for example when \(\eta<\alpha/2\) it includes semiprime products of two primes of order \(\sqrt Z\). This remains a column with the **whole** \(a\)-sum, not simultaneous independent masks on \(a,b\). The result does not pay the unrestricted integer dyad, or a broad fixed-power interval, at scale \(N\).

## Weighted BV and exact local probabilities

The new arithmetic issue in §1 of the [prime-column proof](Proof.md) is that a modulus \(q=b g\) no longer identifies its large factor \(b\) uniquely. It has at most \(\tau(q)\) such decompositions. This loss is admissible in a fixed-power range below the usual Bombieri–Vinogradov level. Indeed, write \(\Delta_N(q)\) for the maximal genuine prime-log discrepancy, maximized over reduced residues and prefixes up to \(N\). The trivial bound is \(\Delta_N(q)\ll N L^2/q\) for \(q\leq N^{\beta+o(1)}\), by counting integers in one class and bounding \(q/\varphi(q)\ll L\). The application to genuine primes follows from ordinary prime-power BV by the same trivial proper-power removal in the prime-column proof, or by using the usual log-prime version. On \(\tau(q)\leq L^C\) use ordinary BV with its requested exponent increased by \(C\). On \(\tau(q)>L^C\) use
\[
 \sum_{\tau(q)>L^C,\ q\leq N}\frac{\tau(q)}q
   \leq L^{-C}\sum_{q\leq N}\frac{\tau(q)^2}q \ll L^{4-C}.
\]
Here \(\tau^2\leq\tau_4\) and the last harmonic bound follows by opening four integer factors. Thus \(\sum_{q\leq N^{\beta+o(1)}}\tau(q)\Delta_N(q)\ll_A NL^{-A}\) for every fixed \(A\). The same reasoning absorbs \(W_b\leq L\) and the stated polynomial number of logarithmic avoidance patterns. Alternatively, the total genuine-prime-power replacement with this actual modulus multiplicity is \(N^{1/2+o(1)}\), since \(q\mid N-p^j\), and the sum over its divisor decompositions is bounded by \(\tau(N-p^j)^2\).

For each fixed \(b\) and squarefree \(g\) from the avoidance expansion, the actual condition \(g\mid (N-p)/b\) is \(p\equiv N\bmod b g\). This justifies using \(b g\), **not** \([b,g]\) when \(b\) shares a selected prime. The class is reduced because \((b,N)=1\) and primes dividing \(N\) need not be opened: they divide no quotient on these prime rows. The exact conditional main weight is
\[
     \frac{\varphi(b)}{\varphi(bg)}
                =\prod_{r\mid g} d_b(r).
\]
In particular the model is independent across distinct excluded primes conditional on \(b\), although individual probabilities now depend on \(b\). An auxiliary color with reciprocal mass at least \(1/4\) still has hit probability at least \(1-e^{-1/4}\), since \(d_b(r)\geq1/r\). The roughness and auxiliary sets are disjoint as before. The Bonferroni tail bounds are uniform in \(b\), since \(d_b(r)\leq1/(r-1)\). Summing after making this independent local calculation **for each \(b\)** gives missed-bank mass
\[
 O\!\left(N L^{-\kappa_0}
       \sum_{\substack{b\in\mathcal B\\(b,N)=1}}
              W_b E_{w,b}(N)/\varphi(b)\right)+O_A(NL^{-A}).
\]
For even \(N\) this local product is positive, and it is within absolute constant factors of \(E_w(N)\); the possible change at every odd \(r\) has ratio
\((1-1/r)/(1-1/(r-1))=1+1/(r(r-2))\). The prime \(2\) is omitted since \(2\mid N\).

## Why the same signed comparison applies

The Type II extraction was on the **quotient** \(n\). With \(u\mid n\), the exact relation is \(N-x=b n=u h\), \(h=b(n/u)\). This requires no coprimality of \(b\) with \(u\), shares no tag with the \(z\)-rough source, and still leaves the separated residual (5) of the [prime-column proof](Proof.md): sum over \(b\mid h\) with coefficient on \(h/b\). Its size is still at most \(L\tau(h)\). The necessary squarefree-at-bank condition is only on \(n\). A tag prime occurring in both \(b\) and \(n\) is not a failure unless it occurs twice in \(n\). The bad-row bound by \(r^2\mid N-x\) remains a permissible upper bound, with the same divisor moments even for composite \(b\).

Likewise Type I is performed at fixed \(b,g\), uses actual \(n=g v\), and has \((de,bg)=1\) forced by reducing the exact additive equation modulo the common prime. It does not need \((b,g)=1\). The exact \(\mu(gv)\) convolution and its finite \(g\)-support tail are identical, and the floor estimates only used that the number of \(b\)'s is at most \(N^\beta\). The reduced modulus for the \(v/j\) sum is \(de\,\operatorname{rad}(N)\), not \(b g de\,\operatorname{rad}(N)\): \(b,g,j\) are fixed units in the congruence modulo \(de\). Thus the real interval size \(X=N/(b g)\) and the original margin below the Möbius BV level are unchanged. Taking arbitrary coefficients bounded by \(W_b\), duality yields (A) in the summed absolute-value form, with no need to evaluate a prescribed individual composite modulus.

## Natural scale for a whole rough cofactor dyad

For \(Z\leq b\leq2Z\leq N^\beta\) with \(P^-(b)>N^\eta\), one has \(\Omega(b)\leq\beta/\eta\) and \(b/\varphi(b)\ll_{\beta,\eta}1\). The simple upper sieve gives
\[
   \#\{b\in[Z,2Z]:P^-(b)>N^\eta\}\ll_{\alpha,\eta} Z/L.
 \tag{C}
\]
This is uniform whether \(Z\) lies below or above \(N^\eta\): take \(v=\min(N^\eta,Z^{1/10})\), so each retained integer avoids the primes at most \(v\), and \(\log v\geq \min(\eta,\alpha/10)L\). For example, the elementary Selberg upper bound in this interval with divisor support at most \(v\) has main bound
\[
    \frac{Z}{\sum_{d\leq v}\mu^2(d)/\varphi(d)}+O(v^2+1).
\]
All squarefree \(d\leq v\) use only sieved primes. In the usual explicit Selberg minimizer the coefficients have absolute value at most one: fixing squarefree \(d\), multiply any denominator term indexed by \(j\leq v/d,\ (j,d)=1\) by each \(e\mid d\); all \(e j\leq v\), with reciprocal \(\varphi\)-mass increased by \(\sum_{e\mid d}1/\varphi(e)=d/\varphi(d)\). The floor errors therefore give \(O(v^2+1)\). The denominator is \(\gg\log v\) by the squarefree harmonic sum, proving (C). If \(N^\eta\geq2Z\), the claimed rough set is in fact empty. By (C),
\(\sum_{Z\leq b\leq2Z,\,P^-(b)>N^\eta}(\log b)/\varphi(b)\ll_{\alpha,\beta,\eta}1\).
Now use (A) with \(w=1\), \(W_b=\log b\), and the literal \(\Lambda\)-identity. The proper-power removal is still \(N^{1/2+o(1)}\), as the number of allowed *integer* divisors \(b\) of a fixed \(N-x\) is at most \(\tau(N-x)\). This proves (B).

## Two genuinely composite tails within an unrestricted dyad

The same argument gives some whole-bin statements with a moving roughness or a genuine marked logarithm. First, with \(V=\exp(L^\sigma)\), \(0<\sigma<1\) fixed, replace \(N^\eta\) by \(V\) in (C). For large \(N\), \(V<Z^{1/10}\), so the count is \(O_{\alpha,\sigma}(Z/L^\sigma)\). The bound \(b/\varphi(b)\ll1\) still holds, since there are at most \(O_\beta(L^{1-\sigma})\) prime factors, all exceeding \(V\). The harmonic weight is \(O(L^{1-\sigma})\) and (B) is \(O(NL^{1-\sigma-\kappa})\), in particular genuinely negligible for fixed \(\sigma>1-\kappa\). This allows the physical factor rank of \(b\) to grow, unlike a fixed-power rough requirement.

At the other end, within a completely unrestricted dyad take the actual weight
\[
 W_b(U)=\sum_{\substack{r^j\mid b\\r\leq U,\ r\ {\rm prime}\\j\geq1}}\log r
     \leq\log b.
\]
It is the part of the exact logarithm \(\log b=\sum_{r^j\mid b}\log r\) carried by primes at most \(U\). For a prime power \(h=r^j\leq2Z\), using \(\varphi(hc)\geq \varphi(h)\varphi(c)\) gives
\[
 \sum_{\substack{Z\leq b\leq2Z\\h\mid b}}\frac1{\varphi(b)}
 \ \leq\ \frac1{\varphi(h)}
       \sum_{Z/h\leq c\leq 2Z/h}\frac1{\varphi(c)}
 \ \ll\ \frac1{\varphi(h)} .
\]
The uniform last bound (including \(Z/h\in[1/2,1]\)) follows by opening
\(c/\varphi(c)=\sum_{d\mid c}\mu^2(d)/\varphi(d)\). The resulting sum of \(1/(d\varphi(d))\) over squarefree \(d\) converges, and each dyadic harmonic sum in \(c/d\) is \(O(1)\). Since \(\sum_{j\geq1}\varphi(r^j)^{-1}=r/(r-1)^2\ll1/r\), Chebyshev and partial summation now give
\[
 \sum_{Z\leq b\leq2Z}\frac{W_b(U)}{\varphi(b)}
         \ll 1+\log U.
\]
For \(U=\exp(L^\sigma)\), \(0<\sigma<\kappa\) fixed, (A) therefore pays the literal mixed dyad, **with this part of the actual logarithm**, at \(O(NL^{\sigma-\kappa})\). In particular the same bound holds with full \(\log b\) on all \(U\)-smooth cofactors in the dyad, without any bound on their rank. Neither this estimate nor the high-roughness one pays the large-prime marks on \(b\)'s with genuinely mixed scales.

For comparison, even just an upper bound over the unrestricted dyad has harmonic weight \(\sum_{Z\leq b\leq2Z}\log b/\varphi(b)\asymp L\). Equation (A) alone then only gives a relative saving at \(NL\); it does not evaluate or bound the entire unrestricted mixed column at the binary scale.
