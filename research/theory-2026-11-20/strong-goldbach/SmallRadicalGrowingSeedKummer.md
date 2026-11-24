# Kummer removes one dimension loss in the moving-seed rank test

Sharpening of [the moving-seed rank result](SmallRadicalGrowingSeedRank.md). The retained conclusion concerns true all-composite prime-factor closures, with the same conditional interpretation at a hypothetical Goldbach failure. In its first theorem replace \(b+2c+\theta<1\) by the stronger
\[
 b+c+\theta<1 .
\]
The seeds still number \(s=\lfloor c\log L/\log\log L\rfloor\), for \(L=\log N\). In a locally smaller-prime regime the number can grow faster, as below.

## 1. Yu's stronger condition (1.11) holds for distinct real prime labels

Use the same three choices of auxiliary field at the moving local rational prime \(\ell\) as in the prior note. Let \(q_{\mathrm{Yu}}=2\) for \(\ell>2\) and \(q_{\mathrm{Yu}}=3\) for \(\ell=2\) (Yu's (1.3)). Here \(u\) in Yu's (1.4) is the largest \(u\) such that a primitive \(q_{\mathrm{Yu}}^u\)-th root of unity is in \(K\); it is unrelated to the seed-relation coefficients. Let \(\alpha_0=\zeta_{q_{\mathrm{Yu}}^u}\). If \(\ell\equiv3\bmod4\), \(K=\mathbb Q,\alpha_0=-1\); if \(\ell\equiv1\bmod4\), \(K=\mathbb Q(i),\alpha_0=i\); if \(\ell=2\), \(K=\mathbb Q(\zeta_3),\alpha_0=\zeta_3\). In every case \(K\) contains the \(q_{\mathrm{Yu}}\)-th roots of unity, and \(\alpha_0\) is not a \(q_{\mathrm{Yu}}\)-th power in \(K\): such a root would be of order \(q_{\mathrm{Yu}}^{u+1}\).

Let \(\alpha_1,\dots,\alpha_n\) be the distinct odd prime seeds with nonzero exponents in a hypothetical relation. In each chosen \(K\), their classes are independent along with \(\alpha_0\) in \(K^\times/(K^\times)^{q_{\mathrm{Yu}}}\). Indeed any relation making \(\alpha_0^{j_0}\prod\alpha_i^{j_i}\) a \(q_{\mathrm{Yu}}\)-th power, evaluated at any prime ideal over \(\alpha_i\), forces \(e_i j_i\equiv0\bmod q_{\mathrm{Yu}}\); all other bases are units there. The ramification \(e_i=1\) in \(\mathbb Q\); it is also 1 for odd rational primes in \(\mathbb Q(i)\); in \(\mathbb Q(\zeta_3)\) it is at most 2 and coprime to \(q_{\mathrm{Yu}}=3\), even for the seed 3. Hence every \(j_i\equiv0\), and \(\alpha_0\) itself excludes a nonzero \(j_0\bmod q_{\mathrm{Yu}}\).

For completeness, adjoining chosen \(q_{\mathrm{Yu}}\)-th roots of the \(n+1\) bases gives a Galois extension since \(K\) contains all \(q_{\mathrm{Yu}}\)-th roots of unity. The Galois group acts faithfully as a subspace of \((\mathbb F_{q_{\mathrm{Yu}}})^{n+1}\) by the root multipliers. If this subspace were proper, a nonzero annihilating vector would give a root monomial fixed by the entire group, hence in \(K\). Raising to \(q_{\mathrm{Yu}}\) contradicts the class independence above. Thus the degree is \(q_{\mathrm{Yu}}^{n+1}\), exactly Yu's (1.11). It holds uniformly even though the labels and \(\ell\) vary.

## 2. New analytic cost

By [Yu, Acta Arith. 89 (1999), Theorem 1, (1.10)–(1.11)](https://doi.org/10.4064/aa-89-4-337-378), under (1.11) one can replace \(C(n,d,\mathfrak p)\) by \(C(n,d,\mathfrak p)/\omega_{q_{\mathrm{Yu}}}(n)\). The quotient in the dimension factor is now \((n+1)^{n+2}/(n-1)!\), which is \(\exp(O(n))\), e.g. by Stirling, rather than \(\exp(n\log n+O(n))\). All the other factors are bounded as in the earlier note: \(e=1,d\le2,f\le2,\ \ell^\kappa\le4\), \(\Phi(\mathfrak p)\le\ell^f\), and the last max divided by its \(f\log\ell\) denominator costs at most \(O(\log(n+2))\). Thus the reduced coefficient is \(\ell^f\exp(O(n))\) uniformly. The original local valuation lower bound remains \(a_\ell\ge L^{1-o(1)}\) at a prime maximizing \(a_\ell\log\ell\) if \(\operatorname{rad}(N)\le L^b\); here \(\ell^f\le4L^b\) because the odd-\(\ell\) residue degree is one.

If \(p_i\le L^{B_0}\), the height factor is \((O(\log L))^s=L^{c+o(1)}\). The coefficient \(\exp(O(s))=L^{o(1)}\), and \(\log\mathcal B=O(k\log L)\le L^{\theta+o(1)}\). A prohibited nonzero supported relation would therefore give
\[
 a_\ell\le v_\ell(\Xi)\le L^{b+c+\theta+o(1)}.
\]
This contradicts the lower bound for \(b+c+\theta<1\). The closure rank, hitting set, and singular-SCC alternatives are exactly those of the earlier note, with this enlarged parameter range.

## 3. One more logarithm when the deep local prime itself is smaller

More generally, suppose there is a prime divisor \(\ell\mid N\) with \(\ell\le(\log L)^A\) for a fixed \(A\) and \(v_\ell(N)\ge L^{1-o(1)}\). If the chosen unit seeds satisfy \(p_i\le(\log L)^{B_1}\) for a fixed \(B_1\), then the heights are \(O(\log\log L)\), while \(\ell^f=L^{o(1)}\). Take
\[
 s=\Big\lfloor c\,\frac{\log L}{\log\log\log L}\Big\rfloor,\quad k\le L^\theta,\quad c+\theta<1 .
\]
The height cost is \((O(\log\log L))^s=L^{c+o(1)}\), and the dimension coefficient remains \(L^{o(1)}\). Hence the same independence and \(\nu\ge s\) follow. The local hypothesis alone does not ensure availability of that many very small unit seeds: this is either an explicit premise, or follows e.g. with \(\operatorname{rad}(N)\le L^b\), since at most \(O(\log L)\) primes divide \(N\) and the number of primes at most \((\log L)^2\) greatly exceeds that. Pure powers \(N=2^a\) automatically have the local and seed conditions. The stronger bound \(\operatorname{rad}(N)\le(\log L)^A\) also ensures a qualifying local prime by maximizing \(v_\ell(N)\log\ell\).

At a hypothetical Goldbach exception all these chosen orbits are all-composite, but the rank applies to the joint orbit only under \(k\le L^\theta\). The alternative with a large individual closure, or with many distinct singular cyclic SCCs under a uniform bound on each individual size, has exactly the same proof. Singular cyclic SCCs need not be terminal; no unconditional existence or failure of a Goldbach representation follows.
