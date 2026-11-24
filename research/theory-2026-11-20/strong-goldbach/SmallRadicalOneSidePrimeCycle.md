# A one-side-prime factor cycle is excluded at small radical

This is a genuine arithmetic exclusion of a class of directed cycles, not an exclusion of all composite closures and not a Goldbach representation result.

## 1. Exact elementary inequality

Let \(N\) be even. Suppose distinct odd unit primes \(x_0,\dots,x_{k-1}<N\) lie on a genuine complementary-factor cycle, with indices modulo \(k\), and a single odd prime \(p\nmid N\) accounts for all multiplicities not in the displayed cycle arcs:
\[
 N-x_i=p^{e_i}x_{i+1},\qquad e_i\ge1.
\]
There need not be a closed graph around the cycle. We do not require \(x_i>\sqrt N\) for the theorem. Write \(L=\log N\), \(M=\lfloor L/\log p\rfloor\), \(E=\sum_i e_i\), and \(R=\operatorname{rad}(N)\). A cycle as above forces \(M\ge1\) and
\[
 L\left(1-\frac{\log 2}{\log p}\right)
       \le R\log p+2\log M.                                      \tag{1}
\]
In particular there is no such cycle in any asymptotic regime with \(R\log p=o(L)\), uniformly since \(p\ge3\). This includes \(R\le L^b\) for fixed \(b<1\) and \(p\le L^B\) for fixed \(B\). The input \(p\) cannot be one of the \(x_i\): its own complementary row would then force \(p\mid N\).

**Local lower bound.** Multiplying \(x_i\equiv-p^{e_i}x_{i+1}\bmod N\) and cancelling all the units gives \(p^E\equiv(-1)^k\bmod N\), and so \(N\mid p^{2E}-1\). For odd \(\ell\mid N\), let \(d_\ell=\operatorname{ord}_{\ell}(p)\), dividing \(\ell-1\). It divides \(2E\), and the standard lifting-the-exponent identity gives
\[
 v_\ell(p^{2E}-1)=v_\ell(p^{d_\ell}-1)+v_\ell(E).
\]
Here \(v_\ell(2E/d_\ell)=v_\ell(E)\). At \(\ell=2\), apply the identity to the base \(p^2\equiv1\bmod 8\) to get \(v_2(p^{2E}-1)=v_2(p^2-1)+v_2(E)\). The identities follow, if desired, by binomial expansion: raising a unit of the form \(1+z\) to an exponent prime to \(\ell\) preserves \(v_\ell(z)\); raising to \(\ell\) adds one when \(\ell\) is odd or \(v_2(z)\ge2\), and these hypotheses persist under iteration.

Let \(h_\ell=v_\ell(p^{d_\ell}-1)\) for odd \(\ell\), and \(h_2=v_2(p^2-1)\). Writing \(a_\ell=v_\ell(N)\), the prime powers \(\ell^{\max(0,a_\ell-h_\ell)}\) all divide \(E\) and are pairwise coprime. Also \(h_\ell\log\ell\le\ell\log p\) at every \(\ell\). The sum of the distinct prime divisors is at most their product \(R\): for two integers \(\ge2\), \(a+b\le ab\), and induction also covers the one-prime case. Hence
\[
 \log E\ge\sum_{\ell\mid N}\max(0,a_\ell-h_\ell)\log\ell
       \ge L-\sum_{\ell\mid N}h_\ell\log\ell\ge L-R\log p.
\]
Since \(1\le e_i\le M\), this yields \(\log k\ge L-R\log p-\log M\). Combining all \(\ell\mid N\) here (not just a maximizing local prime) is what gives an exponent asymptotically equal to 1.

**Contraction upper bound.** Follow the cycle backwards from \(x_i\), taking the shortest terminal word of exponents whose total is at least \(M+1\). This word exists even if it wraps around the cycle: we view the finite cycle periodically. The leading, oldest exponent is in \(\{1,\dots,M\}\); the remaining suffix is a composition of some integer between 0 and \(M\). These suffixes, including the empty composition at 0, number \(1+\sum_{j=1}^{M}2^{j-1}=2^M\). Thus there are at most \(M2^M\) possible whole words. A fixed word sends its initial value to its final value by composing the affine maps \(x\mapsto(N-x)/p^e\). Its absolute slope is \(p^{-\sum e}<1/N\), since \(p^{M+1}>N\). If two outputs had the same word, their initial values in \((0,N)\) would be sent to integer endpoints less than one apart; the endpoints would coincide. The \(k\) distinct cycle labels therefore satisfy \(k\le M2^M\). The two bounds on \(\log k\) give (1).

## 2. Scope in a closure, and the multiple-side-prime alternative

When all \(x_i>\sqrt N\), every row can have at most one factor above \(\sqrt N\), counted with multiplicity, and its cofactor \(m_i=(N-x_i)/x_{i+1}\) is at least 3 and has no factor above \(\sqrt N\). Any full strongly connected component wholly above \(\sqrt N\) which has a cycle is exactly a simple directed cycle: its internal outdegree is at most one, and strong connectivity forces it to be one; all those arcs have multiplicity 1. It is singular (its block is \(I\) minus a cycle permutation matrix) and nonterminal (each cofactor supplies an exit below \(\sqrt N\)). A high cycle in the induced high-label subgraph need not be a full strongly connected component because paths through low labels could return to it. The cycle calculation works in both settings.

For a more general cycle with \(N-x_i=m_i x_{i+1}\), composite rows, and \(m_i>1\), the same congruence gives
\[
 \Xi=\big(\prod_i m_i\big)^2-1\ne0,\qquad N\mid\Xi.
\]
If the \(m_i\) only use \(t\le s\) distinct odd unit prime factors of size at most \(L^{B_0}\), the growing-seed Kummer calculation applies directly to their exponents here. Each exponent is at most \(2kL/\log3\), so \(\log\mathcal B=O(\log(k+1)+\log L)\); there is no determinant cost. Under \(\operatorname{rad}(N)\le L^b\), \(s=\lfloor c\log L/\log\log L\rfloor\), and \(b+c+\theta<1\) for fixed \(\theta>0\), one obtains
\[
 \log(k+1)>L^\theta
\]
for all sufficiently large \(N\): otherwise Yu's upper bound for the chosen deep local valuation is \(L^{b+c+\theta+o(1)}\), while its actual value is at least \(L^{1-o(1)}\). Under a deep prime divisor \(\ell\le(\log L)^{A_0}\) with \(v_\ell N\ge L^{1-o(1)}\), the same conclusion holds for cofactor primes at most \((\log L)^{B_1}\), \(s=\lfloor c\log L/\log\log\log L\rfloor\) and \(c+\theta<1\). See [the growing-seed Kummer calculation](SmallRadicalGrowingSeedKummer.md) (original Yu Theorem 1, (1.9)–(1.11)) for the moving-field parameters, cofactor-base independence, and uniform dimension estimate. This general bound only forces a long cycle unless the cofactor support escapes the stated size/alphabet restrictions; it is not a general exclusion. The singleton exclusion (1) is stronger and elementary.

At a hypothetical Goldbach exception these restrictions apply to cycles in the actual all-composite unit-prime closure. They do not assert that a cycle or a high SCC must occur, constrain all exits of an arbitrary mixed SCC, or prove existence of a Goldbach pair.
