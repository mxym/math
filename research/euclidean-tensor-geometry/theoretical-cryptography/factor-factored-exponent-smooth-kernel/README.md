# Smooth-kernel polynomial classes for factored-exponent factoring

Let \(N>1\). Suppose an even positive integer \(E\), together with its
complete prime factorization, is supplied and
\[
 \lambda(N)\mid E,\qquad \log E=(\log N)^{O(1)}.
\]
As before, let
\[
 \mathcal P_E(N)=\{p:p\mid N,\ p\nmid E\}.
\]

For distinct \(p,q\in\mathcal P_E(N)\), put
\[
 g(p,q)=\gcd(p-1,q-1).
\]
An orientation \(h\in\{p,q\}\) is admissible if
\(h-1\nmid h'-1\), where \(h'\) is the other endpoint. Set
\[
 \Delta(p,q)=
 \max_{\text{admissible }h}
 \frac{\log((h-1)/g(p,q))}{\log(h-1)}. \tag{1}
\]

> **Polynomial-class theorem.** Fix \(\delta>0\). If every residual
> pair satisfies
> \[
> \Delta(p,q)\ge\delta, \tag{2}
> \]
> then the complete prime-power factorization of \(N\) can be recovered
> deterministically in
> \[
> \operatorname{poly}_{\delta}(\log N+\log E)
> \]
> bit operations. More explicitly, any fixed \(A>1/\delta\) permits the
> ordinary-base scan to stop by
> \[
> B=\left\lceil(\log N)^A\right\rceil. \tag{3}
> \]

The condition means that, for every pair, one endpoint \(h\) has a
polynomially large quotient
\[
 \frac{h-1}{\gcd(p-1,q-1)}\ge(h-1)^\delta.
\]

The exact underlying stopping criterion is more general. Let
\(\Psi(x,B)\) be the number of \(B\)-smooth positive integers at most
\(x\). If, for every residual pair, some admissible endpoint \(h\)
satisfies
\[
 \Psi(h-1,B)>\gcd(p-1,q-1), \tag{4}
\]
then complete factorization finishes after scanning bases through \(B\).

Indeed, the subgroup
\[
 H=\{x\in\mathbb F_h^\times:x^{g(p,q)}=1\}
\]
has size \(g(p,q)\). If every prime \(\ell\le B\) belonged to \(H\),
then all \(B\)-smooth integers up to \(h-1\) would give distinct elements
of \(H\), contradicting (4). A prime base outside \(H\) has a local
prime-adic order component that separates the pair in one of the
factored-\(E\) gcd chains.

Konyagin--Pomerance give the unconditional lower bound
\[
 \Psi(x,y)>x^{1-\log\log x/\log y}.
\]
Substituting (2)--(3) proves the polynomial-class theorem.

This is an arithmetic-advice result. It does not construct or factor
\(E\), does not cover pairs whose quotient index is subpower at both
endpoints, and does not concern a concrete modulus or deployed system.
No absolute priority claim is made.

See [PROOF.md](PROOF.md) and [UPSTREAM.md](UPSTREAM.md). Run
\`python3 verify.py\` for finite exact checks.
