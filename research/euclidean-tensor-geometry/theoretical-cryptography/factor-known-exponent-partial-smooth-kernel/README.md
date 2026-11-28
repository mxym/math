# Partial-signature smooth-kernel factoring without factored advice

Let \(N>1\) and suppose only the value of an even positive integer \(E\)
is supplied, with
\[
 \lambda(N)\mid E,\qquad \log E=(\log N)^{O(1)}.
\]
The factorization of \(E\) is **not** supplied.

Choose a cutoff
\[
 2\le Y\le(\log N)^{O(1)}
\]
and enumerate the primes \(r\le Y\). Their valuations in \(E\) are found
by division. Strip from \(N\) the exact powers of these small primes.

For distinct remaining prime divisors \(p,q\), define the oriented known
index
\[
 M_Y(q\mid p)=
 \prod_{\substack{r\le Y\\r\ {\rm prime}}}
 r^{\max\{0,v_r(q-1)-v_r(p-1)\}}. \tag{1}
\]
An orientation is admissible when this index exceeds \(1\), and put
\[
 \Delta_Y(p,q)=
 \max_{\text{admissible }h\mid h'}
 \frac{\log M_Y(h\mid h')}{\log(h-1)}. \tag{2}
\]

> **Polynomial-class theorem without factored advice.** Fix
> \(\delta>0\). If every pair of distinct remaining prime divisors
> satisfies
> \[
> \Delta_Y(p,q)\ge\delta, \tag{3}
> \]
> then the complete prime-power factorization of \(N\) can be recovered
> deterministically in
> \[
> \operatorname{poly}_{\delta}(Y,\log N+\log E)
> \]
> bit operations. In particular, for polynomial-logarithmic \(Y\), the
> running time is polynomial in the input bit length.

More explicitly, any fixed \(A>1/\delta\) permits the base scan to stop
by
\[
 B=\left\lceil(\log N)^A\right\rceil. \tag{4}
\]

For an admissible orientation \(h\mid h'\), let
\(m=M_Y(h\mid h')\) and \(k=(h-1)/m\). The subgroup
\[
 H=\{x\in\mathbb F_h^\times:x^k=1\}
\]
has size \(k\le(h-1)^{1-\delta}\). Konyagin--Pomerance smooth-number
growth guarantees a small prime base outside \(H\). Such a base has,
at \(h\), a larger local order component at one of the known primes
\(r\le Y\) than it can have at \(h'\). The corresponding \(r\)-adic
power-gcd chain splits the pair.

Unlike the full-signature results, this theorem does not factor \(E\)
and does not require its factorization as advice. Its hypothesis only
uses the part of the \(p-1\) valuation profiles supported on small
primes.

This is a promised arithmetic class, not unrestricted polynomial-time
factoring. It constructs neither \(E\) nor the profile promise and
concerns no concrete modulus or deployed system. No absolute priority
claim is made.

See [PROOF.md](PROOF.md) and [UPSTREAM.md](UPSTREAM.md). Run
\`python3 verify.py\` for finite exact checks.
