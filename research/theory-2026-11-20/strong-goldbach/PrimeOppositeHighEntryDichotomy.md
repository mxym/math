# Prime-opposite roots, genuine high entries, and the required unrooted escape

This connects the high-path restrictions to genuinely occurring prime-opposite rows at a hypothetical no-prime-pair target. It makes no claim that either side of the dichotomy is impossible.

## 1. Actual prime-sourced rough complements

Fix \(0<\alpha<\beta<1\), \(0<\varepsilon<1/8\), and write \(X=\sqrt N\), \(z=N^\mu\), \(\mu=1/8-\varepsilon\), at an even target \(N\). For all sufficiently large \(N\),
\[
 \#\{p\in(\alpha X,\beta X]\ {\rm prime}:\ (p,N)=1,\quad
                         P^-(N-p)>z\}\ \gg_{\alpha,\beta,\varepsilon}\ X/(\log N)^2 .
                                                                  \tag{1}
\]
Here and below the least factor condition can be interpreted by sifting primes \(\ell\le z\). No distribution result on primes in a short interval of length \(N^{1/2}\) **at scale \(N\)** is used: the prime variable itself has scale \(X=\sqrt N\).

To check the sieve, use the sequence \(N-p\) over primes \(p\) in that fixed-fraction \(X\)-interval. For a squarefree integer \(d\) over primes \(\ell\nmid N\), the literal test \(d\mid N-p\) is \(p=N\bmod d\), a single reduced residue class modulo the actual \(d\), not a twisted or target-scaled modulus. The main density is \(g(d)=1/\varphi(d)\), with base mass \(Y=\operatorname{Li}(\beta X)-\operatorname{Li}(\alpha X)\asymp X/\log X\) and standard prime-count remainder. Bombieri–Vinogradov, in its max-over-reduced-classes form and applied at both endpoints, controls the total absolute remainder up to any \(D\le X^{1/2}/(\log X)^B\) with arbitrary fixed logarithmic saving after taking \(B\) large. Take \(D=N^{1/4-\varepsilon}\), which is below every fixed logarithmic loss at the square-root BV scale. Our ratio is
\[
 \frac{\log D}{\log z}=\frac{1/4-\varepsilon}{1/8-\varepsilon}>2 .
\]
If desired, lower the level to \(z^{s_0}\le D\) with a fixed \(2<s_0<\min(3,\log D/\log z)\). The ordinary lower linear sieve has \(f(s_0)=2e^{\gamma}\log(s_0-1)/s_0>0\) and \(\lvert\lambda_d^-\rvert\le1\). Its dimension-one hypothesis is uniform: \(2\mid N\) is excluded, \(g(\ell)=1/(\ell-1)\) for the other eligible primes, and the Mertens dimension bound for their product is no worse than the one for all odd primes, since excluding a prime improves the upper bound for \(\prod(1-g(\ell))^{-1}\). The full product over odd primes is \(\asymp 1/\log z\) by comparison with Mertens (the ratio of local factors is \(1+O(\ell^{-2})\)), and excluding primes dividing \(N\) only raises the product. So the lower main term is \(\gg Y/\log z\), and the aggregate remainder is negligible. One can delete all primes dividing \(N\) **after** this sieve, at cost at most \(\omega(N)=O(\log N)\), avoiding any accumulation of a per-modulus deletion error. For the remaining unit sources \(p\), no \(\ell\mid N\) can divide \(N-p\); hence the eligibility filter really removes all primes \(\le z\) from the complement. This proves (1), uniformly in even \(N\). Primary references: [Bombieri, *On the large sieve*, Mathematika 12 (1965), 201–225](https://doi.org/10.1112/S0025579300005313); [Iwaniec, *Rosser's sieve*](https://www.impan.pl/shop/publication/transaction/download/product/102606?download.pdf=).

## 2. A genuine two-way split at the prime sources

Assume now that \(N\) is not a sum of two primes. For every source in (1), \(N-p\) is composite. Every row contains a prime factor \(\le\sqrt{N-p}<X\), and a prime \(q>X\) occurs at most once, including multiplicity. Partition the prime sources into those with no high factor and those with a high factor. Thus at least one holds:

* There are \(\gg X/(\log N)^2\) distinct prime-source rows whose composite complements have **all** prime factors in \((z,X]\).
* There are \(\gg X/(\log N)^2\) distinct high labels \(q>X\), each the actual factor of a displayed prime-source row. The sources are distinct and a fixed high \(q\) cannot occur for two of them: \(0<p<X<q\), so \(p\) is the least positive residue \(N\bmod q\). The remaining cofactor is \(>z\), as it is nontrivial and rough, so every such entrance label \(q<N/z\).

In either branch that has the stated number of rows, at least \(\gg z/(\log N)^2\) distinct low prime labels in \((z,X]\) occur immediately. Indeed assign any one low factor \(\ell>z\) to each row. The actual sources assigned to it lie in one residue class \(p=N\bmod\ell\) in an interval of length \((\beta-\alpha)X\), hence number \(O(X/z+1)=O(X/z)\). This is cardinality in the genuine graph, not replacement by a distributional model. The split is unconditional *at a hypothetical no-pair target* once the rough count is supplied; arbitrary targets with prime pairs would also have a prime-complement branch.

## 3. High labels with a low prime parent cannot sustain a high chain

Call a genuine unit prime \(q>X\) **low-rooted** if there exists an odd unit prime \(p\le X\) with a genuine composite arc \(N-p=m_0q\) with \(m_0\ge3\). This can be a low parent anywhere in the true graph, and not just in the particular forward closure or the sampled interval. All the high entries in the second branch are low-rooted.

Suppose there is a different high predecessor \(x>X\) in a true high step \(N-x=mq\) with \(m\ge3\). Because \(p<q\), \(p\) is the least positive residue \(N\bmod q\), so \(x=p+jq\) with integer \(j\ge1\). Oddness of both \(x,p\) and \(q\) forces \(j\ge2\) even; hence \(x>2q\). Also \(m=m_0-j\). If \(q>N/5\), then \(m_0=(N-p)/q<5\) is odd and at least 3, so \(m_0=3\), which would force \(m\le1\): there is no high composite predecessor at all. This last statement is about an arc in the all-composite graph; an arbitrary edge with quotient 1 is not one of these arcs and would instead display a prime-pair representation.

Let \(k\) be the vertex length of any true high path in \((X,N)\) and \(u\) the number of its non-low-rooted vertices. Set
\[
 B=1+\lfloor\log_2(N/X)\rfloor.
\]
A run of all low-rooted high vertices has length at most \(B\), since every step targeting a low-rooted label divides the previous magnitude by a factor \(>2\); the starting/ending ratio is \(<N/X\). There are at most \(u+1\) runs, so
\[
 k-u\le B(u+1),\qquad
 u\ge \max\left(0,\left\lceil\frac{k-B}{B+1}\right\rceil\right).
\]
For a high cycle some vertex must be non-low-rooted (otherwise sizes would strictly fall round it), and the at most \(u\) cyclic rooted runs give \(u\ge\lceil k/(B+1)\rceil\). These counts are on actual labels. Thus if [the growing-seed rank/branching theorem](SmallRadicalEffectiveBranching.md) forces a high chain of length \(\exp(\Omega(L^\theta/s))\), \(L=\log N\), a diverging number \(\gg k/\log N\) of its labels must have **no** low prime composite parent even globally. In particular the short-prime start cloud cannot itself supply a long chain only of its seeded high labels. The near-top \(q>N/5\) is an even stronger absolute no-high-incoming restriction for a low-rooted label.

There is also a distinct side-factor escape. In the second branch, the rough prime-source edge has quotient \(>z\), so enters below \(N/z\). For any subsequent block all of whose quotients are \(\ge z\), the high labels after each such edge remain \(\le N/z\). If their quotients use only a set of \(t\) side primes, [the affine word argument](HighFactorChainScaleCap.md) for a true high chain below \(U=N/z\) gives an upper length \(\exp(O_\mu((t+1)\log\log N))\), using \(\lambda\asymp N^\mu\) and a constant window size. For completeness, at most \((1+L/\log3)^t\) quotient values are possible; a fixed word of \(w>1/\mu\) quotients all \(\ge z\) has slope \(<1/N\) and determines its integer endpoint uniquely once the real starting range is \((0,N)\). Therefore any much longer path with only \(O(\log\log N)\) side primes must repeatedly have quotients **below** \(z\) in its long blocks. This changes the arithmetic of a high orbit from the initial rough entrance; it is not a contradiction, since later rows were not required to remain rough.

The rank implication applies to the particular closure on which its feedback/depth hypotheses hold; the many sieve sources in (1) need not belong to that closure unless they were included as initial labels. The definition of low-rooted is deliberately global, so the necessity of many non-low-rooted labels in any long genuine high path has no such membership assumption. Neither the many all-low roots, nor the possible long mixed high trajectories with non-low-rooted labels, is excluded here.
