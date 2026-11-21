# Removing the smallest-prime cutoff at any fixed physical rank

Use the notation of [the rough-rank proof](pan-rough-rank/Proof.md), but do not impose its fixed roughness exponent. Fix an integer \(j\ge2\). For any sufficiently small fixed \(0<\epsilon<1/(10j)\),
\[
 \limsup_{P\to\infty,\ 2\mid P}
 \frac1{P\mathfrak S(P)}
 \sum_{p+r=P,\ p\ {\rm prime},\ \Omega(r)=j,\ P^-(r)\le P^\epsilon}
       (\log p)|a(r)|
 \ll_j \epsilon(1+\log(1/\epsilon))^{j-2}.                      \tag{1}
\]
The same estimate applies to the true asymmetric coefficient \(a^*(r)\) in the other orientation: if \(p\nmid P\) then \((r,P)=1\); at the \(O(\log P)\) exceptions the coefficients have absolute size at most \(2^j\log P\). This is a physical fixed-target upper bound; it does not require a progression-mean subtraction. The constant depends on the fixed rank; there is no sum over unbounded ranks.

**Proof.** Put \(L=\log P\), \(Q_0=P^{1/2}L^{-20}\), and discard \(\min(p,r)<P^{9/10}\) at cost \(P^{9/10+o(1)}\). Discard also any \(r\) divisible by the square of a prime exceeding \(P^{1/(100j)}\); their cost is \(\ll_j PL^2 P^{-1/(100j)}\). Then \(\operatorname{rad}(r)\ge r/P^{1/100}\ge P^{.89}\). Write \(s=P^-(r)\), \(R=\operatorname{rad}(r)/s\). Even for \(s^e\Vert r\) with \(e\ge2\), divisors weighted by \(\mu\) have **only one possible copy of \(s\)**. Pairing those with and without it gives exactly
\[
 a(r)=-(\log s)\sum_{d\mid R,\ d>Q_0/s}\mu(d)
       -\sum_{d\mid R,\ Q_0/s<d\le Q_0}\mu(d)\log d.              \tag{2}
\]

For the first term choose a distinct largest prime label \(q\mid r\), \(q\ge P^{.89/j}\). Its multiplicity is one on the retained set, and \(q\ne s\) since \(s\le P^\epsilon\). Fix the other labels and their actual multiplicities, write \(A=r/q\), and use the two-prime upper bound (1) in [the preceding proof](pan-rough-rank/Proof.md). Only the order of magnitude \(\ll_j \mathfrak S(P)(P/A)/L^2\) is needed: \(\log(P/A)\gg_j L\) and the extra local factors for the at most \(j\) primes in \(A\) are bounded by \(2^j\), even if tiny. Nonunits already have been excluded. With \(2^{j-1}\log s\) as coefficient bound and \(\log p\le L\), this costs at most a constant depending on \(j\) times
\[
 \frac{P\mathfrak S(P)}{L}
 \sum_{s\le P^\epsilon\ {\rm prime}}\frac{\log s}{s}
 \left(1+\sum_{s\le t\le P\ {\rm prime}}\frac1t\right)^{j-2}.       \tag{3}
\]
Here \(s^{-e}\le s^{-1}\) and similarly for the other labels; the number of multiplicity patterns/choices is bounded in terms of \(j\). The true least-prime order on all other labels is retained in the harmonic bound.

For the second term of (2), every contributing divisor \(d\mid R\) has \(Q_0/s<d\le Q_0\). Both \(d\) and \(R/d\) exceed \(P^{.3}\) for large \(P\), since \(R\ge P^{.89-\epsilon}\). Choose a prime \(b\mid d\) and another \(q\mid R/d\), each at least \(P^{.3/j}\), necessarily distinct, neither equal to \(s\), each occurring to exponent one in \(r\). For \(j=2\) this configuration is impossible. Fix \(s\), the other multiplicities and labels, and their assignments to \(d\) or its complement. Thus \(d'=d/b\) is fixed without \(b,q\). Now \(b\in (Q_0/(s d'),Q_0/d']\), an interval of multiplicative width \(s\). Subject to the polynomial lower bound on \(b\), its prime harmonic sum is \(\ll_j(1+\log s)/L\): cover by \(O(1+\log s)\) dyads and use Chebyshev. For each such \(b\) one has a free prime \(q\) against the true \(P-Aq\) with \(A=r/q\); apply the same upper sieve, dropping cases \(P/A<P^{.3/j}\) which cannot contribute. Its \(L^{-2}\) pays for both outer logs. Summing the reciprocal \(b\) with its restriction and the other prime labels freely above \(s\) gives at most (3) up to a rank-dependent factor. Counting more than one eligible distinguished \(b,q\) is harmless in this absolute upper bound.

Finally Mertens' prime harmonic sum bounds the inner parenthesis by \(O(1+\log(L/\log s))\). Split the smallest prime into bands \(2^{-i-1}\epsilon L<\log s\le2^{-i}\epsilon L\). For a nonempty band Chebyshev gives \(\sum (\log s)/s\ll2^{-i}\epsilon L\). Its remaining factor is \(\ll_j(1+\log(1/\epsilon)+i)^{j-2}\). Summation proves (1).

**Unrestricted low-rank consequence.** In either orientation of the actual raw remainder, the *entire negative mass* from a true prime paired with \(\Omega(r)=4\) is \(o(P\mathfrak S(P))\), without a least-prime restriction. The same is true at rank three outside its balanced-triangle shapes and at rank five outside its star shapes. For fixed \(\epsilon>0\), restrict first to \(P^-(r)>P^\epsilon\): squareful inputs cost \(P^{1-\epsilon+o(1)}\), and the fixed-rank simplex argument in [§§2–3](pan-rough-rank/Proof.md) applies with \(k=\epsilon\), giving nonpositive limiting \(F_j\) on the stated shapes. Subset-midpoint walls have zero simplex measure. The actual shape uses the logs of the prime factors divided by \(\log r\) (with multiplicity if repeated). For sorted coordinates, rank three can be dangerous only when the largest is below half; rank five only when the largest is below half but the largest plus smallest exceeds half. Then (1) makes *all* remaining smallest-prime contributions negligible on letting \(\epsilon\downarrow0\), including repeats. This does not give the earlier numerical rank-six-and-higher budget on inputs with arbitrarily small factors.

[Arneth's September 2026 five-factor note](https://zenodo.org/records/23016346) treats repeated prime factors of a different truncated coefficient under a specified balanced profile. The divisor pairing here also uses the radical, but estimates the entire small-least-factor contribution of the literal Pan coefficient at an arbitrary fixed rank. This does not compare all signed sectors or settle their combined sign.
