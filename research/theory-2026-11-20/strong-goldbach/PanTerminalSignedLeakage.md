# A one-sided leakage bound for the true double-terminal Pan sector

Write \(L=\log P, L_2=\log L\) for any sufficiently large even target \(P\). Use its standard positive singular series \(\mathfrak S(P)\), and \(Q_0=\sqrt P L^{-20}\). Let
\[
 a(n)=\sum_{b\mid n,\ b>Q_0}\mu(b)\log b,\qquad
 a^*(r)=\sum_{d\mid r,\ d>Q_0,\ (d,P)=1}\mu(d)\log d.
\]
Their reflected convolution is Pan's actual \(R_3(P)\); in particular the unit restriction is **not symmetric**. See [Huang–Li, (2)–(6), recording Pan's theorems](https://arxiv.org/html/2005.03811v2#S1). Set \(0<\delta\le1/4\), \(Z=P^{1-\delta}\), \(T(n)=1_{P^+(n)>Z}\), \(T(1)=0\), and define
\[
 B_\delta(P)=\sum_{1\le n<P}T(n)T(P-n)a(n)a^*(P-n),\qquad
 G(P)=\sum_{p+q=P\atop p,q\ {\rm prime}}\log p\log q
\]
with ordered representations. For an absolute \(C\), uniformly in these parameters,
\[
 -C(\delta+e_P)\le \frac{B_\delta(P)-G(P)}{P\mathfrak S(P)}
 \le C(\delta^2+e_P),\qquad
 e_P=\frac{1+L_2^2}{L}+L^2P^{-\delta}.                 \tag{1}
\]
In particular the unknown true prime atom is retained. Since \(G\ge0\), the double-terminal block by itself cannot produce a negative loss exceeding \(O(\delta P\mathfrak S(P))+o(P\mathfrak S(P))\) for fixed small \(\delta\). There is **no** proof this block is positive.

## 1. Uniform two-linear-forms upper sieve

For \(1\le m,l\le P^\delta\), let \(e=(m,l)\). There are no representations \(mp+lq=P\) unless \(e\mid P\). If \(e\mid P\), then
\[
 \#\{p,q>Z\text{ prime}:mp+lq=P\}
 \ll \frac{Pe}{ml L^2}
 \prod_{s\mid mlP,\ s>2\ {\rm prime}}\frac{s-1}{s-2}.             \tag{2}
\]
Here and below constants are absolute. Write \(U=m/e,V=l/e,H=P/e\). If a prime divides both \(UV\) and \(H\), it forces one prime variable to equal that divisor, impossible as \(U,V\le P^\delta<Z\). Otherwise write \(p=p_0+Vz,q=q_0-Uz\); such a solution parameterization exists since \((U,V)=1\). Positivity restricts \(z\) to an interval of length at most \(Y+O(1)\), \(Y=H/(UV)=Pe/(ml)\ge P^{1-2\delta}\ge\sqrt P\). Enlarge arbitrarily short endpoint pieces to this length; no lower bound on the actual piece containing admissible primes is used.

For primes \(s\nmid UVH\) the product of these forms removes two distinct residues; for \(s\mid UVH\) it removes one, by \((U,V)=(UV,H)=1\). If all residues modulo 2 are removed there are no candidates. Otherwise apply [the arithmetic large sieve (Montgomery's inequality, e.g. Ford notes, Theorem 6.5)](https://ford126.web.illinois.edu/sieve_notes_large_sieve.pdf) to the enlarged interval, with \(z_1=Y^{1/4}\). The numerator is \(O(Y+z_1^2)\); the denominator is \(\sum_{r\le z_1}\mu^2(r)\prod_{s\mid r}\nu(s)/(s-\nu(s))\), with the preceding counts \(\nu(s)\). Every counted prime exceeds \(z_1\). For an elementary lower bound on this denominator, take divisors of the product of primes up to \(w=z_1^c\) for a sufficiently small fixed absolute \(c>0\). Under the product probability normalized by the corresponding Euler product the expected \(\log r\) is \(\sum_{s\le w}\nu(s)(\log s)/s\ll\log w\). By Markov, at least half the mass has \(r\le z_1\). Mertens' product bound thus gives a denominator
\[
 \gg (\log Y)^2\prod_{s\mid UVH,\ s>2}\frac{s-2}{s-1},
\]
since replacing two forbidden classes by one costs the displayed local factor. Enlarging the bad-prime set to the prime divisors of \(mlP\) can only increase the RHS of (2). This proves (2), uniformly despite variable slopes and endpoints.

## 2. Exact arithmetic and the coprime leakage

Each terminal integer has a unique large prime label and can be written \(n=pm\), \(p>Z, m<P^\delta<Q_0\). Every divisor \(>Q_0\) contains \(p\), which is coprime to \(m\). Hence
\[
 a(pm)=-\log p\,1_{m=1}+\Lambda(m).
\]
If either terminal prime label divides \(P\), omit this physical input. There is at most one such distinct prime since \(Z^2>P\); there are \(O(P^\delta)\) possible multiples in either coordinate. The absolute cost is \(P^{\delta+o(1)}\) by the elementary divisor maximum for \(n,P-n\in[1,P)\). Their possible true prime-pair contributions obey the same bound.

First suppose \((n,P)=1\), equivalently \((P-n,P)=1\). Then both coefficients have the same exact formula. The two-prime case is \(G(P)\), except for possible prime inputs \(\le Z\) costing in total \(O(ZL^2)\) and the preceding omitted prime labels. The two mixed cases have negative sign; each has magnitude
\[
 \ll \frac{P\mathfrak S(P)}{L}\sum_{l\le P^\delta}\frac{\Lambda(l)}l
 \ll P\mathfrak S(P)(\delta+1/L).
\]
This uses (2) with \(m=1\), the large-prime weight at most \(L\), and at most one additional prime in the singular product from the prime power \(l\); each extra local factor is at most 2. The both-composite contribution is nonnegative. Its nonzero terms have prime-power \(m,l\) and automatically \((m,l)=1\): a shared prime would divide \(P\). Thus (2), with at most two extra local factors, gives
\[
 \ll\frac{P\mathfrak S(P)}{L^2}
 \left(\sum_{l\le P^\delta}\frac{\Lambda(l)}l\right)^2
 \ll P\mathfrak S(P)(\delta+1/L)^2.
\]

## 3. Full accounting of nonunits

When \((n,P)>1\) and the large labels do not divide \(P\), a nonzero left term forces \(m=k^i\) with prime \(k\mid P\), weight \(\log k\). Write \(P-n=q l\) with \(q>Z\), and \(l=g h\) uniquely with \(g\mid P^\infty\), \((h,P)=1\). The *allowed* large divisors are exactly \(qj\) for \(j\mid h\), because the excluded primes in \(g\) divide \(P\). In particular the right coefficient is **not** the symmetric formula in \(l\); it is
\[
 a^*(q l)=-\log q\,1_{h=1}+\Lambda(h).
\]
The gcd in (2) is now \((k^i,g)\); the singular product costs only \(O(\mathfrak S(P))\), since \(h=1\) or one prime power supplies at most one new prime. Summing over \(h\le P^\delta\) costs \(L+\sum\Lambda(h)/h\ll L\) after accounting for its weight and harmonic denominator. The remaining factor is
\[
 \sum_{k\mid P\ {\rm prime}}\log k\sum_{i\ge1}\sum_{g\mid P^\infty}
 \frac{(k^i,g)}{k^i g}
 \ll\frac P{\phi(P)}\sum_{k\mid P}\frac{\log k}{k}
 \ll 1+L_2^2 ,
\]
where the last sum runs over prime divisors. Indeed the \(k\)-part has \(\sum_{i\ge1,j\ge0}k^{-\max(i,j)}\ll1/k\). Splitting primes at \(L^2\) and using Mertens'/Chebyshev's bounds below it and \(\sum_{k\mid P}\log k\le L\) above it gives both final log-log factors. Thus all nonunit terms together, in either sign, cost \(O(P\mathfrak S(P)(1+L_2^2)/L)\). This completes (1).

**Interpretation and limitation.** From Pan's separate identity \(R_3(P)=G(P)-P\mathfrak S(P)+O(P/L)\) (ordinary prime powers alter the weighted count by at most \(O(P^{1/2}L^{O(1)})\)), the complementary *signed* raw sector satisfies
\[
 R_3(P)-B_\delta(P)=-P\mathfrak S(P)+O\big((\delta+e_P)P\mathfrak S(P)\big).
\]
Thus dropping the complementary mass as negligible would be false: for sufficiently small fixed \(\delta\) it is negative. For example taking \(\delta=4\log L/L\) gives an asymptotic with relative error \(O((1+L_2^2)/L)\). This sign is obtained by cancelling the **same true prime atom** on the two sides of Pan's identity, not by proving a sign for that atom, for \(B_\delta\), or for \(R_3\). In particular the result does not show there is even one Goldbach representation. The underlying two-prime upper sieve is classical; its use here is to account for genuinely reflected mixed terms and the asymmetric divisor mask, not to claim a new upper-bound sieve or precedence over the broad literature on large prime factors of shifted primes.

For comparison, [Arneth's October 2026 cubic-minorant preprint](https://zenodo.org/records/23477014) also retains the exact prime contribution in a signed comparison, but uses a different cubic coefficient on the central interval that vanishes on squarefree semiprimes. The present argument instead bounds the actual mixed terms after a largest-prime cutoff; they do not vanish algebraically. Neither method gives an unconditional sign for the full prime-detecting remainder.
