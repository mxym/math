# Balanced rough composite companions at every large even center

There are absolute positive constants \(\eta,\rho,c\) such that every sufficiently large even \(N\) has at least \(cN\mathfrak S(N)/(\log N)^2\) actual primes \(P\in[N/4,N/2]\) whose companion \(y=N-P\) is squarefree and all of whose prime factors belong to \([N^\eta,N^{1/2-\rho}]\). Thus these companions have at least three and at most \(\lfloor1/\eta\rfloor\) actual prime factors. Write
\[
 \mathfrak S(N)=2\prod_{r>2}\left(1-\frac1{(r-1)^2}\right)
                    \prod_{\substack{r>2\\r\mid N}}\frac{r-1}{r-2},
\]
with prime-indexed products.

**Tagged version.** Fix \(0\le\xi<1/2\) and \(C_0\ge0\). There are \(\eta,\rho,c>0\) so that the following holds uniformly for sufficiently large even \(N\). A tag bank consists of squarefree integers \(h\le N^\xi\), coprime to \(N\), all of whose prime factors are at least \(N^\eta\), with weights \(0\le w_h\le1\). The tag \(h=1\) is allowed. If
\[
 H_N=\sum_h\frac{w_h}{\varphi(h)}\ \ge (\log N)^{-C_0},
\]
then
\[
 \sum_{\substack{P\in[N/4,N/2]\ {\rm prime},\ (P,N)=1\\
 y=N-P\ {\rm squarefree},\ N^\eta\le P^-(y)\le P^+(y)\le N^{1/2-\rho}}}
 \ \sum_{h\mid y}w_h
 \ \ge c H_N\frac{N\mathfrak S(N)}{(\log N)^2}.
 \tag{1}
\]
The bank can depend arbitrarily on \(N\); the parameters and threshold do not depend on the bank. A row has at most \(2^{\lfloor1/\eta\rfloor}\) tags, so (1) also lower-bounds the number of distinct rows meeting the support of the bank, after changing \(c\).

For example, require one actual prime factor in each of finitely many disjoint fixed exponent windows \((N^{a_j},N^{b_j}]\) with \(a_j>0\) and \(\sum_j b_j<1/2\), allowing any fixed reduced residue class for each tag prime (e.g. each tag prime is \(1\bmod4\)). Take \(h\) to be the product of the tags, \(w_h=1\), and decrease \(\eta\) below the left endpoints. The prime number theorem in fixed progressions and partial summation give \(H_N\) converging to a positive constant: each factor harmonic converges to the corresponding fixed fraction of \(\log(b_j/a_j)\), and the omission of primes dividing \(N\) costs \(O((\log N)/N^{a_j})\). This example does not claim that the *unmarked* factors lie in those residue classes.

## Proof

Write \(L=\log N\), \(J=[N/2,3N/4]\), \(X=|J|=N/4\), and \(z=N^\eta\). A rough row \((P,h)\) consists of an actual prime \(P\in N-J\) with \((P,N)=1\), a tag \(h\mid y=N-P\), and \(P^-(y)\ge z\). Its weight is \(w_h\log P\). Let \(T\) be their total weight, and put
\[
 V_N(z)=\prod_{\substack{r<z\\r\nmid N}}\left(1-\frac1{r-1}\right),
\]
over primes. Since \(2\mid N\), no factor vanishes. Uniformly for fixed \(\eta>0\),
\[
 V_N(z)\asymp \frac{\mathfrak S(N)}{\eta L}. \tag{2}
\]
Indeed, compare to \(\prod_{r<z}(1-1/r)\) by the absolutely convergent twin-prime correction and the factors \((r-1)/(r-2)\) for \(r\mid N\). Target primes above the cutoff omitted in that comparison cost \(1+O(L/z)\). The same local density has a uniform dimension-one sieve bound: omission of primes dividing \(N\) only decreases the product of inverse local survival factors.

### 1. The actual small-factor log mass

Fix a tolerance \(\tau>0\). Take a fixed large \(s=s(\tau)\) for the fundamental lemma of the dimension-one sieve. Use lower and upper sieve coefficients \(\lambda_d^\pm\) supported on squarefree divisors of \(\prod_{r<z,r\nmid N}r\), with \(d\le z^s\), of uniformly bounded magnitude, such that
\[
 \sum_d\frac{\lambda_d^-}{\varphi(d)}
           \ge(1-\tau)V_N(z),\qquad
 \sum_d\frac{\lambda_d^+}{\varphi(d)}
           \le(1+\tau)V_N(z). \tag{3}
\]
The corresponding divisor sums sandwich the actual small-prime exclusion indicator. These statements hold for all sufficiently large \(N\); they require no congruence properties of the tags.

The prime log mass in \(N-J\) in the reduced class \(N\bmod m\) is \(X/\varphi(m)+R_N(m)\). Ordinary Bombieri–Vinogradov, with the maximum over residues and endpoints, gives
\[
 \sum_{m\le N^{1/2-\eta},(m,N)=1}|R_N(m)|\ll_{A,\eta}N L^{-A}
\]
for every fixed \(A\). To use the version for \(\psi\), delete proper prime powers; their summed trivial bound on this strict power-subroot modulus range is \(O(N^{1-\eta}\log^2N)\). We can omit actual prime inputs \(P\mid N\) also from all these estimates: for each such \(P\), the deletion only affects moduli dividing \(N-P>0\), of which there are \(N^{o(1)}\). The total log cost of deleting all those inputs in the summed remainders is \(N^{o(1)}\). After deletion, \((N,y)=1\), so sifting primes not dividing \(N\) gives exactly the desired roughness.

The supports of \(d\) and all tag primes are disjoint, and the modulus \(hd\) recovers both by its primes below and above \(z\). We choose parameters so that \(\xi+s\eta<1/2-\eta\). By (3) and Bombieri–Vinogradov,
\[
 (1-\tau-o(1))X V_N(z)H_N\le T
 \le (1+\tau+o(1))X V_N(z)H_N. \tag{4}
\]
The assumption \(H_N\ge L^{-C_0}\) makes the error relative and uniform.

Put \(\beta=1/2-\rho>\xi\) and \(Q_h=\min(N^\beta,N^{1/2-(s+1)\eta}/h)\). Take \(\eta\) small enough that \(Q_h\ge z\) throughout the bank. Define the recorded small log mass in a rough row to be
\[
 \log h+\sum_{\substack{z\le q\le Q_h\\q\mid y,\ q\nmid hN}}\log q, \tag{5}
\]
summing over primes \(q\). All prime factors counted in (5) are distinct and at most \(N^\beta\); their exponents in \(y\) do not enter.

Apply the lower bound in (3) to each log contribution, with modulus \(hqd\le N^{1/2-\eta}\) for its extra mark, and \(hd\) for the \(\log h\) term. From \(hqd\), the primes below \(z\) determine \(d\). There are at most \(O_\eta(1)\) choices for \(q\) among the other prime factors, then \(h\) is determined. Thus summing errors even with the \(\log q\) factor still gives arbitrary log saving. The exact local multiplier for the extra prime is \(1/(q-1)\). By Mertens' first theorem and convergence of \(\sum_q\log q/(q(q-1))\),
\[
 \log h+\sum_{\substack{z\le q\le Q_h\\ q\nmid hN}}\frac{\log q}{q-1}
 \ge \left(\frac12-\max\{\rho,(s+1)\eta\}-\eta-o(1)\right)L, \tag{6}
\]
uniformly in the bank. Here primes above \(z\) dividing \(hN\) cost only \(O(\log(hN)/(z-1))\). By (3), (4) and (6), the total of (5) over the weighted rows is at least \((1/2-\varepsilon)TL\) for any chosen fixed small tolerance \(\varepsilon>0\), with parameters chosen as below.

Since \(\log y\le L\) and the primes in (5) are disjoint from those above \(N^\beta\), the total remaining distinct-large-prime log mass satisfies
\[
 \sum_{(P,h)\ {\rm rough\ rows}} w_h\log P
       \sum_{\substack{q\mid y\\ q>N^\beta\ {\rm prime}}}\log q
 \le (1/2+\varepsilon)TL. \tag{7}
\]
This concerns actual factors, not a prime model for the large-factor statistic.

### 2. The narrow band of large factors cannot take all the rows

Take a small fixed \(\delta>0\), with \(\delta<(1/2-\xi)/4\) and \(\rho\le\delta/100\). Let \(T_{\rm near}\) be the weight of rough rows with \(N^\beta<P^+(y)\le N^{1/2+\delta}\). For any such row choose a prime \(q\mid y\) in this interval and write \(a=y/q\). Then
\[
 P=N-aq,\qquad \frac12 N^{1/2-\delta}\le a
                      \le\frac34N^{1/2+\rho}. \tag{8}
\]
Both \(q\) and \(P\) are actual primes. Also \((a,N)=1\), \(a\) is odd and \(z\)-rough, and \(h\mid a\) because \(P^+(h)\le h\le N^\xi<N^\beta\) for any nonunit tag.

For each fixed admissible \(a\), the two-linear-form upper sieve for \(q,N-aq\) in \(J/a\) bounds the number of these prime pairs by
\[
 \ll \frac{N}{aL^2}\mathfrak S(N)
       \prod_{r\mid a}\frac{r-1}{r-2}
 \ll \frac{N}{aL^2}\mathfrak S(N). \tag{9}
\]
At \(2\) the local pair of forms forbids just one class. Each odd prime forbids two classes unless it divides \(aN\), when it forbids one, giving the displayed Euler factors. By (8) the interval in \(q\) has length \(\asymp N/a\), with logarithm comparable to \(L\) by absolute constants. An upper sieve may use a fixed small power of this length, strictly below either prime value being counted. The additional product is \(1+O_\eta(1/z)\), since \(a\le N\) has at most \(1/\eta\) prime divisors, all at least \(z\). Thus the implicit constant in the last bound is absolute for all sufficiently large \(N\).

For fixed \(h\), write \(a=hb\). Its interval in (8) places the \(z\)-rough integer \(b\) above \(N^{1/2-\delta-\xi}/2\), in \(O((\delta+\rho)L+1)\) dyadic intervals. Choose \(\eta\) small relative to \(1/2-\delta-\xi\). The one-form upper sieve on a dyadic interval of integers of size \(U\) gives \(O(U/(\eta L))\) such rough integers. Indeed use level a fixed small power of \(U\), trivial congruence errors, and Mertens' theorem; the implied constant is absolute with these margins. Consequently
\[
 \sum_{\substack{a\text{ as in (8)},\ h\mid a\\P^-(a)\ge z}}\frac1a
 \ll\frac{\delta+\rho+L^{-1}}{h\eta}. \tag{10}
\]
Multiplying (9) by \(\log P\le L\), allowing multiple choices of \(q\) in the upper bound, and summing (10) against \(w_h\) now gives
\[
 T_{\rm near}\ll
  (\delta+\rho+L^{-1})\frac{N\mathfrak S(N)}{\eta L}H_N, \tag{11}
\]
using \(\sum_h w_h/h\le H_N\). The target-divisor factors are shared between (2) and (11); no boundedness of \(\mathfrak S(N)\) is necessary.

### 3. Balance on a positive fraction of the weighted rows

First choose \(\delta\) smaller than \(10^{-3}\), \((1/2-\xi)/4\), and a sufficiently small absolute constant from (2), (4), (9)–(11) for \(T_{\rm near}\le T/4\). The comparison constants there are uniform under the stated sieve margins for large \(N\). Set \(\varepsilon=\delta/8\), choose \(\tau\ll\varepsilon\), then \(s=s(\tau)\), and \(0<\rho\le\delta/100\). Finally choose \(\eta>0\) sufficiently small relative to \(\delta/(s+2)\), \(1/2-\delta-\xi\), and \(\beta-\xi\). These choices give all the margin and tolerance conditions above. One may decrease \(\eta\) further to accommodate fixed tag windows.

Let \(T_B\) be the weight of rough rows with \(P^+(y)\le N^\beta\). A near row contributes at least \(\beta L\) to the prime-log sum in (7), and any other unbalanced row contributes more than \((1/2+\delta)L\) from its largest prime alone. Therefore
\[
 (1/2+\delta)T_B
 \ge (\delta-\varepsilon)T-(\delta+\rho)T_{\rm near}
 \gg\delta T. \tag{12}
\]
This does not assume uniqueness of a prime above \(N^\beta\). A nonsquarefree rough \(y\) has a square factor \(q^2\) with prime \(q\ge z\), hence there are \(O(N/(z-1))\) such \(y\le N\). Each has at most \(2^{\lfloor1/\eta\rfloor}\) tags even before squarefreeness, so their log-weighted loss is \(o(T)\). Divide (12) by \(L\), use (2) and (4), and absorb the fixed parameters into the constant. This proves (1). The untagged assertion takes \(h=1,w_1=1\). Since \(y\in J\), for large \(N\), \(N^\beta<\sqrt y\). A prime has largest prime factor \(y\), and a squarefree semiprime has largest prime factor strictly above \(\sqrt y\); neither occurs in the reservoir. The upper bound on factor count follows from multiplying factors at least \(N^\eta\).

## Scope and comparison

The proof uses the classical fundamental lemma, the ordinary upper sieve for two linear forms, and ordinary Bombieri–Vinogradov, not a greater-than-square-root prime-distribution theorem. See [Sieve Methods](https://ford126.web.illinois.edu/sieve2023.pdf) for the upper and lower sieve inputs and Bombieri's primary [On the large sieve](https://doi.org/10.1112/S0025579300005313) for the distribution method. The point of (7)–(12) is a moving-target, two-sided **factor-size** restriction with genuine prescribed divisor tags, not primality detection.

For fixed shifts much stronger upper bounds on the largest factor are known. [Baker–Harman, *Shifted primes without large prime factors*, Theorem 1](https://matwbn.icm.edu.pl/ksiazki/aa/aa83/aa8342.pdf) fixes the shift and allows its threshold to depend on the shift. [Lichtman, *Primes in arithmetic progressions to large moduli and shifted primes without large prime factors*, Theorem 1.1](https://arxiv.org/abs/2211.09641) gives the exponent \(0.2844\) for infinitude with fixed shift \(-1\), and discusses Friedlander's earlier positive-proportion result. These statements do not supply the moving shift \(y=N-P\) or the simultaneous lower cutoff and tag bank above. In the distributional direction [Bharadwaj–Rodgers, *Large prime factors of well-distributed sequences*, Lemma 8 and Theorem 11](https://doi.org/10.4153/S0008439526101982) distinguish sub-level prime-factor correlations from the largest-factor law, and obtain a general near-one upper tail. The September 2026 preprint [*The Poisson–Dirichlet law for prime predecessors*](https://github.com/openai/math/tree/main/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026) specifically treats \(P-1\), not this moving reflected family. This comparison is not a priority claim.

The weighted rows here are all **composites**. The theorem does not pick out rank three among the bounded ranks, distinguish their rank parity, or prove a positive signed angular sum. In particular it does not prove that \(N\) is a sum of two primes.

## A positive part of the no-small composite score

Choose the fixed completion exponent smaller than \(\eta/2\), so on every retained untagged row there is only the free cofactor 1. At the own root its score is \(2\sum_{d\mid y,\ d>\sqrt y,\ \mu(d)=1}\log(y/d)\). It is at least \(2\eta\log N\): for odd rank omit one prime; for even rank four choose the largest two primes (strictly larger in product than the smallest two); at any higher even rank omit the two smallest primes. Every chosen divisor is even-rank, larger than the root, and has a nonempty complement. The actual signed sum over this reservoir is consequently positive of order at least \(N\mathfrak S(N)\). Using the same cofactor weights, widening to the [reciprocal gap](../wide_gap_all_terminal/Proof.md) of width \(U=o(1)\) changes this sum by only \(O_\eta((U+1/\log N)N\mathfrak S(N))\): each changed orientation has polynomially rough divisor and cofactor, so the true two-form rough/prime upper sieve costs \(O_\eta(N\mathfrak S(N)/(d(\log N)^2))\), and the rough harmonic mass for the divisor in its actual collar is \(O_\eta(U+1/\log N)\). The two logarithmic weights cancel the two log losses from the upper. This identifies a specific positive part, not an independent reserve to add to any overlapping part already counted, and does not control the fully rough score after centering.
