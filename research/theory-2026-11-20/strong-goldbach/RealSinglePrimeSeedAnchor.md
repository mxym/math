# A real single prime entrance to prescribed small factor seeds

An unconditional CRT–Linnik construction selects actual prime-opposite source rows with controlled first factors. Its application to an entirely all-composite forward orbit, and hence to the moving-seed rank theorem, is conditional on a no-prime-pair target (or on checking that the relevant actual orbit is all-composite).

## 1. A single entrance in a controlled range

Let \(N\) be even, \(L=\log N\), \(R=\operatorname{rad}(N)\le L^b\) for a fixed \(b>0\). Let \(P\) be any prescribed set of \(s\) distinct odd primes not dividing \(N\), all at most \((\log L)^2\), with
\[
 s\le \left\lfloor c\,\frac{\log L}{\log\log L}\right\rfloor
\]
for fixed \(c>0\). There are enough such primes: at most \(O_b(\log L)\) divide \(N\), whereas the number of primes up to \((\log L)^2\) is \(\gg(\log L)^2/\log\log L\) by ordinary prime counting. Put \(Q=\prod_{q\in P}q\), so \(Q\le L^{2c}\), and \((Q,R)=1\). CRT gives a class
\[
 a\equiv N\pmod Q,\qquad a\equiv 1\pmod R.
\]
It is reduced modulo \(QR\): no prime of \(Q\) divides \(N\), and none of \(R\) divides \(1\). The absolute-exponent form of Linnik's theorem gives an actual prime \(p\equiv a\bmod QR\) with
\[
 p\ll (QR)^{C_{\mathrm{Lin}}}\le L^{C_{\mathrm{Lin}}(b+2c)},
\]
where the implied constant and exponent are absolute. Only existence of an absolute exponent is used. References: [Linnik, *On the least prime in an arithmetic progression. I*, 1944](https://www.mathnet.ru/php/archive.phtml?jrnid=sm&option_lang=eng&paperid=6196&wshow=paper), [Linnik, Part II, the complete proof](https://www.mathnet.ru/links/bb88ec18ed21db0f8a9239aee7741f6f/sm6202.pdf), and [Xylouris, *On the least prime in an arithmetic progression and estimates for the zeros of Dirichlet L-functions*, Acta Arith. 150 (2011)](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/150/1/83078/on-the-least-prime-in-an-arithmetic-progression-and-estimates-for-the-zeros-of-dirichlet-l-functions).

For sufficiently large \(N\) this actual prime \(p\) is less than \(\sqrt N\), is odd because \(2\mid R\), is coprime to \(N\), and is not any \(q\in P\) because its class is reduced modulo \(Q\). Each \(q\in P\) divides the actual \(N-p\). If \(s\ge2\), this initial complement is genuinely composite without any hypothesis on the existence of other pairs.

## 2. What this says about a single forward orbit

At a hypothetical Goldbach exception the joint factor-orbit closure starting at \(P\) is contained in the **one** genuine all-composite orbit starting at this \(p\), because every \(q\in P\) is an actual first successor. The two closures need not be equal; \(p\) could already lie downstream of \(P\), and the new entrance can have further prime factors. This step makes the rank conclusion realizable at a single small actual root, rather than only a union over many small roots.

For instance take \(b,c,\theta>0\) with \(b+c+\theta<1\) and \(s=\lfloor c\log L/\log\log L\rfloor\). Apply [the moving-prime Kummer seed-rank theorem](SmallRadicalGrowingSeedKummer.md) to the actual closure of \(p\) with the designated \(s\) descendants as its seed-coordinate test. If that one closure has size \(\le L^\theta\) then its corank is at least \(s\), every feedback vertex set has size at least \(s+1\), and the singular-SCC consequences apply with their usual size conditions. Otherwise this actual polylogarithmic input \(p\) individually has an all-composite orbit exceeding \(L^\theta\). The DAG/branching variants can replace the total size assumption with their retained-cost assumption on that same orbit. No independence is claimed for a large orbit absent such a bound. It is also valid to include \(p\) among the tested tiny seeds if desired: it is another unit prime of fixed polylogarithmic size, and adding a fixed one seed changes only the \(L^{o(1)}\) factor in the proof.

## 3. Several genuinely distinct entrances, with exact first-step markers

Let \(M=\lfloor d\log L/\log\log L\rfloor\) for fixed \(d>0\). Choose \(M\) distinct additional odd unit primes \(r_j\le(\log L)^2\), disjoint from \(P\). For every subset \(J\subseteq\{1,\ldots,M\}\), choose
\[
 a_J\equiv N\bmod Q,\qquad a_J\equiv1\bmod R,\qquad
 a_J\equiv \begin{cases}
 N\bmod r_j & j\in J,\\
 -N\bmod r_j & j\notin J .
 \end{cases}
\]
All are reduced modulo the same \(RQ\prod_j r_j\le L^{b+2c+2d}\), and the classes are distinct because \(N\not\equiv -N\bmod r_j\) for an odd unit marker. Linnik gives \(2^M\) distinct actual prime inputs \(p_J\) of fixed polylogarithmic size, disjoint from the marked primes. Each real \(N-p_J\) is divisible by all prescribed \(q\in P\), and among the marked \(r_j\) is divisible by exactly those in \(J\). In particular the singleton choices give real entrances with private first-step markers. This is about the actual row at each input; it asserts neither disjoint downstream closures nor different eventual SCCs.

Alternatively, to force one entrance outside a previously given small set, use a single auxiliary prime \(r\) greater than both \(|C_0|+1\) and every divisor of \(RQ\), with \(r\) of fixed polylogarithmic size whenever \(|C_0|\le L^a\) for fixed \(a\) (Bertrand suffices after increasing the fixed exponent slightly). Combine the original CRT conditions with every nonzero class modulo \(r\), and apply Linnik to the common modulus \(RQr\). There are \(r-1>|C_0|\) distinct entrance primes, so one lies outside \(C_0\). In particular if \(C_0\) is the small joint closure of \(P\), the corresponding entrance's closure strictly contains it. This says nothing about whether the other entrances reach this new one.

This construction may designate an exact valuation \(e\ge1\) at an odd unit marker \(r\) by using \(p\equiv N-r^e\bmod r^{e+1}\); put \(p\equiv-N\bmod r\) for valuation zero. These classes are reduced. The same polylogarithmic bound applies when the product of the resulting prescribed prime powers is of fixed polylogarithmic size. There is no assertion that the undesignated part of \(N-p\) is prime or has bounded arity.

## 4. Unconditional remainder obstruction for tiny supports

There is a simple local check on that undesignated part. Fix \(0<b<1\), \(0<c'<1-b\), \(B>0\). At a center with \(R\le L^b\), for any genuine unit prime \(p\le L^B\), the complement \(N-p\) cannot have all its distinct prime factors \(\le L^B\) and at most \(\lfloor c'\log L/\log\log L\rfloor-1\) of them. Otherwise the single original row \(e_p-(v_q(N-p))_q\), with \(p\) not a divisor of its own complement, is a nonzero integer relation on at most \(\lfloor c'\log L/\log\log L\rfloor\) distinct true small units, with coefficient magnitudes \(O(L)\). Its squared product minus 1 is nonzero and divisible by every \(\ell^{v_\ell(N)}\). At the maximizing local prime, Yu–Kummer as in the small-radical seed theorem gives at most \(L^{b+c'+o(1)}\) (the exponent size only contributes \(O(\log L)\)), contrary to the actual \(L^{1-o(1)}\). Thus if \(P\) has scale constant \(c<c'<1-b\) and \(B\) is chosen to cover the fixed polylog bound for the selected Linnik root as well as its prescribed primes, either the complement has a prime factor above \(L^B\), or it has at least \((c'-c+o(1))\log L/\log\log L\) additional distinct factors beyond \(P\). This local remainder restriction does not require (or produce) a Goldbach pair.
