# A joint-marginal parity witness for the coupled smoothing envelope

This note gives a counterexample to the **specific linear envelope which keeps the ordinary divisor moments and profilewise cutoff compensation but forgets the exact equation inside each factorization cell**. It is not a counterexample to any Goldbach representation, to a theorem about genuine solutions of the affine equation, or to a parity-sensitive bilinear estimate. Its construction is a local extension of the Selberg parity witness in the earlier [ArithmeticTwoWeightParityWitness.md](ArithmeticTwoWeightParityWitness.md); the additional features here are the two coupled quotient axes, their exact ordinary joint divisor data, and the compatibility with the two proved negative sectors.

Keep \(x=N/2, L=\log x\), genuine prime \(x^{.10}<s<x^{.14}\), \((s,N)=1\), and the reflected interval \(J=[x,3x/2)\). Put \(M=Ns\). Write
\[
   Q_s(m)=(N-m)/s,qquad
   H_F(v)=1_{(v,F)=1}\mathfrak S(Fv)\quad(F\text{ even}),
\]
and \(a(m)=1-\lambda(m)\), with the ordinary completely multiplicative Liouville function. Use the same \(W_s\), \(M_N=\mathfrak S(N)x/(2L)\), and matched reference \(\mathcal M=(.19567\ldots+o(1))M_N\) from the true unmarked semiprime cell, as in [DoubleSwitchedMain.md](DoubleSwitchedMain.md) and [DoubleSmoothBoundedRankResidual.md](DoubleSmoothBoundedRankResidual.md).

There is an explicit **nonnegative measure on actual integers** \((s,m,q)\) such that \((m q,Ns)=1\), \((m,q)=1\), and \(|sq-(N-m)|\ll x\exp(-L^{1/10})\). It is not supported on \(sq=N-m\). For this measure:
* The ordinary integer-row joint \(d\mid m,e\mid q\) moments have the same unit CRT main as on the physical integer row, below any fixed subcritical \(d e\) level stipulated in (5) below. The prime-quotient marginal has the same relevant ordinary \(d\mid m\) Type I main, with arbitrary log reserve for each prefix.
* Each fixed compact actual prime-product \(m\) profile has the precise matched reference of [CompensationNeutrality.md](CompensationNeutrality.md); all reverse cutoff variations have zero whole effect there to arbitrary log precision. A true-prime \(q\) population in this measure is **twice** that reference on odd squarefree ranks and zero on even ones. These values are within the one-sided arithmetic sieve envelopes used in the coupled notes.
* The fully rough and the marked core sums satisfy the corresponding upper inequalities in [CoupledParityCompensation.md](CoupledParityCompensation.md) on the model measure. Nevertheless the modeled whole residual is \(+\mathcal M+o(M_N)\) for **every** allowed smooth forward/reverse pair and their finite signed cutoff averages of total 1, far above \(.010M_N\).

Thus one cannot certify the wanted inequality by using only these ordinary marginals, their whole cutoff equalities, and these selected actual-sector numerical bounds, in an envelope that otherwise treats the remaining cells as free. This does not exclude constraints exploiting the exact equation or stronger comparisons on those cells.

## 1. Uniform weighted divisor law

For even \(F\le x^C\), set \(b(p)=1/(p-2)\) on odd primes and extend it squarefree multiplicatively. On \((v,F)=1\),
\[
          H_F(v)=\mathfrak S(F)
                      \sum_{g\mid v,(g,F)=1} b(g).
\tag{1}
\]
On an interval of length \(\Delta\) in \([cX,C'X]\) with \(X\ge x^c\) and \(\Delta\ge X\exp(-2L^{1/10})\), the moment of \(H_F\) at \(d\mid v\), uniformly when \(d\le Xx^{-\epsilon}\), is
\[
      \sum_{v\text{ in interval},d\mid v} H_F(v)
      =\frac{\Delta\,1_{(d,F)=1}}{\phi(d)}+O_{A,c,\epsilon,C}
                                      ((X/d)L^{-A}).
\tag{2a}
\]
In such full-length or nearly full-length intervals its error can in fact be made \(O((\Delta/d)x^{-c_1})\) for a positive \(c_1\) depending on the fixed exponent slack. This remains an absolute prefix statement with the same global error budget \(O((X/d)x^{-c_1})\) on arbitrary subintervals of \([cX,C'X]\).

For the proof, the gcd condition in (2a) is necessary and the nonunit case is exact zero. In the unit case sum (1) up to \(g\le G=x^{\epsilon/10}\). Impose \((v,F)=1\) by inclusion-exclusion across \(f\mid\operatorname{rad}(F)\). Here \((f,[g,d])=1\), so the length divided by \(f[g,d]\) in each integer interval has floor error at most 1. The aggregate floor is \(\tau(F)x^{o(1)}\sum_{g\le G}b(g)=x^{o(1)}\). For large \(g\), allowing only positive multiples gives absolute bound
\[
   \ll \frac{X\mathfrak S(F)}{d}
            \sum_{g>G} \frac{b(g)(d,g)}{g}
       \ll \frac{X}{d}G^{-1/4}x^{o(1)}.
\]
The Rankin product after inserting \(g^{1/4}\) converges away from \(d\); at primes dividing \(d\) its log loss is at most \(O(\sum_{p\mid d}p^{-3/4})=o(L)\), uniformly for polynomial \(d\). For example split at \(L^2\) and use that \(d\) has \(O(L)\) prime divisors. This also bounds the corresponding main tail. The complete main relative to \(\Delta/d\) is
\[
  \mathfrak S(F)\frac{\phi(F)}F
   \prod_{p\nmid F}(1+b(p)/p)
   \prod_{p\mid d}\frac{1+b(p)}{1+b(p)/p}
      =\prod_{p\mid d}\frac{p}{p-1}.
\]
Indeed \(1+b(p)/p=(1-1/(p-1)^2)^{-1}\) and the first three factors have product 1 by the exact singular-series normalization. This proves (2a), with its power slack.

On the full positive interval \([x,3x/2)\), the **signed** analogue is
\[
  \sup_{I'\subseteq[x,3x/2)}\left|\sum_{v\in I',d\mid v}
                           H_F(v)\lambda(v)\right|
                     \ll_{A,\epsilon,C} (x/d)L^{-A},\qquad d\le x^{1-\epsilon}.
\tag{2b}
\]
Use (1), the same \(g\)-tail, and truncate the coprimality expansion at \(f\le x^{\epsilon/4}\); the large \(f\mid\operatorname{rad}(F)\) tail is bounded by \(\sum f^{-1}\ll x^{-\epsilon/8+o(1)}\) by Rankin. The \(g\)-weighted harmonic factor, even with \((d,g)\), is log-bounded, or \(x^{o(1)}\) harmless against the polynomial tail. For retained \(f,g\), complete multiplicativity extracts \(\lambda(f[g,d])\). The remaining Liouville sum is on an interval of integers at scale \(x/(f[g,d])\ge x^{\epsilon/2}\); the classical PNT for Liouville gives exponential-in-a-positive-log-power saving compared with that scale, uniformly at prefixes. Summing the retained factors costs only log powers: the actual product \(\sum_g b(g)(d,g)/g\) is \(\ll \prod_{p\mid d}(1+b(p))\), times an absolute constant (so at most a fixed power of \(L\)), and \(\sum_{f\mid\operatorname{rad}(F)}1/f\ll L^C\). This proves (2b). These assertions use only integer values of \(v\) and no distribution of actual prime pairs.

## 2. Construction and preservation of the divisor data

At each \(s,m\in J\) with \((m,M)=1\), use outer mass \(1/(s-1)\). Write \(F=Mm\) and \(Q=Q_s(m)\). Choose a real interval \(I_{s,m}\subseteq[x/(2s),x/s]\) with length \(Q\exp(-L^{1/10})\) and with all points at this distance or less from \(Q\), using a one-sided interval at endpoints. On its integer \(q\)'s, assign the positive probability measure proportional to \(H_F(q)\). By (2a) its normalizing total is \((1+O_A(L^{-A}))|I_{s,m}|\), even with a power saving, and its divisor moments, for each \(e\) with polynomial reserve below \(Q\), are
\[
     \mathbb P(e\mid q)=
              1_{(e,F)=1}/\phi(e)+O_A(e^{-1}L^{-A}).
\tag{3}
\]
The case \((e,F)>1\) is exact zero. Uniformity in the actual \(F=Mm\) follows from \(\log F=O(L)\). Uniform PNT on these long intervals gives the baseline probability
\[
                  P=\mathbb P(q\text{ prime})
                      =\mathfrak S(F)/\log Q+O_A(L^{-A}).
\tag{4}
\]
An extra local factor at a prime \(q\asymp Q\), or at the at most \(O(L)\) excluded divisors of \(F\), is power-negligible. The error in (4) is in fact exponential-in-a-positive-log-power times \(\mathfrak S(F)/L\), by ordinary PNT and the chosen interval length.

With \(Y=x^{.070}\), the same baseline measure has room to redistribute (4) among the fully \(Y\)-rough composites. To see this without any unsupplied tail estimate, apply the lower linear sieve to **ordinary integers** in the same interval at \(D=x^{.280}\) and \(Y\), with exact floor errors and density \(1/p\). Its lower coefficient is \(\log 3/.140-o(1)>7.84\) against \(|I_{s,m}|/L\). Remove primes dividing \(F\) that are greater than \(Y\), with cost \(O(|I_{s,m}| L/Y+L)\), and remove proper prime powers with cost \(O(Q^{1/2}L^C)\). On the surviving \(Y\)-rough integers, \(H_F(q)=\mathfrak S(F)(1+o(1))\) uniformly, since their actual prime factors exceed \(Y\). As \(\log Q\ge(.86-o(1))L\), the total fully rough **composite** nonpower mass \(C_q\) obeys \(C_q>P\), eventually with a large fixed margin. This is just an unrestricted one-dimensional calculation, not an actual shifted pair estimate.

Now multiply the mass of the genuine prime \(q\)'s by \(a(m)=0\) or 2, and multiply the mass of the fully \(Y\)-rough genuine composites other than powers by \(1+(1-a(m))P/C_q\). Do not change any other weight. The new masses are nonnegative, still sum to 1, and all moments \(1_{e\mid q}\) with \(e>1\) composed of primes at most \(Y\) are unchanged **exactly**, since the modified points are all fully rough. The total moment \(e=1\) is also unchanged by construction. The same holds for every prescribed nontrivial small-core bucket, with the actual core transferred intact.

For example for any fixed \(\epsilon>0\), \(e\) supported on primes \(\le Y\), \(e\le x^{.4}\), \(d e\le x^{1-\epsilon}\), and fixed \(s\), the integer-row joint \(d\mid m,e\mid q\) mass over a physical \(m\)-prefix of length \(U\) in \(J\) is
\[
  \frac{U\phi(N)}{N s d e}\,1_{(d e,Ns)=1}\,1_{(d,e)=1}
                + O_A\!\left(\frac{xL^{-A}}{s d e}\right).
\tag{5}
\]
Indeed (3) on the tilted measure is still zero for \((m,e)>1\) and otherwise gives \(1/\phi(e)\). The outer integer count at \(d\mid m\), \((m,M e)=1\), gives \(U\phi(Me)/(d M e)\), with floor error \(O(\tau(Me))\). When permitted, \((e,M)=1\), so multiplication by \(1/((s-1)\phi(e))\) produces exactly (5). The floor reserve is supplied by \(de\le x^{1-\epsilon}\) and \(\tau(Me)=x^{o(1)}\). This matches the physical unit CRT main in \(m\equiv N\bmod se\), \(m\equiv0\bmod d\). In particular \(d=e=1\) matches ordinary integer-row inventory. The factor \(1_{(e,s)=1}\) here is automatic because \(s>Y\), and no comparison for probes at primes in \((Y,x]\) is asserted.

The prime-\(q\) marginal of the same measure on \(m\) is, by (4),
\[
       \frac{1}{s-1}\,\frac{H_{M}(m)a(m)}{\log Q_s(m)}
           +\text{arbitrarily log-small relative-scale error}.
\tag{6}
\]
For each \(s,m\), the error is in fact of arbitrarily log-small size compared with \(\mathfrak S(Mm)/((s-1)L)\), including the exact zero on even ranks. Therefore (2a)--(2b) and partial summation prove the same ordinary \(d\mid m\) Type I mean as for a genuine prime quotient, throughout \(d\le x^{1-\epsilon}\) with \((d,Ns)=1\); the only harmless scale difference from the continuous \(q\)-rate per \(dm\) is \(s/(s-1)=1+O(x^{-.10})\). For any polylog-divisor-weighted sum of these progression errors the harmonic moments absorb the losses. In particular no ordinary such short-divisor probe of this marginal detects the Liouville tilt.

## 3. Whole signed identities and the two selected inequalities survive

All reverse cutoff differences in (3) of [CompensationNeutrality.md](CompensationNeutrality.md) are supported on the literal \(e\)-moments of (3), since \(r k'\le Y^2\). The smooth quotient weights use actual \(q\) values, not new labels for the primes. The q-window variation gives \(\log q=\log Q+O(\exp(-L^{1/10}))\); freezing any output \(W_s(q)\) or the \(1/\log q\) factor has arbitrary log reserve (the divisor envelopes at \(q\) have log-power mean by (3) or elementary divisor moments on the long unrestricted window). Evaluate the two short moments exactly as in that accounting note, now with mask \(F=Mm\) at each \(m\). The first reassembled short piece has expected value \(\mathfrak S(F)/\log Q\); the second is log-small, including its \(p\mid r\) overlap. Together with (4), this gives the model's actual conditional coefficient
\[
                    \mathbb E[B_f(q)\mid s,m]
                      =(a(m)-1)\frac{\mathfrak S(F)}{\log Q}
                        +O_A(L^{-A})
\tag{7}
\]
for every fixed smooth reverse cutoff, signed or not. This proves the full reverse-neutrality on every fixed \(m\) profile, not only after totaling them. On a compact true macro prime-product rank profile \(\mathfrak S(Mm)/\mathfrak S(M)=1+O(x^{-c})\) uniformly. Hence the prime-\(q\) frequency is exactly the rank factor \(1-(-1)^k\) times the reference (1) of that accounting note, up to arbitrary log reserve. It obeys the one-sided sieve upper constants in the coupled sectors (which are strictly more than twice this prime reference on each such profile).

Consider next any allowed forward coefficient \(Z_i\) of the double-smooth reduction. Up to power-small genuine prime powers, its literal form is
\[
           Z_i(m)=\Lambda(m)+(\log m)\sum_{d\mid m}
                                      \mu(d)g_i(\log d/\log m).
]
The \(\Lambda\) cancellation on actual primes is literal as before. Since \(a(m)-1=-\lambda(m)\), in (7) every ordinary divisor sum in the second term above has log-small total by (2b), with \(d\le x^{1/2-c}\), physical partial summation, and harmonic summation of \(1/d\). For the remaining \(\Lambda(m)\) term, \(-\lambda(m)=1\) on actual prime \(m\); proper powers negligible. Ordinary PNT in \(m\), with \(\mathfrak S(Mm)/\mathfrak S(M)=1+o(1)\) uniformly on such primes, thus gives
\[
         \text{model }\sum_{s,m,q} W_s(q)Z_i(m)B_f(q)
                         =\mathcal M+o(M_N).
\tag{8}
\]
The equality of the constant with the true matched reference uses only separate PNT: the prime \(m\) log weight yields the continuum \(dm\) main in \(J\), the denominator \(\log Q_s(m)\) remains, and the outer factor \(1/(s-1)\) may be replaced by \(1/s\) with power error before comparing the separate true semiprime main. Likewise the true-\(q\) modeled \(\Lambda(m)\) term doubles, while the short pieces in the original \(C\) keep their usual means by (6) and (2); hence that model's original true-\(q\) residual is \(+\mathcal M+o(M_N)\) as well. Formula (8) is stable for any fixed finite linear combination of forward and reverse cutoff pairs of total coefficient 1.

Finally, the two negative sectors proved for the coupled kernel are **consistent** with this adverse value. On no-core q the only changed internal split is the prime/composite split. Even after doubling the prime mass, the actual rough-composite **model** mass on each macro \(m\) profile is at least
\[
          (7.84-2/.86-o(1))\frac{\mathfrak S(Ns)}{L}
                                  > 2.20\frac{\mathfrak S(Ns)}{L}.
\]
The same dimension-one upper sieve is available from the unchanged ordinary small-divisor moments (3), so half-neck even-mass bounds are unaffected. Thus the controlled no-core triprime lower and whole negative upper of the coupled proof still hold. On the two marked cores, all conditional small-core masses are unchanged **exactly** in the redistribution. The local upper/lower sieve bounds for these marks follow directly from (3) with \(e\) replaced by the product of the core \(pt\) and the corresponding short sieve modulus, with the same \(p\mid pt\) normalization \(1/p\) and modulus margin. Since all macro m factors exceed \(Y\), the original matched local factors are unchanged up to power error on the outer \(m\) factor. The same rank-two negative and rank-four positive arithmetic comparison therefore establishes the second selected bound in this model. Consequently even imposing both selected inequalities and exact cutoff neutralities cannot force the desired inequality in any linear envelope that otherwise forgets the pointwise equation.

The model is a positive law on **nearby** ordinary prime factorizations, with actual prime labels where used; weighting them is not proof there is an exact solution. In particular it does not assert joint distribution in a prime-conditioned cell of the true equation \(m+sq=N\). Such a coupled estimate, or another input that genuinely distinguishes the physical equation from these ordinary marginals, remains necessary for this strategy.

## Prior parity analyses

See [Ford's sieve notes](https://ford126.web.illinois.edu/sieve2023.pdf) for the classical Selberg–Liouville example and [Arneth's October v1](https://zenodo.org/records/23560521) for a distinct finite Bonferroni–Liouville transfer program. The model here deliberately weakens the exact affine equation and therefore does not establish an impossibility theorem for an envelope retaining that equation or true prime-sensitive dispersion.
