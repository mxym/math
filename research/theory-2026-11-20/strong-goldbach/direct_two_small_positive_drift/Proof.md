# A quantitative actual positive drift in the direct two-small signed ledger

This gives a **signed-ledger reserve**, not a bound on its residual Möbius difference. In the direct fixed-target score of [the exactly-two-small proof](../direct_two_small_pairing/Proof.md), every sufficiently large even target has an explicit strictly positive paired drift, on the *same* actual outer/lower divisor range as the unresolved antisymmetry. It comes from true reflected primes, by a distribution theorem for a selected factorization of a genuine over-root modulus. No prime-pair existence is inferred.

Use that proof's notation \(N=2x\), \(L=\log x\), \(\ell=\log L\), \(z=\exp(L/\ell^2)\), \(y\in[x,1.5x]\), \(R=\sqrt y\), \(A(N-y)=\log(N-y)1_{N-y\ {\rm prime}}\), and \(\mathfrak S(N)\). Set \(\epsilon=10^{-6}\) and \(C_y=y/x^{1-\epsilon}\). For any fixed \(0<\alpha<\epsilon/10\) define
\[
 W_\alpha(N)=
 \sum_{\substack{y=p q d v\in[x,1.5x],\ y\ {\rm squarefree}\\
        x^\alpha\le p<q<C_y,\ p,q\ {\rm prime}\\
        P^-(dv)\ge C_y,\ R/p<d\le R}}
         A(N-y)\,2\log(q/p).                                   \tag{1}
\]
Everything in (1) is literal, including the shared reflected prime. The macro divisor \(d\) and its cofactor \(v\) are actual integers, not assumed prime. The sum counts labeled macro divisors on the physical \(y\)'s; \(p,q\) are its two unique eligible small primes.

**Theorem.** For all sufficiently large prescribed even \(N\),
\[
                   W_\alpha(N)>7\cdot10^{-7}\,\mathfrak S(N)x. \tag{2}
\]
In addition, for \(\alpha\) sufficiently small (chosen after the fixed \(\epsilon\)),
the **entire exactly-two-small contribution** of the moving-gap score in the preceding note is at least
\[
               5\cdot10^{-7}\mathfrak S(N)x
                       -\mathcal T_{\epsilon,\alpha}(N),       \tag{3}
\]
where \(\mathcal T_{\epsilon,\alpha}\) is the literal signed Möbius difference (7) in that note. It is not estimated here. Even a favorable estimate for that difference would leave other small-factor families and their shoulders unresolved.

## 1. The retained drift for both macro parities

The own-square-root pairing in the preceding note is \(d\leftrightarrow v=M/d\) when \(y=pq M\). Represent each outer/lower pair by its outer divisor \(d\). On \(\mu(M)=-1\), its exact score is
\(\log y-2\log v-\mu(d)\log y\).
Since \(v=R^2/(p q d)<R/q\), the first term is \(>2\log q\). On \(\mu(M)=+1\), the paired score is \(2\log(d/v)\) when \(\mu(d)=\mu(v)=+1\), and \(2\log(pq)\) when both equal \(-1\). In the first case \(d/v>q/p\), since \(d>R/p\) and \(v<R/q\). Thus on every such pair, irrespective of parity,
\[
     B_{\rm pair}(y;d)
       \ \ge\ 2\log(q/p)-\frac12(\mu(d)-\mu(v))\log y .          \tag{4}
\]
All middle-strip terms are nonnegative. In particular a lower for the drift does **not** require counting odd macro parity, nor any other hidden primality beyond the real reflected prime.

## 2. True prime occupancy on a selected actual outer chart

Inside (1) choose the actual small primes in the disjoint bands
\[
 x^{.2\epsilon}\le p\le x^{.3\epsilon},\qquad
 x^{.7\epsilon}\le q\le x^{.8\epsilon},
\]
choose \(d\) with \(x^{.5-.18\epsilon}<d\le x^{.5-.10\epsilon}\), and require \(P^-(d),P^-(v)>2x^\epsilon\). For every \(y\in[x,1.5x]\) these choices ensure the correct own-root strip, *without* replacing it by a different weight: \(p d>x^{.5+.02\epsilon}>\sqrt{1.5x}\) eventually, and \(d<x^{.5}\le\sqrt y\). They also give \(p<q<C_y\), \(P^-(dv)>C_y\), and \(2\log(q/p)\ge.8\epsilon L\). Thus this is an actual subpopulation of (1) on its literal domain.

For the independent source of the prime progression give \(d\) two genuine prime factors
\[
        x^{.029}\le p_2\le x^{.031},\qquad
        x^{.075}\le p_3\le x^{.078},
\]
and write \(d=p_2p_3d_0\). We will count the set of such \(d\)'s once each. For any chosen \(A_0=p q d\) coprime to \(N\), the physical \(v\)-interval is \([x/A_0,1.5x/A_0]\), and the output prime is \(P=N-A_0 v\in[x/2,x]\). When imposing a sieve divisor \(r\mid v\) the actual prime modulus is **\(A_0r=p q d r\)**, with residue \(N\), not \(N/(p q)\) or a maximized free parameter. Target primes are omitted from the v-sieve; for such primes the original v rows with that divisor would require the large prime \(P\) to equal a small target factor and are already empty.

Use the ordinary dimension-one lower linear sieve in \(v\), with cutoff \(2x^\epsilon\) and level \(x^{10\epsilon}\). To transfer the progression errors use [Maynard, *Primes in arithmetic progressions to large moduli III*, arXiv:2006.08250, Theorem 1.2](https://arxiv.org/abs/2006.08250). The required physical factor slots are
\[
            q_1=p q d_0,\qquad q_2=p_2,\qquad q_3=p_3 r .
\]
The residue on \(q_1q_2\) is the **same actual integer \(N\)** independent of \(q_3\). This verifies the theorem's common reduced residue condition; it does not ask for an arbitrary moving base class depending on this last factor. In dyadic triples of \(q_i\), use the two fixed prime prefixes \(X=x\) and \(X=x/2\). With \(\delta=2\cdot10^{-5}\), the true product exponent is at most
\[
             .5-.10\epsilon+.3\epsilon+.8\epsilon+10\epsilon
             =.500011<.5+\delta.
\]
Thus enlarge one upper endpoint in each actual dyadic packet, for example \(Q_3\), to make \(Q_1Q_2Q_3=X^{.5+\delta}\). This is permitted even at \(X=x/2\), with fixed slack. The enlarged exponent of \(Q_3\) is still \(.075\)–\(.07804\) up to \(o(1)\), since the true lower product has exponent at least \(.5+(.2+.7-.18)\epsilon+o(1)\). The exponent of \(Q_2\) is \(.029\)–\(.031\) up to \(o(1)\). These lie strictly inside both conditions
\[
 .0008<\log_X Q_2<.04986,\qquad
 .10024-\log_X Q_2<\log_X Q_3<.09992-.6\log_X Q_2
\]
of the theorem, with more than .003 fixed room in the last two comparisons. One does not enlarge all three factors independently across the whole source. This handles band and dyad adjustments without a fictitious global product.

Maynard bounds the sum of absolute discrepancies over all allowed factor triples, also for our prescribed common actual residue \(N\). For each actual modulus the number of decompositions and labels \(p,q,p_2,p_3,d_0,r\) is at most a fixed divisor power; there is no unique-choice assumption for the genuine medium labels in \(d\). Insert this power by Cauchy: beside the arbitrary-log discrepancy bound, the trivial absolute bound \(O(x/q^\ast+1+x/\varphi(q^\ast))\) for \(q^\ast=q_1q_2q_3\), summed with any fixed divisor powers, is \(O(xL^C)\) for some \(C\) by the reciprocal divisor moments and \(q^\ast\le x^{.50002}\). The two actual prefixes suffice because all primes tested lie in the same interval \([x/2,x]\). We can first count the primes unweighted and multiply each lower-bound row by \(\log(x/2)\). No maximal prefix with a hidden v-dependent endpoint or derivative is needed.

The local density at a sieve prime \(\ell'\) on the physical v progression is
\[
 g_{A_0}(\ell')=
 \begin{cases}
 0,&\ell'\mid N,\\
 1/\ell',&\ell'\mid A_0,\\
 1/(\ell'-1),&\ell'\nmid A_0N.
 \end{cases}
\]
In the middle line it is essential to retain \(\varphi(A_0)/\varphi(A_0\ell')=1/\ell'\); one cannot treat that factor as coprime to its original modulus. The local Euler product through \(2x^\epsilon\) is \((1+o(1)) e^{-\gamma}\mathfrak S(N)/(\epsilon L)\) uniformly. All primes of \(A_0\) are polynomially large, so its extra local factors differ from the ordinary product by \(1+o(1)\); target primes exceeding \(2x^\epsilon\) contribute \(O(L/x^\epsilon)\) uniformly. The level/cutoff ratio tends to \(10\). The ordinary sieve functions give \(e^{-\gamma}f(s)\ge e^{-\gamma}f(4)=\frac12\log 3>.5\) here. Consequently the lower progression main on the indicated rows, with the actual output prime logarithm, is at least
\[
             \frac{x}{2\,\varphi(A_0)}
                  \frac{.5\,\mathfrak S(N)}{\epsilon L}
\]
before the summed \(O_B(xL^{-B})\) errors, for every fixed \(B\), after summing the selected genuine \(p,q,d\). These errors tolerate arbitrary fixed nonnegative selections of the eligible \(d\)'s because the analytic input was absolute. The factor \(\varphi(A_0)\) is the true residue density rather than an additional factor coming from the v count. This is an actual prime lower, not an upper sieve on the output.

## 3. Explicit main, without mark double counting

We give explicit constants for the required rough harmonic d-mass. Let \(A_2=\log(31/29)\) and \(A_3=\log(78/75)\), the true asymptotic reciprocal masses of their genuine prime bands. They satisfy
\[
                         .06<A_2<.07,\qquad .035<A_3<.04 .
\]
For a designated collection of up to four distinct medium primes, two per band at most, use the actual integer \(d_0=d/\text{(product of tags)}\). Its lower endpoint is at least \(x^{.28}\); its logarithmic interval length is exactly \(.08\epsilon L\), independently of the tag product. Enforce \(P^-(d_0)>2x^\epsilon\) using a one-dimensional sieve on the integers at level \(x^{.05}\). For reciprocal counting, the exact main for \(\sum_{m\equiv0\bmod r}1/m\) on the real interval is \(r^{-1}\) times its logarithmic length, with error \(O(x^{-.28})\) uniformly for \(r\le x^{.05}\). Thus literal floors have a large reserve even when all four labels are retained. Target-unit removal costs negligible harmonic mass: all relevant divisors \(r\mid N\) of an already rough free integer exceed \(2x^\epsilon\) and their reciprocal sum is \(O(L/x^\epsilon)\), with negligible floors. Likewise omitting genuine medium primes or \(p,q\) dividing \(N\) changes their harmonic sums by \(o(1)\). At sieve ratio \(>4\), \(e^{-\gamma}f>.5\) and \(e^{-\gamma}F\le e^{-\gamma}F(3)=2/3\). Thus, conditional on any such fixed medium tag collection, its normalized corrective coefficient for the d-harmonic main is between \(.08\cdot.5\) and \(.08\cdot(2/3)\) in the limit.

Let \(\beta_2(d)\) count the actual possible ordered-by-band tag pairs. Apply \(1_{\beta_2\ge1}\ge\beta_2-\beta_2(\beta_2-1)/2\) to the nonnegative rough unit d-harmonic measure. The first moment has lower main at least
\[
                     .08\cdot.5\cdot.06\cdot.035=.000084.
\]
For the second factorial moment, distinct pairs either share no tag, share only the first, or share only the second. The sums are bounded above by \(A_2^2A_3^2+A_2A_3^2+A_2^2A_3\) times the rough conditional coefficient just proved; these are ordered *different pair choices* and no symmetry factor should be inserted. Thus the factorial moment has upper main at most
\(.08(2/3)(.07^2.04^2+.07.04^2+.07^2.04)<.00001685\).
Uniformity of the harmonic floors can be summed against the products of tag reciprocals; their total is bounded and the floor \(x^{-.28}x^{.05}\) has a power reserve. Hence the actual distinct-d harmonic sum is \(>7\cdot10^{-5}\). For the analytic distribution step we may take any canonical admissible pair for each such \(d\); the sum of its errors is still at most the already bounded absolute error over all tuples. The main is only counted once.

The actual p and q reciprocal masses in their bands exceed .40 and .13, respectively, after the target-unit removal, by prime Mertens. Use \(1/\varphi(p q d)\ge1/(p q d)\) in the positive lower main. Finally if a counted \(y=p q d v\) is not squarefree, a repeated prime is \(>2x^\epsilon\), since the two actual small distinct primes do not divide \(d v\). There are \(O(x^{1-\epsilon}+\sqrt x)\) possible values of such a \(y\); their label multiplicities and log weights cost \(x^{o(1)}\), preserving a power saving. This is also enough to force the original physical unit restrictions beyond the finitely many endpoint primes, if needed by the ambient direct ledger.

Combining the half-x v-prime interval length, the \(.5\) sieve coefficient, the two harmonic prime masses, the distinct-d harmonic lower, and the drift \(.8\epsilon L\) gives
\[
        (.5)(.5)(.40)(.13)(7\cdot10^{-5})(.8)\,\mathfrak S(N)x
        =7.28\cdot10^{-7}\,\mathfrak S(N)x
\]
as a conservative lower before the asymptotic errors. This proves (2). In particular the \(\epsilon^{-1}\) from the lower rough-v sieve has been canceled by the actual \(\epsilon L\) drift; there is not a spurious extra inverse power of epsilon in this reserve.

## 4. Relation to the signed threshold

Apply (4) to every outer pair with \(p\ge x^\alpha\), and retain (1) rather than discard that drift. The preceding proof paid the entire exactly-two clock shoulder at \(o(\mathfrak S(N)x)\), and the genuinely tiny \(p<x^\alpha\) part at \(O_\epsilon(\mathfrak S(N)x\alpha[1+\log(\epsilon/\alpha)])+o(\mathfrak S(N)x)\). Choose fixed \(\alpha<\epsilon/10\) sufficiently small that this latter coefficient is \(<10^{-7}\). The lower subpopulation in (2) still lies within the selected bands. Taking \(x\) large gives (3). We have therefore reduced **this part** of the remaining sign question to an absolute *fixed* threshold on \(\mathcal T_{\epsilon,\alpha}\), not necessarily an \(o(\mathfrak S(N)x)\) bound. The favorable drift may be larger outside the exhibited chart.

The prime input is different from the earlier use of an auxiliary factorable slope with two independent shared-index columns: here the actual residue is the reflection of **a true factorized \(y\) at prescribed \(N\)** and the two macro divisors of (4) belong to that same \(y\). Ordinary Bombieri–Vinogradov does not give the lower just used: even before the v sieve the actual modulus \(p q d>q\sqrt y\) lies above the square root by a fixed power in this chart. A usual Chen reversal produces an upper sieve on a different sequence, not the required true-prime occupancy with this literal \(d\) and v restriction. On the other hand the present Maynard transfer cannot estimate the full antisymmetric \(\mathcal T_{\epsilon,\alpha}\) by simply swapping \(d,v\). It uses the medium tags of the **fixed** macro divisor only. Imposing the counterpart's two medium labels on the free macro would add approximately .105 to the actual modulus and leave the theorem's permitted range. This is a lower on the retained drift, not evidence that the actual Möbius discrepancy is below it, and does not supply a binary Goldbach proof.

For comparison, the [October 2026 preprint by Pham](https://www.preprints.org/manuscript/202610.3061), Section 8 and Appendix A, explicitly retains an unresolved balanced signed boundary and gives a sub-root mixed distribution result; neither estimates this same-divisor signed difference. The [November 2026 preprint of Chan](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf), Theorem 1.1, concerns the allowable relative sizes of two prime factors of a Chen-type complement, rather than this signed drift on a selected true factorization.
