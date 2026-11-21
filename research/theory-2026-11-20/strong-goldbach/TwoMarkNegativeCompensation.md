# A two-small-mark q sector with a net negative signed estimate

Keep the exact \(\mathcal T_{\rm v}(C^\dagger)\), \(C^\dagger=C+P-J\), \(M_N=\mathfrak S(N)x/(2\log x)\), and the true \(W_s(q)=K_{P_3}(sq)\) from [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md). Use the complete prime \(s\)-band \(x^{.10}<s<x^{.14}\), \(\kappa_s=1\), \(n=sq\in I\), \(m=N-n\), and \((n,N)=1\). Retain the genuine old reverse thresholds \(U_q=x^{.070},V_q=x^{.010},E=x^{.080}\). Consider the following artificial-quotient sector:
\[
 \mathcal Q_2:\quad
 q=p t w,\qquad p<t\ {\rm actual\ primes},\quad
 x^{.036}\le p,t\le x^{.069},\qquad P^-(w)\ge x^{.071}.
\tag{1}
\]
The variable \(w\) is otherwise an arbitrary rough integer, not asserted prime. Two actual pointwise conclusions, both for all sufficiently large even \(N\), are:

* On (1) with \(m\) a genuine squarefree semiprime having both prime factors at least \(x^{.120}\), the signed contribution to \(\mathcal T_{\rm v}(C^\dagger)\) is at most \(-.180 M_N\).
* On **all** of (1) with \(P^-(m)\ge x^{.120}\), without excluding any rank or any sign of its terms, the signed contribution is at most \(-.040 M_N\).

These are two alternative accounting statements for overlapping sectors: do **not** add them. The second controls positive terms in addition to the negative semiprime terms. Either sector is disjoint from [NegativeRankFourCompensation.md](NegativeRankFourCompensation.md), since that one has \(P^-(q)\ge x^{.071}\), and (1) has exactly two actual primes smaller than \(x^{.071}\). The whole complement is not controlled.

## 1. The exact positive reverse coefficient and negative m-semi sign

At a tuple (1), the two marks are uniquely determined by \(q\) in increasing order. They are coprime to \(w\), and all nontrivial divisors of \(w\) exceed \(U_q\). Both marks individually are below \(U_q\), but their product is above \(U_q\). Compute the genuine \(C_q^{\rm hi}(q)\) by considering its actual von Mangoldt argument \(k\).

* If \(k\mid w\), write the \(r\)-part dividing \(q/k\) as \(r=r_0\cdot a\) with \(r_0\mid w/k\) and \(a\mid pt\). For \(r_0>1\), all four choices of \(a\) satisfy \(r>U_q,r k>E\), so cancel by \(\sum_{a\mid pt}\mu(a)=0\). This is exact even if \(r_0\) is nonsquarefree. For \(r_0=1\), only \(a=pt\) satisfies \(r>U_q\); it has sign \(+1\), and \(pt\,k>E\) whenever \(\Lambda(k)\ne0\) in this case. Thus all \(k\mid w\) contribute \(\sum_{k\mid w}\Lambda(k)=\log w\).
* If \(k=p\), the remaining \(r\) divides \(tw\). Every nontrivial \(w\)-part puts \(r>U_q,rk>E\), independently of whether it is multiplied by \(t\); those two choices cancel. The \(w\)-part 1 gives no \(r>U_q\). Interchanging \(p,t\) is identical. There is no other \(k\) with \(\Lambda(k)\ne0\) because the two marks are distinct and occur only once.

Therefore
\[
                    C_q^{\rm hi}(q)=\log w .
\tag{2}
\]
On the central range, \(\log q\ge .86L-O(1)\), \(\log q\le .90L\), and \(.072 L\le\log(pt)\le .138L\), where \(L=\log x\). In particular,
\[
                     .83<\frac{\log w}{\log q}\le .92
\tag{3}
\]
eventually. This is opposite to the exact sign on the rough-composite sector of the previous note.

If \(m\) has all its prime factors at least \(x^{.120}\), the three cutoff errors of (10) in [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md) vanish literally. Its initial two sums are the symmetric min test
\[
 \sum_{a\mid m}\mu(a)\min\{\log a,\log(m/a)\}
\tag{4}
\]
up to \(O(\tau_2(m)\log H)\) from the moving neck, where \(H=\exp(L^\eta)\), \(0<\eta<1\). For squarefree semiprime \(m=u v\), \(u<v\), (4) is \(-2\log u\). Hence \(C^\dagger(m)=-2\log u+O(\log H)\), both a genuine negative sign and a uniform relative \(o(1)\) weight error on this sector.

## 2. Sieve counts on actual prime products with the two marks

Fix \(s,p,t\) in their respective bands, all units modulo \(N\), and let \(b=s p t\). On any of the actual \(m\)-prime-product sequences below, impose \(m\in N-I\), \((m,N)=1\) and the physical relation \(m\equiv N\bmod b\). Then \(w=(N-m)/b\) is the actual free quotient. For each squarefree sieve divisor \(e\) composed of primes \(<z=x^{.071}\) not dividing \(N b\), the exact condition \(e\mid w\) is \(m\equiv N\bmod b e\). All tested \(m\)-factors are at least \(x^{.120}>z\), so none meet the sieve \(e\). The true reduced reference is thus \(X_b/\phi(e)\), with
\[
             X_b=\frac1{\phi(b)}
                      \sum_{\substack{m\in N-I\\(m,Nb)=1}} a_m
\tag{5}
\]
for the nonnegative exact product weight \(a_m\) being tested. The unit reduction at \(s,p,t\) is not omitted. If any of the labels divides \(N\), the original physical term is absent. The marks are necessarily distinct from \(s\) by their disjoint bands, but \(s\) could be an \(m\)-factor, so \((m,s)=1\) is still retained in the model (5).

The sum of absolute remainders in this model is \(O_D(xL^{-D})\) through \(e\le x^{.217}\), simultaneously over all \(s,p,t\). This is [Maynard I Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733) at the true scale \(m\asymp x\): the actual moduli satisfy \(b e\le x^{.14+.138+.217}=x^{.495}\). A fixed modulus has \(O(1)\) possible prime-divisor choices from each of the named \(s,p,t\) bands, since even the smallest of those primes is of fixed polynomial size; \(e\) is determined after the labels. Use ordered \(k\)-prime products divided by \(k!\) for \(2\le k\le8\), with genuine unit masks on each factor and polynomial factor lengths, grouped as one prime and a complementary product of \(k-1\) primes. Both groups meet the polynomial lengths condition. The prime factor used for SW is independent of the test on the modulus. Logarithmic meshes on individual prime factors enforce the sharp central product and any required exponent intervals: the resulting errors on physical \(m\) use divisor moments on the central edges and the original modulus dividing \(N-m\) with divisor multiplicity; the reduced-sum edges use the harmonic modulus weights, as in §2 of [NegativeRankFourCompensation.md](NegativeRankFourCompensation.md). A fixed log-smooth or Lipschitz product weight, such as \(2\min(\log u,\log v)/L\), can be frozen on each fine prime-factor rectangle with arbitrary log accuracy. Thus the BV statement for the **weighted** semiprime is verified as well as for the unweighted products. Repeated primes of \(m\) are later paid by the square-divisibility bound \(O(x^{.88})\) times divisor weights, since all its factors lie above \(x^{.120}\).

For this actual sieve sequence \(g_b(\ell)=1/(\ell-1)\) at primes \(\ell\nmid N b\) and 0 at \(\ell\mid N b\); its dimension-one condition is uniform as before. The exact mixed local factor is
\[
               V_b(z)=(1+o(1))\frac{e^{-\gamma}\mathfrak S(N s p t)}
                                                     {.071 L}.
\tag{6}
\]
The omitted primes dividing \(N b\), including 2, are treated as in (6) of [NegativeRankFourCompensation.md](NegativeRankFourCompensation.md), using the true local factor \((\ell-1)/(\ell-2)\) at each odd omitted prime. In particular (6) does not expect another small-prime sieve factor from sifting the fixed marks in the \(w\)-variable. Omitting primes dividing \(N\) costs no physical roughness because \(w\) is already a unit modulo \(N\); \(s>z\). To restore the two excluded primes \(p,t<z\) in the \(w\)-roughness take away \(p\mid w\) or \(t\mid w\), which would force \(p^2\mid q\) or \(t^2\mid q\). For each \(s\sim S\), the set of such \(q\asymp x/S\) has count
\[
       O\left(\frac xS\sum_{j\ge x^{.036}}\frac1{j^2}\right)
                        \ll \frac{x^{.964}}{S}.
\]
Even with all possible prime-divisor label choices and actual coefficient magnitudes these contributions are \(x^{.964+o(1)}\) after summing \(s\), by the elementary divisor bound. This restores the true (1) in either lower or upper sieve. No extra parity condition on \(w\) is being imposed.

The Rosser--Iwaniec linear sieve and (6) yield the uniform aggregate constants
\[
\begin{array}{c|c|c}
    \text{level}& \text{lower multiplier on } X_b\mathfrak S(Nb)/L
                         &\text{upper multiplier}\\ \hline
 x^{.217}& 2\log(146/71)/.217-o(1)&\text{not needed}\\
 x^{.213}& 2\log 2/.213-o(1)&2/.213+o(1).
\end{array}
\tag{7}
\]
In the first line the sieve parameter is \(.217/.071=217/71\in(3,4)\), and in the second it is exactly 3, so the ordinary finite formulas for \(f,F\) from the previous note apply. Errors are summed absolute by the level \(.217\) result just proved. For example one can also multiply the nonnegative main by any bounded smooth function of the fixed labels \(s,p,t\); since the total error was absolute this incurs no new remainder.

## 3. Density normalizations and the rank-two sector

For actual squarefree semiprime \(m=u v\), \(u<v\), both factors \(\ge x^{.120}\), the weight \(2\log u/L\) has total over \(m\in N-I\) equal to
\[
       (D_2+o(1))\frac{x}{2L},\qquad
 D_2=2\int_{.12}^{.5}\frac{dt}{1-t}
                  =2\log(44/25)>1.12.
\tag{8}
\]
This is the same PNT product computation as for rank four in the previous note: order the two factors, sum the larger by uniform PNT on each fixed box, and use the prime harmonic density \(dt/t\) for the smaller. Fixed \(N,b\)-unit exclusions in this reference are uniformly power-small: each possible removed \(m\)-factor is \(\ge x^{.120}\) and divides \(N b\) of polynomial size. Thus (8) applies uniformly in each model (5). The actual ratio \(C^\dagger/L\) is then \(-2\log u/L\) with relative \(o(1)\) error by §1.

The actual prime label harmonic factors obey
\[
 \sum_s \frac1{s-1}\sim \log(7/5),\qquad
 \sum_{p<t}\frac1{(p-1)(t-1)}
                  \sim \tfrac12\log^2(23/12),
\tag{9}
\]
where all bands are exactly (1) and \(s\in(x^{.10},x^{.14})\), and factors of \(N\) are removed. The diagonal \(p=t\) has power-small harmonic mass. Since \(b\) consists of three distinct polynomially large primes outside \(N\), \(\mathfrak S(N b)=\mathfrak S(N)(1+O(x^{-.036}))\) uniformly. Also \(W_s(q)\ge.44\). Combining (3), (7) first line, (8) and (9), the coefficient of the negative contribution on \(M_N\) is bounded below in magnitude by
\[
   .336\cdot \tfrac12(.65)^2\cdot .44\cdot .83
                  \cdot1.12\cdot \frac{1400}{217}
          =\frac{22681659}{121093750}>.1873 .
\]
Here \(\log(7/5)>.336,\ \log(23/12)>.65,\ \log(146/71)>.70\) and \(2\log(44/25)>1.12\) follow from the positive \(\operatorname{arctanh}\) series, using \(u=(a-1)/(a+1)\) for \(\log a\). All errors are \(o(M_N)\), giving the stated \(-.180M_N\) for the rank-two subpatch.

## 4. Bound the positive complement inside the same marked q sector

Still require all \(m\)-factors \(\ge x^{.120}\); then the rank is at most 8 for large \(x\). Repeated primes cost power-small as above. Prime \(m\) contributes exactly zero, and each odd squarefree rank \(3,5,7\) has symmetric min test (4) identically zero, because complementary divisors have opposite \(\mu\) but the same minimum. The true coefficient is \(O_k(\log H)\) in those ranks. The same **upper** sieve constants in (7) and their actual compact prime-product densities bound their combined absolute sum by \(O(\mathfrak S(N)x\log H/L^2)=o(M_N)\).

For four distinct factors the min test is nonnegative where \(p_{\max}<\sqrt m\), with value \(2\min(2\log p_{\min},\log m-2\log p_{\max})\), as proved in [NegativeRankFourCompensation.md](NegativeRankFourCompensation.md). It is at most \(\log m\). If \(p_{\max}>\sqrt m\), the divisors below half are precisely the subsets of the three other primes and their combined \(\mu\log\) sum is zero; then (4) is zero. The equality \(p_{\max}=\sqrt m\) is impossible for a squarefree product. Thus for an **upper** density of the positive rank-four weight divided by \(L\), it suffices to count the four-prime products with all factor exponents in \([.12,.5]\), with coefficient \(1+o(1)\), plus \(O(\log H/L)\) on the entire rank. As in the prior notes the endpoint \(\sqrt{3x/2}\) gives the same asymptotic density as \(x^{.5}\). On the truncated simplex all factor products satisfy
\(\prod_i t_i\ge .5\cdot.26\cdot.12^2\), by minimizing the concave sum of logarithms at its vertices, whose exponent vectors are permutations of \((.5,.26,.12,.12)\). Its ordered volume is \([.52^3-4(.14)^3]/6\) by the same disjoint-corner computation as before. Dividing by \(24\), the upper density is
\[
                         U_4\le\frac{4051}{8424}.
\tag{10}
\]
For ranks \(k=6,8\), an absolute bound for (4) divided by \(L\) is \(2^{k-1}+o(1)\), since each of its \(2^k\) terms has min log at most \(\log m/2\). On the simplex \(t_i\ge .12\), the unordered volume is \((1-k\cdot.12)^{k-1}/(k!(k-1)!)\), and \(\prod t_i\ge .12^{k-1}(1-(k-1)\cdot .12)\) by the same vertex argument. Hence upper densities for the positive pieces in these ranks are bounded by
\[
                       U_6\le\frac{16807}{262440},
                 \qquad U_8\le\frac{1}{555532992}.
\tag{11}
\]
The sum of (10)--(11) is \(<.545\), an exact rational comparison. All density estimates in (10)--(11) concern the actual ordered-product PNT and use their explicit compact exponent sets; they are applied to nonnegative counts via upper sieve, not substituted for a pointwise asymptotic prime-pair count.

It is important to compare the positive and negative terms with the **same** \(s\)-weight. On the entire central band
\[
 W_s(q)=(1-\log_x s)(1-2\log_x s)^2+O(1/L)
\]
uniformly. This replacement costs \(o(M_N)\) here: use the true upper sieve (7) on each compact rank for the total actual \(q\)-marked count \(O(\mathfrak S(N)x/L^2)\), multiply by its bounded-rank coefficient \(O(L)\), and then the \(O(1/L)\) variation. The common \(s\)-weight is positive, \(\ge.44\), and can now be included in the fixed-label sums of both sieve bounds. Using both lower and upper parameters at level \(x^{.213}\), (3), (7), (8), and (10)--(11) give a certified net negative multiplier, before the common harmonic label factors, of magnitude at least
\[
 \frac{.83\cdot1.12\cdot2\log2-.92\cdot.545\cdot2}{.213}
 >\frac{.83\cdot1.12\cdot1.38-.92\cdot.545\cdot2}{.213}.
\]
The last uses \(\log2>.69\) by the positive series at \(u=1/3\). Multiplying that last rational number by \(.44\cdot.336\cdot(.65)^2/2\) gives \(>.041\). This pays every positive rank inside the actual macro-rough \(m\) sector (including all moving-neck errors and repeats accounted above) and proves the safe whole-sector bound \(-.040M_N\).

## 5. Scope and budget

As in the previous note, only the **whole** artificial \(\mathcal T_{\rm v}(C^\dagger)\) is equivalent to the original \(\mathcal T_{\rm p}(C)\) up to arbitrary log accuracy. The above sectors do not contain genuine prime \(q\)'s. The negative rank-two patch and the negative net macro-rough patch are not disjoint from one another, but both are disjoint from the old rank-four rough-\(q\) patch. Consequently one can either exhibit signed subpatches totaling \(\le-.192M_N\), or account for the much larger whole sector (and its positive ranks) plus the old patch, yielding \(\le-.052M_N\). These statements leave different complements. Neither bounds the rest of the exact signed row, and no binary Goldbach conclusion follows.

[Chan’s November preprint](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) also uses two least-factor marks, for a different Chen sieve coefficient and different retained quotient. The exact two toggles here apply to the original reverse Vaughan cutoff, giving the positive (q)-coefficient before evaluating the entire rough reflected sector. [The separate marked Pan calculation](PanMarkedCompensation.md) uses two factors but a different divisor sum and cutoff; its contribution cannot be added to this row’s budget.
