# Fixed-power roughness transfer for the paired same-cofactor cell

The actual centered same-cofactor cell can be projected onto reflected integers with a **fixed polynomial least-prime threshold**, at a cost arbitrarily small relative to its literal \(M_N\) allowance. In particular the remaining reflected ranks are bounded independently of the target. This is not the replacement of a genuine prime condition by an uncalibrated rough model: the same prime term and the same existing rough reference are matched. Both opposite-sign physical families remain; no bound on their joint sign is asserted.

## 1. Statement

Use the original notation of [SameCofactorVaughanCenter](SameCofactorVaughanCenter.md) and [SameCofactorPhysicalMacroCore](SameCofactorPhysicalMacroCore.md), including the two genuine quotient ranks in \(C_s(u)\), \(m=N-su\), \(L=\log x\), \(N=2x\), and \(G_N=\sum(a-b)(su)C_s(u)\). The reference \(b\) in this definition is always the original \(Z=\exp(L^{1/4})\) reference. Fix a sufficiently small \(\eta>0\), and put
\[
 z=x^\eta,\qquad \Delta=\eta^{2/3},\qquad
 U=x^{1/4-\Delta},\qquad R_z(t)=1_{P^-t\ge z}.
\]
Take \(x\to\infty\) with \(\eta\) fixed; only afterwards may \(\eta\downarrow0\). Then
\[
 G_N=\sum_{s,u} C_s(u)1_{(su,N)=1}R_z(m)T(m;U)
   +O_\delta\!\left(M_N\{\eta^{-2}H^{-H/2}+
                         \eta^{-1}e^{-c/\eta}\}\right)
   +o_{\eta,\delta}(M_N),\qquad H=\eta^{-1/3},                        \tag{1}
\]
with an absolute \(c>0\) and uniform target errors. The exact open coefficient \(T\) has the all-powers identity (1) of SameCofactorPhysicalMacroCore. In (1) squareful reflected rows are power-small for fixed \(\eta\). With its physical notation \(m=Mv,\ j=\omega(M)\), one can further retain only \(v=1,j\in\{2,3\}\) and \(v>U,j\in\{1,2\}\) at extra cost \(O_\delta(\eta^{2/3}M_N)+o_{\eta,\delta}(M_N)\). Every retained \(m\) has at most \(\lceil1/\eta\rceil\) true prime factors eventually. This reduces the same paired problem to fixed ranks without relying on separate bounds that contradict [the dyadic means](SameCofactorOppositeDyadicMeans.md).

## 2. Uniform harmonic estimates at the fixed rough threshold

Let \(A=Nsu\), even and polynomial in \(x\), and define
\[
 F_A(y)=\sum_{\substack{d\le y\\(d,A)=1}}\frac{\mu(d)}{\phi(d)},\qquad
 B_A(y)=\sum_{\substack{d\le y\\(d,A)=1}}\frac{\mu(d)}{\phi(d)}\log(y/d).
\]
We need actual control at \(y\) near 1, not merely the usual polynomial-endpoint asymptotic. By the uniform Goldston--Yıldırım finite estimates in [Huang--Li, Lemma 1](https://arxiv.org/pdf/2005.03811), when \(\log A\ll\log y\) and \(y\) is polynomially long, \(F_A(y)=O_D(L^{-D})\), \(B_A(y)=\mathfrak S(A)+O_D(L^{-D})\). At the *fixed* mask \(A=2\), the same estimates with \(\log(2y)\) show that the dyadic suprema of \(|F_2|\) are summable, and \(B_2\) is bounded, including \(y\ge1\). Convolve the full \(A=2\) series with the nonnegative inverse on primes \(p>2,\ p\mid A\), having weights \((p-1)^{-j}\) on \(p^j\). Its total mass is exactly \(\mathfrak S(A)/\mathfrak S(2)\). The partial unweighted and log-weighted sums are the corresponding convolutions \(F_2(y/b)\), \(B_2(y/b)\), extended by zero below 1. A rescaled dyadic partition overlaps the usual partition at most twice. Hence
\[
 \sum_{j\ge0}\sup_{2^j\le y\le2^{j+1}}|F_A(y)|\ll\mathfrak S(A),
 \qquad \sup_{y\ge1}|B_A(y)|\ll\mathfrak S(A),                           \tag{2}
\]
with absolute constants even when \(N\) has many small prime factors.

To restrict \(d\) to \(R_z\), convolve the \(A\)-masked coefficients with the nonnegative completely multiplicative weight \(h=h_{A,z}\), supported on primes \(p<z,\ p\nmid A\), with \(h(p^j)=(p-1)^{-j}\). Call its full mass \(\mathcal H\). The source factors all exceed \(z\), so
\[
 \mathcal H=\prod_{\substack{p<z\\p\nmid A}}(1-1/(p-1))^{-1}=V_N(z)^{-1}.
\]
The following **local** tail is crucial; a total Rankin tail multiplied by the unweighted incomplete Möbius sum is not sufficient:
\[
 \begin{split}
 \sum_{b>\sqrt U}h(b)&\ll\mathcal H e^{-c/\eta},\\
 \sum_{Y\le b\le 2Y}h(b)&\ll
       \frac{\mathcal H}{\log z}e^{-c/\eta}+x^{-c'}
                       \qquad(Y\ge \sqrt U/2),                       \tag{3}
 \end{split}
\]
for absolute positive \(c,c'\), for all sufficiently large \(x\) with \(\eta\) fixed.

Here is a direct proof uniform in the mask. For all \(e^4\le y\le z\) and \(\alpha=1/\log y\),
\[
 \sum_{P^+b\le y} h(b)b^\alpha
   \ll \sum_{P^+b\le y}h(b)\le \mathcal H.
\]
Indeed \(p^\alpha/(p-1)\le3^{1/4}/2<1\) for admitted \(p\ge3\), and the extra Euler log is \(O(\sum_{p\le y}(p^\alpha-1)/p)=O(1)\) by \(\sum_{p\le y}\log p/p\ll\log y\). Taking \(y=z\) and applying Rankin gives the first line of (3), since \(\log U\gg L\). For the local assertion, split the largest prime of \(b\) into bands \((y^{1/2},y]\) with \(y=z^{2^{-j}}\ge e^4\). Open one such prime \(p\), write \(b=pc\), and retain \(P^+c\le y,\ c\ge Y/y\). The factorization \(h(pc)=h(p)h(c)\) is exact even when \(p\mid c\). For fixed \(c\), the \(p\)-harmonic sum on \([Y/c,2Y/c]\) restricted to this band is \(O(1/\log y)\), by the ordinary prime upper bound on a factor-two interval and \(p>y^{1/2}\). The sum over \(c\) is \(\ll\mathcal H (Y/y)^{-1/\log y}\) by the preceding Rankin estimate. Summing the bands costs
\[
 \ll\frac{\mathcal H}{\log z}
             \sum_{j\ge0}2^j\exp(-c_0\,2^j/\eta)
 \ll\frac{\mathcal H}{\log z}e^{-c/\eta},
\]
since \(\log Y\gg L\). Once the band endpoints are bounded, the remaining primes are in a fixed finite set; \(\sum h(b)b^{c_1}<\infty\) on this set uniformly in the mask for an absolute small \(c_1>0\), giving \(x^{-c'}\). This proves (3) without a theorem for masked smooth integers. The factor \(\mathcal H/\log z\) in the local bound, which reflects **the actual** mask, prevents an extra unbounded singular factor.

Write \(F_A^{(z)},B_A^{(z)}\) for the same sums with \(R_z(d)\) inserted. Decompose the convolution at \(b=\sqrt U\). The part below it sees polynomial \(U/b\) and hence the usual finite asymptotics. In the remaining part up to \(U\), use (3) on dyads in \(b\) and (2) on the corresponding \(U/b\) dyads. For \(B_A^{(z)}\) use the total tail (3), including \(b>U\) in the full mass term. This proves
\[
 \begin{split}
 F_A^{(z)}(U)&=O\!\left(\frac{\mathfrak S(A)\mathcal H}{\log z}
                                         e^{-c/\eta}\right)+O_{D,\eta}(L^{-D}),\\
 B_A^{(z)}(U)&=\mathfrak S(A)\mathcal H
          +O\!\left(\mathfrak S(A)\mathcal H e^{-c/\eta}\right)
          +O_{D,\eta}(L^{-D}).                                       \tag{4}
 \end{split}
\]

## 3. Sieve transfer at the actual residue

Apply the Vaughan expansion to the actual \(\Lambda(m)R_z(m)\). On genuine primes it is unchanged; proper powers cost power-small, as in the preceding same-cofactor proof. The two short terms have \(q=d\le U\) or \(q=d\ell\le U^2\), with \(R_z(q)=1\). Use a *dimension-one fundamental lemma*, not a fixed-depth elementary Bonferroni polynomial. For clarity, [Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 19.1, author PDF p.205](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf#page=206) gives lower/upper coefficients \(|\lambda_e^\pm|\le1\) on squarefree \(e\) with primes \(<z\) and \(e\le z^H=x^\Delta\), bracketing the pointwise rough condition and with relative main error \(O(H^{-H/2})\). Here the local density in the coprime main is \(1/(p-1)\) for \(p<z\) not dividing \(N\); \(2\) is excluded by the even target. The dimension-one product condition follows from Mertens and the convergent \(1+O(1/p^2)\) per-prime correction to \(1-1/p\), and omitting the primes of \(N\) only decreases its inverse product. All these constants are uniform in \(N\).

As in SameCofactorPhysicalMacroCore §2, apply [Polymath Theorem 2.9](https://msp.org/ant/2014/8-9/ant-v8-n9-p03-p.pdf) at the full \(su\asymp x\) scale with actual prime-\(s\) SW slot, actual two signed \(u\) branches, real reduced residue \(N\), and \(qe\le U^2x^\Delta=x^{1/2-\Delta}\). The \(q,e\) splitting is unique by their disjoint prime supports, and the coefficient multiplicity for \(q=d\ell\) is at most \(\log q\). Retain the same \(s\)-relative mesh of sharp \(u\) prefix and factor endpoints and the same separately handled \(\log(m/d)\). The wall costs from the actual rows and coprime principal remain arbitrary-log-small, even after inserting the bounded sieve coefficients, by the strip and divisor-moment proof in that section. This removes no genuine prime labels and requires no fixed-\(s\) quotient BV at this level.

For each short branch first bound its rough bracket gap with the **absolute** source/short coefficients. The relative sieve error multiplies \(V_N(z)\) times the absolute harmonic sum. The latter is \(O(L/\eta)\): for the first term use \(\sum_{d\le U,R_z(d)=1}|\mu(d)|/\phi(d)\ll1/\eta\) by the squarefree Euler product on \(z\le p\le U\), and a log weight \(O(L)\); for the second sum use the same \(d\)-bound and \(\sum_{\ell\le U}\Lambda(\ell)/\phi(\ell)\ll L\). The possible overlap in \(d,\ell\) only decreases \(1/\phi(d\ell)\) from \(1/(\phi(d)\phi(\ell))\). As \(V_N(z)\ll\mathfrak S(N)/(\eta L)\) and the unsigned mass of \(C_s\) is \(O_\delta(x/L)\), the total cost is \(O_\delta(M_N\eta^{-2}H^{-H/2})\), besides the arbitrary-log BV error. Thus no sieve error is multiplied by an unnoticed power of \(L\).

The main harmonic in the first term is \(B_A^{(z)}(U)+\log(m/U)F_A^{(z)}(U)\), before summing over actual \((s,u)\). Its \(V_N(z)\) multiplier cancels \(\mathcal H\). Equation (4), including the unweighted local tail, gives main \(\mathfrak S(A)\) with error \(O(\eta^{-1}e^{-c/\eta}\mathfrak S(A))+O_{D,\eta}(L^{-D})\). In the second term write \(\ell=p^j\). The relative \(1-1/p\) adjustment when \(p\mid d\) in \(1/\phi(d\ell)\) is \(O(L^{O(1)}/z)\) in the absolute harmonic, by summing \(\log p/(p\phi(p^j))\) over \(p\ge z\). After removing this adjustment, use the product of \(F_A^{(z)}(U)\) and an \(O(L)\) prime-power harmonic, so its main is zero with the same error. Finally \(\mathfrak S(A)/\mathfrak S(N)=1+O(x^{-.10})\), since all actual factors of \(su\) are macro primes, and \(\mathfrak S(N)\sum C_s\) is the already proved literal subpower rough reference. Preserving the unit masks throughout proves (1).

## 4. Fixed-rank quarter removal

The all-powers identity applies also with \(R_z\), since it multiplies the whole grouped coefficient. Repeated prime bases cost \(O(x/z+x^{1/2})\) for the support, and fixed divisor moments plus the log weight make their weighted loss power-small. The exact squarefree cancellations remain. For four macros only \(v=1\) survives; the reciprocal harmonic of each of three fixed macro labels in the near-quarter band of width \(O(\Delta)\) is \(O(\Delta)+o_\eta(1)\). Use the true prime last slot and \(x^{.36}\)-rough \(u\) in the two-affine-form upper of the preceding macro-core note to obtain \(O_\delta(\Delta^3 M_N)+o_{\eta,\delta}(M_N)\).

For three macros and \(v>U\), open \(a\mid v\) with \(a<v/U\le 1.5x^{4\Delta}\) by complementary Möbius as before. It is now \(z\)-rough and its reciprocal harmonic is \(O(\Delta/\eta)\) by Mertens. At fixed \(s,P,a\), with \(P\) the three macro factors, the affine forms for \(b=v/a\) and \(u\) are exactly those in the preceding note. Their determinant remains \(N\) and the physical units force \((s,Pa)=1\), \((sPa,N)=1\); if a slope prime divides a form's leading coefficient, the constant is nonzero at it and the local adjustment is \(1+O(1/p)\) at primes \(\ge z\). Sieve \(b\) to \(z\) and \(u\) to a small fixed polynomial scale above \(z\); the mixed density is \(O(\mathfrak S(N)/(\eta L^2))\) with absolute constant. The number of fixed labels is at most \(x^{.89+13\Delta+o(1)}\); for sufficiently small fixed \(\eta\), the \(x^{.01+o(1)}\) dimension-two sieve floor per label still saves a fixed power. Multiplying the three \(O(\Delta)\) prime harmonics, the rough \(a\)-harmonic, and the log weight gives
\[
       O_\delta(M_N\Delta^4/\eta^2)+o_{\eta,\delta}(M_N)
                =O_\delta(M_N\eta^{2/3})+o_{\eta,\delta}(M_N).
\]
The pure four-macro bound is smaller. Thus after a small cost relative to the same ledger, each of the two remaining actual physical families has reflected rank bounded independently of \(N\). One still needs a fixed-target **paired signed** estimate, not termwise positivity or just a bound on the number of ranks.
