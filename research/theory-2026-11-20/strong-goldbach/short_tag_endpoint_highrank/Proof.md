# The short-tag prime-column proxy has a positive high-rank component

This is a **nonzero** endpoint companion to [the centered short-tag result](../short_tag_full_triprime/Proof.md). Use exactly that note's \(N=2x\), \(Y,L,\ell,z\), squarefree shared \(k\), physical two-slope box, actual prime mark \(\beta_{\rm sh}\), \(A=kp\), \(R=x^{.5003}\), \(T\), and \(K_R\). References to the original equations (2)–(3) and three-box arguments refer to that centered note. The present result is not a bound for the centered covariance or a claim of binary Goldbach. Write \(T^\sharp(s)=\max(T(s),R)\). In (2) use this larger threshold and denote the score by \(F^\sharp\). In (3) separately use \(T^\sharp\), replace the two lower output bounds \(x^{.080}\) by \(x^\eta\), and replace the cap on \(c\) by \(x^\kappa\), where
\[
 \eta=10^{-4}\ell^{-1/4},\qquad \kappa=10^{-10}\ell^{-3/4}.
\]
Denote this score by \(G^\sharp\), and put \(H^\sharp=K_R-F^\sharp-G^\sharp\). The exact two-medium coefficient is unchanged: \(2\kappa<\eta\), and both free slots exceed \(x^{\eta-\kappa}>x^\kappa\), so the two selected free indices remain unique. The full thresholds are on the two output slots \(a,bc\), not on the separated \(b,c\). We prove uniformly for sufficiently large even \(N\) that, with the literal original unit marks and squarefree \(k\),
\[
 \sum_{d,e,k} \beta_{\rm sh}(d)\beta_{\rm sh}(e)
   a_{\rm p}(N-dk)H^\sharp(N-ek)
   1_{\{N-ek\ {\rm squarefree},\ \omega(N-ek)\ge 5\}}
   \gg x^{3/2}\frac{\varphi(N)}N .                              \tag{1}
\]
Each contributing right-leg integer has every prime factor at most \(x^{.505}\). The sum on this real support is signed; positivity does not follow from replacing it by an upper sieve or an absolute value.

## 1. The signed two-medium transfer with shrinking lower output bound

The proof of §4 of the centered note still applies to \(G^\sharp\), with the following explicit reserves. Each opened rough divisor is at most \(z^{J}=x^{O_B(1/\ell)}\). In the three-free branch the post-division lengths are \(\ge x^{\eta/2}\) for sufficiently large \(x\) depending on the desired fixed log reserve: \(a\ge x^\eta\), \(b\ge x^{\eta-\kappa}\) and \(s>x^{.01}\). Their total scale is \(X\ge x^{1-\kappa-O_B(1/\ell)}\), so the original strict modulus rails \(.501,.504\) hold. One does not need \(|h_i|<A\) for the CRT completion in §3: if any individual frequency is a nonzero multiple of \(A\), the all-prime zero-mask for that coordinate has no active modulus and cancels identically; all other integers are treated by the same exact residue masks. With \(|h_i|\ll X^\xi A/X_i\), the dual-length product and the bound on the product of the two longer lengths are exactly the same as in §3, without requiring a fixed positive lower exponent on \(X_i\). The bound on the shortest dual slot and the actual smooth Mellin-weight derivative bounds likewise use only those upper lengths and \(h_iX_i/A\ll X^\xi\). Thus the entire three-box power estimate, with fixed small \(\xi\), applies unchanged. In the one-long-free case use direct Poisson as before.

For volume/neck costs and unit counts now pay the true divisor and Bonferroni factors by \(x^{O_B(1/\ell)}\): the elementary divisor estimate \(\tau(n)^D\le \exp(O_D(L/\ell))\) holds uniformly, as do the numbers of divisor aliases. The power of \(A^\varepsilon\) in the *full-period* part of the elementary rectangle bound can be replaced by \(\tau(A)^C\) times log powers by its proof (split into full periods and two residual intervals; count the mixed pieces by ordinary Möbius floors). Its sum and every interior smoothing floor therefore still gain \(x^{-\eta/3}\) by the minimum physical free length. The \(A^{1/2+\varepsilon}\) part retains a fixed power reserve, since the true short-\(s\) labels contribute \(x^{.01+\kappa}\). The factorial-moment errors for signed roughness are unchanged, because the literal upper envelope is still a fixed divisor power on \(y,N-y\). These bounds apply equally to the real exact moving cutoff \(T^\sharp(s)\), whose log slopes are bounded. After \(v=bc\), the exact archimedean cut again has no \(c\) in it.

Finally the common masked harmonic \(\mu_3(c)/c\) prefix at \(C=x^\kappa\) is still arbitrary-log small: in the same Perron rectangle the decay at an endpoint \(\ge C^{1/3}\) is \(\exp(-c_0\kappa \ell^2/3)\), which beats every fixed inverse log because \(\kappa\ell^2\gg\ell\). The standard half-integer and truncation errors are also arbitrary-log on this endpoint. Use the three-variable Dirichlet hyperbola or the cubed harmonic Dirichlet series with the exact \(AN\) mask. It follows that the complete signed \(G^\sharp\) estimate against the fixed divisor envelopes holds with every log reserve.

## 2. Endpoint mean and exact prime-column transfer

The change from \(F\) to \(F^\sharp\) is an instance of [the separately evaluated upper-endpoint mechanism](../full_endpoint_composite_proxy/Proof.md), with the **same raw** \(R=x^{.5003}\) as in (1). We record its exact endpoint and sign to prevent mixing different normalizations. The difference \(D=F-F^\sharp\), which is *added* to the residual, is
\[
 D(y)=-R_z(y)
    \sum_{\substack{sca=y,\ s>x^{.4177},\ ca>R\\
                    x^{.918}/s<a\le R}}\mu_2(c)\log s.             \tag{4}
\]
Indeed the cap \(x^{.505}>R\) does not contribute to this change; \(T_0(s)<R\) precisely when \(s>x^{.4177}\), where the exact old branch is \(x^{.918}/s\). Thus there is no added term with \(a\) in \((x^{.5003},x^{.505}]\). Fix \(c\) and use the same two-free rectangle completion as in §2, with \(x^{.4177}<s<y/R\), \(c<y/x^{.918}\), \(a>R/c\gg x^{.4183}\). The error has ample power reserve uniformly for \(A\le x^{.503+o(1)}\); the independent rough-label expansions, unit mask on \(c,AN\), and true radial \(I_k\) window are as above. Dropping the full \(N\) masks on the free rough factors initially costs only \(O(xL/z+L)\) true \(y\)'s before the fixed moments. Its literal mean is
\[
 -\frac{\varphi(A)W_z(A)^2}{A^2}\int_{I_k}
 \int_{x^{.4177}<s<y/R}\frac{\log s}{s}
 \sum_{\substack{y/(sR)\le c<y/x^{.918}\\(c,AN)=1}}
          \frac{\mu_2(c)R_z(c)}c\,ds\,dy .                       \tag{5}
\]
Put \(u=\log(y/(sR))\), \(Z_y=\log(y/x^{.918})\). The inner archimedean integral at each \(c<e^{Z_y}\) equals
\((\log(y/R))\log c-\tfrac12(\log c)^2\). If
\(B_{AN}(w)=\prod_{p\le z\ {\rm or}\ p\mid AN}(1-p^{-1-w})^{-1}\),
the signed harmonic series is \(\zeta(1+w)^{-2}B_{AN}(w)^2\), with zero of order two and leading coefficient \(B_{AN}(0)^2\). The same moving-rough Perron estimate (with Cauchy differentiation twice) at \(e^{Z_y}\asymp x^{.082}\) therefore gives mean \(+|I_k|/\varphi(A)\) up to arbitrary-log error, since
\[
   W_z(A)^2 B_{AN}(0)^2=(A/\varphi(A))^2(1+O(L/z)).
\]
This identity keeps the actual extra primes of \(N\) above \(z\). Independently, \(b_z\) has that same mean on the physical class, by one-variable rough Bonferroni counting and \(W_z(A)/V_z=(A/\varphi(A))(1+O(L/z))\); its nonunit-on-\(N\) rough values can be dropped at the same cost. After summing actual labels all errors have the earlier arbitrary-log bound, including against the actual opposite row. Combining the \(F_R-b_z\), \(F\), \(G^\sharp\), and \(D-b_z\) transfers shows **\(H^\sharp\) matches \(a_{\rm p}\)** in this sense. Its centered covariance uses \(H^\sharp-b_z\); replacing it by an uncentered quadratic form without the \(b_z\)'s would be incorrect.

## 3. The remaining lower ranks and their small upper cost

This lift preserves the giant-prime deletion, because \(T^\sharp\le x^{.505}\), and preserves the exact prime/semiprime zero. It need not preserve the exact triprime zero or rank-four nonpositivity: these two debts can instead be made *arbitrarily small* on the literal scale, as follows.

For a triprime, the only possibly positive nondeleted term is the \(r=pP>R\) pair with the smaller true prime \(p<x^\eta\) and \(P\le T^\sharp(s)\). Because \(Ps=y/p>x^{.918}\) when \(\eta<.08\), this necessarily has \(P>T(s)\) and \(P\le R\). Thus the true remaining possibilities all satisfy \(P\in(R/p,R]\), with the singleton \(s\) genuinely prime, and weight at most \(2\log s\). For rank four, the sign calculation of §2 still gives \(-2n_2+4n_1\) for the rank-three \(r\) before \(G^\sharp\). If \(n_1\ge1\) there is no valid correcting partition. If \(n_1=0,n_2\ge1\), the at most two tiny-\(c\) charges are already paid as before (two tiny primes cannot fill both slots when \(2\kappa<\eta\)). Any strictly positive remainder of a rank-three \(r=pqt\) therefore has one tiny true \(p\le x^\kappa\), \(n_2=0\), \(s\) a genuine singleton prime, and \(qt\in(R/p,R]\): \(qt>T(s)\) from \(sqt=y/p>x^{.918}\), and \(qt\le T^\sharp(s)\) from \(n_2=0\). A valid correcting partition implies \(q,t\ge x^{\eta-\kappa}\). It costs at most \(2\log s\). There are also \(r\) of rank two within rank-four \(y\); their same tiny-pair correction as for triprimes has \(s\) a **product of two actual primes**, not necessarily rough at a fixed polynomial cutoff. If these terms are positive, \(P\in(R/p,R]\) again and \(s\) is within a relative \(p\)-factor of \(x^{.4997}\). This last debt requires a separate estimate below; it cannot be thrown into the prime-\(s\) case.

For clarity let us give the needed upper estimates on the true determinant. For a fixed positive integer \(h\), equal below to \(p\) or to a product \(pq\) of two revealed true primes, require
\[
 v\in(R/p,R],\quad sv\in I_k/h,\quad
 sv\equiv N\bar h\pmod A,\qquad P^-(s),P^-(v)>x^\nu ,
\]
where \(0<\nu\le \nu_0\), with \(\nu_0\le .001\) an absolute sufficiently small constant for the dimension-one fundamental lemma. For \((h,A)>1\) the actual progression is empty. At a reduced class the unweighted upper reference is
\[
 C\,\nu^{-2}\frac{x\log p}{h\varphi(A)L^2},                     \tag{6}
\]
with power-saving aggregate errors after summation. Here \(C\) is absolute, uniformly even for the small moving \(\nu=\min(\nu_0,\eta/2)\).

To prove this, use independent dimension-one upper sieve divisors for \(s,v\) at level \(x^{.01}\) and sifting threshold \(x^\nu\). The upper majorizing polynomial is nonnegative on each integer, including nonsifted ones, so the product is an upper majorant. Omit the primes dividing \(A\) from each sieve: on the true unit class they never occur. The dimension-one product bound is uniform on omitting these primes. The upper fundamental lemma [Friedlander–Iwaniec, *Opera de Cribro*, Lemma 6.11, cited in the primary application §2.1](https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/article/superscars-for-arithmetic-point-scatters-ii/3CCB969E058792C1803466AE0EF29136) gives, for the ratio \(.01/\nu\) above its fixed dimension-one threshold, scalar at most \(C\,(A/\varphi(A))/(\nu L)\), uniformly for both slots. Use the elementary rectangle count after imposing both sieve divisors, with exact reduced residue \(N\overline{h d_1d_2}\bmod A\). Its correct scalar is \(\varphi(A)/A^2\), so the product of the two scalar sieves gives the \(1/\varphi(A)\) in (6). The true volume is at most \((x/h)\log p\) times an absolute constant by integrating the window \(sv\in I_k/h\) at fixed \(v\). A relative log-fine rectangle outer cover of the radial boundary only adds an arbitrarily small inverse-log proportion of this volume, since \(p\ge2\); all terms from the majorant remain nonnegative. The rectangle's \(A^{1/2+o(1)}\) cost, summed over all actual marked moduli, the two divisor lists, \(p\le x^\eta\), and the optional \(q\le x^{.002}\), is
\(\ll x^{.7545+.02+.002+\eta+o(1)}\), before the opposite \(d\)-length. The full-period error has exponent at most \(.501+.02+.002+2\eta+o(1)\) since the lengths are \(\ll x^{.501+\eta}\). These bounds allow the true fixed divisor weights and all box and mark multiplicities. The positive scalar comparison uses precisely the actual unit-modulus normalization.

For triprimes both \(s,v=P\) are genuine large primes. Use \(\nu=\nu_0\) and weight \(O(L)\). The true \(p\)-sum uses \(\sum_{p\le x^\eta}\log p/p\ll1+\eta L\), giving \(O((\eta+L^{-1})x/\varphi(A))\) before the negligible errors.

For rank four with \(r=pqt\), take \(v=qt\), \(\nu=\min(\nu_0,\eta/2)\), and \(s\) the actual singleton prime. The bound \(q,t\ge x^{\eta-\kappa}\) from the actual positive profile guarantees this roughness. A genuine rank-two \(v\) has exactly one unordered prime factorization, so no additional log factor is introduced in the main. Here the \(p\)-sum ends at \(x^\kappa\); the cost is \(O((\kappa+L^{-1})\eta^{-2} x/\varphi(A))\).

For rank four with \(r=pP\) and \(s\) semiprime, first keep those \(s\) with both factors \(>x^{.002}\): (6) with fixed \(\nu=\nu_0\) and \(h=p\) controls them with the same cost as triprimes. Otherwise reveal the least actual prime \(q\mid s\). It satisfies \(z<q\le x^{.002}\) by the physical rough mask, and the other factor \(s'=s/q\) is a genuine prime \(>x^{.49}\) for sufficiently large \(x\): \(s=y/(pP)\gg x^{.4997-\eta}\). Apply (6) with \(s'\) in place of \(s\), \(h=pq\), and \(\nu=\nu_0\). Any \(q\) sharing \(A\) gives no physical term, and uniqueness of the least actual label prevents a divisor loss. The extra reciprocal prime cost is
\[
 \sum_{z<q\le x^{.002}}\frac1q=O(1+\log\ell)
\]
by Mertens, using the true \(z=\exp(L/\ell^2)\). Thus the total signed upper for this possibility is \(O((\eta+L^{-1})(1+\log\ell)x/\varphi(A))\). These three upper estimates enumerate the actual positive possibilities, not hypothetical independent prime densities. With the chosen parameters their sum is \(o(x/\varphi(A))\), since \(\eta(1+\log\ell)\to0\) and \(\kappa\eta^{-2}\to0\).

## 4. Strict same-target lower with the actual opposite primes

Put \(\Gamma_a(k)=\sum_e\beta_{\rm sh}(e)a_{\rm p}(N-ek)\) on the exact unit slopes and let
\[
 M(k)=|I_k|\sum_{\substack{p\text{ in its mark band}\(p,N)=1}}
               \frac1{\varphi(kp)}.
\]
Sharing labels \(p\mid k\) may be kept or discarded at the earlier power cost. Since \(|I_k|\asymp x\), the cumulative upper just proved for lower ranks, weighted by the actual opposite prime column \(\Gamma_a(k)\), is \(o(\sum_k\Gamma_a(k)M(k))+O_B(x^{3/2}L^{-B})\). No main equality between \(\Gamma_a(k)\) and \(M(k)\) is assumed. The unit box positivity of the centered result gives \(\sum_k\Gamma_a(k)\gg x\varphi(N)/N\); by elementary unit counting there are \(O(Y\varphi(N)/N)\) available \(k\)'s. Hence
\[
   \sum_k\Gamma_a(k)^2\gg x^{3/2}\varphi(N)/N.
\]
On the other hand \(M(k)\ll Y,k/\varphi(k)\), by harmonic summation of the actual prime marks and \(\varphi(kp)\ge(p-1)\varphi(k)\). The elementary Euler product moment
\(\sum_{k\asymp Y,(k,N)=1}(k/\varphi(k))^2\ll Y\varphi(N)/N\)
follows by expansion with nonnegative coefficients \(g(p)=O(1/p)\), bounded \(\tau(N)\) floor costs, and convergence of \(\prod_p(1+g(p)/p)\); it is also the uncut upper in [the balanced prime-column proof, §3](https://github.com/mxym/math/commit/bafa9b8f). Restricting it to squarefree \(k\) only decreases it. Thus Cauchy gives
\(\sum_k\Gamma_a(k)M(k)=O(\sum_k\Gamma_a(k)^2)\), and the entire lower-rank debit is \(o(\sum_k\Gamma_a(k)^2)\).

The exact prime-column match proved in §2 and the genuine opposite prime coefficient give the all-ranks signed test \(\sum_k\Gamma_a(k)^2+O_B(x^{3/2}L^{-B})\). Its squareful rough terms may be removed: at most \(O(x/z+\sqrt{x})\) different \(y\) have a repeated prime above \(z\), and the actual \((e,k)\) multiplicities are divisor powers of \(N-y\); Hölder with the fixed divisor moments of these two variables and \(\Gamma_a(k)\ll YL\) makes their contribution arbitrary-log small. The diagonal \(d=e\) in the prime-proxy test itself is zero, since \(H^\sharp=0\) on primes. In the squared genuine prime column its absolute cost is only \(O(xL^2)\) by bounded mark multiplicity, also negligible. Thus subtracting the actual lower-rank debit proves (1).

This is a strong positive **composite** mass in a real fixed-target same-index correlation. The actual two entries are \(N-dk\) and \(N-ek\), not a Goldbach pair for \(N\). A bound for their centered covariance and positivity of the binary Goldbach count remain open. In particular the theorem does not assert exact nonpositivity on all uncentered rank-four inputs; that statement fails for some valid angular profiles, whose positive parts are priced above.

The companion checker replays the exact positive debt classifier in the three possible physical cases and the numeric rail inequalities; it does not test any analytic estimate.
