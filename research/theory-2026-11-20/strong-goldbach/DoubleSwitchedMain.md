# Two whole switches with the actual positive intersection main

Take the unrestricted central row (1) of [SwitchedLongFreeReverseColumns.md](SwitchedLongFreeReverseColumns.md) for a fixed \(S=x^\alpha\), \(.10\le\alpha\le.14\); in particular do not introduce any coupled \(d\ell\) or \(srk\) mask beyond the original cuts. Retain \(U=.454,V=.004,Q=.466,U_q=.070,V_q=.010,E=.080\) as **exponents** of the corresponding \(x\)-power cutoffs. In the formulas below the symbols themselves denote the resulting integer thresholds, not the exponents. Set
\[
 C_q^{\rm hi}(q)=\sum_{\substack{rk\mid q\\r>U_q,\ k>V_q,\ rk>E}}\mu(r)\Lambda(k),
 \qquad
 \mathcal B(F,G)=
  \sum_{\substack{s\sim S\ {\rm prime},\ sq\in I\\(sq,N)=1}}
      \frac{\kappa_s W_s(q)}{\log q}F(N-sq)G(q).
\]
The original double high sum is \(T=\mathcal B(C_m^{\rm hi},C_q^{\rm hi})\). Fix \(0<\delta<.005\), let \(B_m=x^{(1+\alpha)/2+\delta}, B_q=x^{1/2+\delta}\). Define the explicit long-divisor components at the actual arguments \(m,q\) by
\[
\begin{split}
 L_m(m)&=-\!\!\sum_{\substack{a\mid m\\a<m/B_m}}\big(\mu*\Lambda_{>V}\big)(a),\\
 L_q(q)&=\sum_{\substack{e\mid q\\e<q/B_q}}c_q(e;q),\\
 c_q(e;q)&=-\big(\mu *\Lambda_{>V_q}\big)(e)
            +\mu_{>U_q}(e)\log(q/e)-\big(\mu_{>U_q}*\Lambda\big)(e).
\end{split}
\tag{1}
\]
For every \(D>0\) these satisfy, at each \(N\), uniformly in the label dyad,
\[
\begin{split}
 \mathcal B(L_m,C_q^{\rm hi})&=O_{D,\delta}(xL^{-D}),\\
 \mathcal B(C_m^{\rm hi},L_q)&=O_{D,\delta}(xL^{-D}),\\
 \mathcal B(L_m,L_q)&=\mathcal M+O_{D,\delta}(xL^{-D}),\\
 T&=\mathcal B(C_m^{\rm hi}-L_m,C_q^{\rm hi}-L_q)-\mathcal M
                         +O_{D,\delta}(xL^{-D}),
\end{split}
\tag{2}
\]
where the exact original semiprime reference main, up to the displayed error, is
\[
 \mathcal M=\sum_{\substack{s\sim S\ {\rm prime}\\(s,N)=1}}
       \kappa_s\mathfrak S(Ns)
          \int_{I/s}\frac{W_s(u)}{\log u}\,du .
\tag{3}
\]
Here \(\mathfrak S\) is the usual Goldbach singular series and \(I=(x/2,x]\). In particular the two whole switches do **not** have negligible intersection, even though each against the entire opposite high coefficient is negligible. There is no estimate for the first term in the last line of (2).

## 1. Exact free components and the two whole estimates

Use the formal identities and literal long marked coefficients \(P_B,H_B\) of [SwitchedLongFreeReverseColumns.md](SwitchedLongFreeReverseColumns.md). In the forward term a long free slot of size \(b>B_m\) can occur in the expansion of \(\mu(d)\), not in that of \(\Lambda(\ell)\): if \(d>U\), \(\ell>B_m\), then \(d\ell>x^{.454+.55+\delta}>3x/2\) for large \(x\). On writing \(d=t b\), this automatically satisfies \(d>U,d\ell>Q\); \(\ell>V\) remains. The marked weight is \(-\mu_2(t)\Lambda(\ell)\). Combine \(t h\) by \(\mu_2*\mathbf1=\mu\), giving exactly \(L_m(m)\) in (1), with \(a=t\ell h\).

On the quotient side write \(q=r k j\), and use the two allowed marked pieces, which are disjoint at \(q\). A long free slot in \(r=t b\) automatically satisfies \(r>U_q,rk>E\); combine \(t j\) by the same \(\mu_2*\mathbf1=\mu\), retaining \(k>V_q\). This yields the first term of \(c_q(e;q)\) with \(e=t k j\). For a long free slot in \(k=t b\), \(k>V_q,rk>E\) hold automatically, and \(r>U_q\) stays. Combine \(t j=c\) using \(\mu*\mathbf1=\delta_1\) and \((\mu*\Lambda)*\mathbf1=\Lambda\). This gives the contribution \(\mu(r)1_{r>U_q}\{1_{c=1}\log b-\Lambda(c)\}\), and hence the other terms of \(c_q\) with \(e=r c\), \(b=q/e\). All of these combinations use unrestricted actual \(h,j\). They are not justified on the previously discarded product masks or individual \(d,r\) dyads.

The second estimate of (2) is the prior full switched-modulus theorem. For the first, unfold the just-described forward long-free term before combining its labels: \(m=a b\), \(a=t\ell h\), \(b>B_m\). For each fixed \(s\) and \(a\), the true equation is
\[
          s q+a b=N,\qquad a\ll (x/S)^{1/2}x^{-\delta}.
\]
The unit condition forces \((a,Ns)=1\), in particular if \(s\mid a\) the physical class is empty since \(s\nmid N\). Conversely it is the true reduced progression \(q\equiv N\bar s\bmod a\) with the further mask \((q,N)=1\). Every restriction on the free \(b\) becomes an interval for \(q\); \(|\mu_2(t)\Lambda(\ell)|\) and the number of representations \(a=t\ell h\) cost divisor weights and powers of \(L\). The test \(\kappa_s W_s(q)/\log q\) has log-power variation on the central \(q\)-range.

Now reassemble the *entire* \(C_q^{\rm hi}\) just as the reflected coefficient was reassembled in the reverse switch. Its three short terms have divisor at most \(x^{.080}\), including the true \(rk\le E\) subtraction. The CRT with the \((q,N)=1\) mask has density \(\phi(N)/(Na e)\) for each short divisor \(e\) coprime to \(Na\); retain \(\log(q/e)=\log q-\log e\) in the first term. Uniform coprime Mertens evaluates the short mean exactly to \(-1/\phi(a)\) plus arbitrary log error, as in (7)--(8) of [SwitchedLongFreeReverseColumns.md](SwitchedLongFreeReverseColumns.md). The cut \(r>U_q=x^{.070}\) has polynomial margin, and the first short convolution starts at \(r=1\) with its Euler derivative. Thus ordinary weighted maximal BV for \(\Lambda(q)\) at its *own* scale \(x/S\) bounds every \(s\) row by \(O_D((x/S)L^{-D})\), including all allowed \(a\) with \(a\ll(x/S)^{1/2}x^{-\delta}\); the target residue may depend on \(s\). The aggregate floor error is at most
\[
 x^{.080+\alpha+(1-\alpha)/2-\delta+o(1)}\le x^{.650-\delta+o(1)}.
\]
Prime-power values with \((q,N)>1\) have \(O(L^2)\) possible \(q\)'s across all \(s\), and \(a\mid N-sq\) has divisor multiplicity; their total is \(S x^{o(1)}\). Summing over \(s\) proves the first estimate of (2).

## 2. The intersection is a true free/free CRT sum

Use the combined (1) at the full physical arguments. Put \(n=sq\), \(m=N-n\), \(\mathcal W_s(n)=\kappa_s W_s(n/s)/\log(n/s)\). For fixed \(a,e,s\) the equation is \(a b+s e j'=N\) on the true unit support. If \((a,s e)>1\), or \((a s e,N)>1\), the unit support is empty. Otherwise the additional \(b>B_m,j'>B_q\) and central \(n\) restrict an interval. Exact CRT with \(\sum_{f\mid(b,N)}\mu(f)\) gives density \(\phi(N)/(N a s e)\) in \(n\), up to \(O(\tau_2(N))\) interval floor. The coefficient \(c_q(e;n/s)\) includes only a log-power variation in \(n\), so use ordinary partial summation. The number of possible tuples times the coefficient floors is
\[
 \ll x^{o(1)} S\frac{3x}{2 B_m}\frac{x}{S B_q}
          \ll x^{1-\alpha/2-2\delta+o(1)} .
\]
The actual main is therefore
\[
\sum_{\substack{s\sim S\ {\rm prime}\\(s,N)=1}}
  \int_I \mathcal W_s(n)\frac{\phi(N)}{Ns}
  \sum_{\substack{e<n/(sB_q)\\(e,N)=1}}\frac{c_q(e;n/s)}{e}
  \sum_{\substack{a<(N-n)/B_m\\(a,Ns e)=1}}
         \frac{-\big(\mu*\Lambda_{>V}\big)(a)}{a}\,dn .
\tag{4}
\]
Here the \(a\)-bound is at exponent \((1-\alpha)/2-\delta+o(1)\ge .425+o(1)\), and the \(e\)-bound at \(1/2-\alpha-\delta+o(1)\ge .355+o(1)\). They are polynomially long, including after dividing by either of the corresponding short \(\Lambda\)-cutoffs.

The exact identity \(\mu*\Lambda=-\mu\log\) follows by differentiating \(1/\zeta\). Thus the ordinary harmonic \(a\)-sum in (4) equals
\[
            -\frac{Ns e}{\phi(Ns e)}+O_D(L^{-D}).
\tag{5}
\]
The short \(\Lambda_{\le V}\) correction is uniformly negligible by summing \(\mu(d)/d\) at the reduced cutoff for each fixed short \(\ell\), with ordinary \(1/a\) multiplicative. The Euler derivative and log-power tails are those of (8) in the first switch. The arbitrary reserve in (5) absorbs all harmonic divisor masses, since \(|c_q(e;q)|\ll L\) (each prime-log convolution is bounded by \(\sum_{\ell\mid e}\Lambda(\ell)\)). As \((N,s e)=1\), the remaining density in (4) is exactly
\[
                       -\frac{1}{\phi(s e)}.
\tag{6}
\]
The terms \(s\mid e\) in this remaining harmonic sum cost power small: \(\sum_{e\le x,\ s\mid e}1/\phi(s e)\ll s^{-2}L^{O(1)}\) for prime \(s\), by \(\phi(s^2 f)\ge s(s-1)\phi(f)\); multiply by \(x\), count \(O(S)\) labels and pay fixed log weights. On the rest, (6) is \(-1/[(s-1)\phi(e)]\), with coprime mask \(F=Ns\).

## 3. The needed quotient harmonic mean with the true Euler denominator

For \(Z=n/(s B_q)\), \(F=Ns\), the matched finite tails of [UnmarkedSemiprimeWholeTypeI.md](UnmarkedSemiprimeWholeTypeI.md), (11), give
\[
 \sum_{\substack{e<Z\\(e,F)=1}}\frac{\mu(e)}{\phi(e)}
      \ll_D L^{-D},
 \qquad
 \sum_{\substack{e<Z\\(e,F)=1}}\frac{(\mu*\Lambda)(e)}{\phi(e)}
      =\mathfrak S(F)+O_D(L^{-D}).
\tag{7}
\]
The exact distinction between \(<Z\) and \(\le Z\) costs a single power-small term here and at the other polynomial endpoints. The short \(\Lambda_{\le V_q}\) convolution in the first term of \(c_q\) is negligible with the \(1/\phi\) denominator, just as below (11) in that note: for \(\ell=p^b\),
\(\phi(d)\phi(\ell)/\phi(d\ell)=1-p^{-1}1_{p\mid d}\).
Splitting into the two corresponding reduced \(\mu(d)/\phi(d)\) sums with masks \(F\) and \(F p\) gives arbitrary log reserve since \(Z/\ell\) is polynomially long. Thus the first term of \(c_q\) contributes \(-\mathfrak S(F)+O_D(L^{-D})\).

The term \(\mu_{>U_q}(e)\log(q/e)\) has negligible weighted sum: combine the finite sums of \(\mu(e)/\phi(e)\) at \(Z,U_q\), and the finite sums of \(-\mu(e)\log e/\phi(e)\) at those endpoints, whose main constants are the same. For the remaining term, use \(\mu_{>U_q}*\Lambda=\mu*\Lambda-\mu_{\le U_q}*\Lambda\). For \(d\le U_q\), \(Y=Z/d\) is polynomially long. Uniformly for \((d,F)=1\), the \(\ell\)-sum is
\[
 \sum_{\substack{\ell\le Y\\(\ell,F)=1}}\frac{\Lambda(\ell)}{\phi(d\ell)}
  =\frac{1}{\phi(d)}
      \left(\log Y+C_F-\sum_{p\mid d} b_p+O_D(L^{-D})\right),
 \qquad
 b_p=\frac1p\sum_{j\ge1}\frac{\log p}{\phi(p^j)}
       =\frac{\log p}{(p-1)^2}.
\tag{8}
\]
Indeed the \(\Lambda(\ell)/\phi(\ell)\) harmonic sum is \(\log Y+C_F+O_D(L^{-D})\) by ordinary prime number theory with log reserve, since the difference from \(\Lambda(\ell)/\ell\) converges absolutely. Removing the prime powers of primes dividing \(F\) changes the constant and incurs a uniform tail \(O(x^{o(1)}/Y)\) by \(\log F=O(L)\) and the geometric progression over powers; \(C_F=O(L^C)\). For primes \(p\mid d\) use the exact overlap factor \(1-1/p\) in the previous paragraph. Its tail beyond \(Y\) also costs \(O(x^{o(1)}/Y)\). This proves (8) uniformly.

Multiply (8) by \(\mu(d)\) and sum. The \(\log Y=\log Z-\log d\) part gives \(\mathfrak S(F)\) by (7) at \(U_q\); the \(C_F\) part is negligible. For the \(b_p\) part, split at \(p=x^{.035}\). The large-\(p\) tail is power-small even absolutely after using \(b_p\ll(\log p)/p^2\) and \(\sum_d1/\phi(d)\ll L\). At smaller \(p\) write \(d=p d'\); nonzero \(\mu(d)\) demands \((d',p)=1\). The remaining sum is \(-1/\phi(p)\) times the \(\mu(d')/\phi(d')\) sum up to \(U_q/p\) with mask \(F p\), again arbitrary-log small by (7). This proves that the weighted \(\mu_{\le U_q}*\Lambda\) sum is \(\mathfrak S(F)+O_D(L^{-D})\), hence the \(\mu_{>U_q}*\Lambda\) portion of (1) is negligible.

Combining these evaluations gives the uniformly negative quotient harmonic mean \(-\mathfrak S(F)+O_D(L^{-D})\) for \(c_q(e;q)\), with the exact inherited \(1/\phi(e)\) denominator. The minus sign of (6) makes the intersection main positive. Replace \(1/(s-1)\) by \(1/s\) at power-small cost and set \(u=n/s\). This produces precisely (3), proving the last two estimates of (2).

## 4. What actually survives both subtractions

The new forward coefficient is supported on \(B_m\)-smooth actual \(m\): if \(m=P u\), \(P>B_m\) prime, then \(u<U\), \(P\nmid u\). The only eligible \(d>U\) contain \(P\), \(\ell\) cannot be based on \(P\) (otherwise \(d\le u\) or the product repeats \(P\)), and \(d\ell>Q\) is automatic. Möbius convolution on \(u\) then gives \(C_m^{\rm hi}(m)=-\Lambda_{>V}(u)\), including nonsquarefree \(u\). The divisors \(a<m/B_m\) are exactly the divisors of \(u\); hence \(L_m(m)=-(\mu*\Lambda_{>V}*\mathbf1)(u)=-\Lambda_{>V}(u)\). On the quotient side, every summand with a prime \(>B_q\) in \(r\) or \(k\) is eliminated in the *combined centered coefficient*, as in the prior switch (a prime in the literal free \(j\) is not excluded).

These supports do not provide a one-sided bound. For instance on an actual squarefree balanced triple \(m\) with all three prime exponents near \(1/3\), the only eligible original \(d\)'s are products of two factors paired with the remaining \(\ell\), so \(C_m^{\rm hi}(m)=\log m\); the moving cutoff \(m/B_m\) retains all three individual primes but none of their pairs, so \(L_m(m)=-\log m\). Thus the new coefficient is \(2\log m\) there, not a general reduction in absolute size. Analogously a balanced triple \(q\) with all three prime exponents near \((1-\alpha)/3\) has \(C_q^{\rm hi}(q)=-\log q\) and \(L_q(q)=-3\log q\), leaving \(2\log q\). Both surviving supports allow this positive sign. The true reference in (2) is therefore necessary bookkeeping, not a proof of a favorable bound on the remaining correlation or of binary Goldbach.

For the complete \(s\)-band and exact semiprime weight \(K_{P_3}\), (3) is \((\log(7/5)-0.160+0.0192+o(1))M_N\) by (4) of the [original Type I proof](UnmarkedSemiprimeWholeTypeI.md). Thus the original budget \(T\le\eta M_N\) is equivalent, up to the displayed logarithmic error, to
\[
 \mathcal B(C_m^{\rm hi}-L_m,C_q^{\rm hi}-L_q)\le
 \mathcal M+\eta M_N+O_D(xL^{-D}).
\]
Allocating this cell the entire \(\eta=.010\) from the separate low-marker criterion would require a uniform upper bound near \(.205672M_N\) on the centered product. This does not repair other low cells or improve the budget for the original discrepancy.

For comparison, [Arneth's September 2026 Gold-IX](https://zenodo.org/records/23011147) also stresses that the uncentered Vaughan term need not be small and studies calibration for a different coupled comparison. The calculation here is the exact overlap from **both actual long-free switches** in the stated semiprime row, with both moving cutoffs and its original weight. It is not a claim of a new general main-term calibration technique or a resolution of the sign problem.
