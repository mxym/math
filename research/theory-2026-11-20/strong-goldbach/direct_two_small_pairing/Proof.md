# The exactly-two-small part of the direct fixed-target score

This treats one actual part of the direct, prime-versus-reflected-integer square-root score; it is not a comparison of auxiliary shared-index columns. We remove its entire moving square-root shoulder, **without a rank cutoff**, when the reflected integer has exactly two eligible small primes. An exact opposite-divisor comparison then shows that even macro parity cannot contribute a significant negative under this restriction. The remaining two-small signed term is explicitly antisymmetric in its two genuine macro factors.

Throughout fix the parameters of the calibrated pair completion: \(m\ge3\) odd and \(0<\epsilon<.04/m\), before taking \(x\to\infty\). Write \(N=2x\) even, \(L=\log x\), \(\ell=\log L\), \(z=\exp(L/\ell^2)\), and \(C_y=y/x^{1-\epsilon}\). Work on the physical interval \(x\le y\le1.5x\) and with the true prime weight
\[
 A(N-y)=\log(N-y)1_{\{N-y\ {\rm prime}\}}.
\]
Let \(\mathfrak S(N)\) be the ordered binary singular series, including the factor \(2\) at an even target. Put \(R_\pm=x^{1/2\pm\delta_x}\), with \(\delta_x=3\log\ell/\ell\). The direct score is the sum of the long raw divisor score above \(R_-\) and the calibrated free score above \(R_+\), with global roughness \(R_z(y)\). We analyze only **squarefree** \(y=pq M\) with \(z<p<q<C_y\) two true primes and every prime factor of \(M\) at least \(C_y\). This is exactly the two-eligible-small-prime family, not a condition on a formal average.

On this family the completed coefficient for every \(c\mid pq\) is exactly \(\mu_2(c)\), where \(\mu_2=\mu*\mu\): \(1,p,q\) are already below \(C_y\), and \(pq\) is either below the cutoff or supplied by the pair completion. No other \(c\) is supported, since any prime \(\ge C_y\) cannot divide a small \(c\); the \(m\)-prime payer is also absent, as it needs at least three distinct primes smaller than \(C_y\). Thus the literal score \(B_{\rm gap}\) there is
\[
 \sum_{\substack{a\mid y\\a>R_-}}\mu(a)\log(y/a)
 +\sum_{c\mid pq}\mu_2(c)
       \sum_{\substack{a\mid y/c\\a>R_+}}\log(y/(ca)).             \tag{1}
\]
No moving coefficient or variation of the payer is hidden in this exact reduction. Let \(B_0\) be the same expression with *both* free divisor thresholds replaced by the own square root \(R=\sqrt y\).

## 1. Uniform control of the actual moving shoulder

The following estimate holds for the entire stated family, with no bound on the number of prime factors of \(M\) other than its literal roughness:
\[
 \sum_{\text{this family}} A(N-y)\left|B_{\rm gap}(y)-B_0(y)\right|
 \ll_\epsilon \mathfrak S(N)x\,
    (\delta_x+L^{-1})(1+\log\ell)^2+O_\epsilon(x^{.65})
 =o_\epsilon(\mathfrak S(N)x).                                  \tag{2}
\]

To see this, each changed label has \(a=du\), \(d\mid M\), \(u\mid pq\), with \(R_-<du\le R_+\) up to harmless endpoints or absolute fixed enlargements. The statement \(a\mid y/c\) just restricts \(u\) further; it can be dropped for the positive absolute count. The number of \(c,u\) labels is bounded by an absolute constant, and the individual coefficients and \(\log\) weights are at most \(O(L)\). Write \(v=M/d\). Throughout the counted ranges \(d,v\ge x^{1/2-2\epsilon-\delta_x-o(1)}\) and both have all prime factors \(\ge x^\epsilon\). In particular these are truly two independent rough macro-variable lengths after fixing either one, not a sum over individual rank profiles.

Fix \(p,q,u,d\), put \(h=p q d\), and use the actual forms \(v\) and \(N-hv\), where \(v\) ranges in \([x/h,1.5x/h]\). Any \(r\mid(h,N)\) would divide the true prime \(N-hv\ge x/2\); but \(h\le x^{1/2+2\epsilon+\delta_x+o(1)}<x/2\) for sufficiently large \(x\), so that case is empty. On \((h,N)=1\) their simultaneous small-divisor root count at a prime \(r\) is one if \(r\mid hN\), and two otherwise. This includes one root at \(2\), as \(N\) is even and \(h\) odd. Use an ordinary dimension-two upper sieve on the product of the two forms, at level \(D=x^{.05}\), cutoff \(w=x^{c_\epsilon}\), with a fixed \(c_\epsilon<\epsilon/2\) sufficiently small for its fixed ratio. Both true forms are automatically \(w\)-rough on the target set. The local main is
\[
 \ll_\epsilon \frac{x}{h}\frac{\mathfrak S(N)}{L^2}.
\]
Indeed divide the exact sieve product by \(\prod_{r\le w}(1-1/r)^2\): the local generic factors are \(1-1/(r-1)^2\), and target primes have \((1-1/r)^{-1}\). The extra primes dividing \(h\) give only \(1+O(L/z)\) since \(h\) is \(z\)-rough. Omitting target primes above \(w\) changes the ratio by \(1+O(L/w)\); the generic omitted prime-square tail converges. The CRT floor errors per \(p,q,u,d\) are \(O(D(\log D)^C)\) by the squarefree root-count bound \(2^{\omega(r)}\), using the standard upper beta-sieve with bounded coefficient weights. Their total before logs is \(x^{.55+2\epsilon+\delta_x+o(1)}\), below \(x^{.65}\); two additional log weights are harmless in that reserve. This argument uses prime \(N-hv\) only through a valid upper sieve, never its unproved distribution for a fixed \(h\).

For \(d\) itself, each complete dyad meeting \([R_-/u,R_+/u]\) has harmonic mass \(O_\epsilon(L^{-1})\) on \(x^\epsilon\)-rough integers by the ordinary one-dimensional upper sieve with the same small polynomial level \(D\). The interval lower endpoint has a fixed polynomial power, so the corresponding floors are smaller than \(1/L\) on each dyad. The number of dyads needed is \(O(1+\delta_x L)\). Thus the \(d\)-sum of reciprocals is \(O_\epsilon(\delta_x+L^{-1})\), uniformly for each \(p,q,u\). All smaller primes are actual \(z<p,q\le1.5x^\epsilon\); their double reciprocal sum is \(O_\epsilon((1+\log\ell)^2)\) by Mertens. The logarithm of the true opposite prime and the score's logarithm cost only \(O(L^2)\), already paid by the two-form sieve. This proves (2). The proof also works for either endpoint taken at any fixed constant multiple of \(\sqrt x\) in place of the own centre; a multiplicative constant-width shoulder costs \(O_\epsilon(\mathfrak S(N)x(1+\log\ell)^2/L)\). No growing-rank use of a fixed-rank bound is involved.

## 2. Exact same-integer paired signs

Let \(d\mid M\), \(v=M/d\), and \(\eta_d=\mu(d)\). In the own-square-root score each nonzero term for this macro divisor arises by putting \(a=du\), \(u\mid pq\), \(du>R\). The corresponding complementary full small divisor (outside \(a\)) is \(pq/u\). The elementary complete convolution over it is
\[
 \sum_{c\mid pq/u}\mu_2(c)\log(v(pq/u)/c)
 =\mu(pq/u)\bigl(\log v-\log(pq/u)\bigr).
\]
This follows by expanding the two subset choices \(1,-2\) for each remaining small prime, and summing the logarithmic moment of each. Since \(\mu(pq/u)=\mu(u)\), the combined summand in \(B_0\) is exactly
\[
   \mu(u)\bigl[(\eta_d+1)\log v+
                   (\eta_d-1)\log(pq/u)\bigr].                 \tag{3}
\]
There is no tied own-square-root boundary: on squarefree \(y>1\), an integer \(du\) cannot equal \(\sqrt y\).

After summing \(u\), the three nontrivial strips for \(d\) give this literal table:
\[
\begin{array}{c|cc}
 & \mu(d)=+1 & \mu(d)=-1\\ \hline
 (R/p,R]\quad\text{outer}&-2\log v&2\log(pq)\\
 (R/q,R/p]\quad\text{middle}&0&2\log p\\
 (R/(pq),R/q]\quad\text{lower}&2\log v&0 .
\end{array}                                                    \tag{4}
\]
Above the three strips the full \(u\)-sum cancels by two independent small factors; below them it is empty. Crucially the same **physical** reflection \(d\leftrightarrow v=M/d\) exchanges outer with lower and maps middle to itself. It introduces no new integer \(y\), no change to the true opposite prime, and no new modulus. On \(\mu(M)=+1\), the two macro signs agree. The paired outer and lower terms are \(2\log(d/v)\ge0\) if both are even, and \(2\log(pq)>0\) if both are odd. Middle terms are already nonnegative. Thus \(B_0(y)\ge0\) on every squarefree case with these two small primes and even \(M\). Combining with (2) gives an actual signed lower \(-o_\epsilon(\mathfrak S(N)x)\) for the **whole even-\(M\) part**, at each prescribed even \(N\).

If \(\mu(M)=-1\), the middle terms remain nonnegative. The exact sum for an outer/lower pair represented by its outer divisor \(d\) is
\[
     \underbrace{\log y-2\log v}_{\ge2\log q}
                         -\mu(d)\log y.                         \tag{5}
\]
This is not a sign assertion. Its first term is favorable and the signed second term is the only possible negative of its pair. On squarefree \(M\), \(\mu(d)1_{\{\mu(M)=-1\}}=(\mu(d)-\mu(v))/2\); this turns the residual into a dependence on the two actual macroscopic factors rather than separate one-leg upper bounds.

## 3. Removing the genuinely tiny first label and the exact remaining test

Fix \(0<\alpha<\epsilon/2\). The negative contribution to \(B_0\) from \(p\le x^\alpha\) has a uniform upper bound on its magnitude,
\[
 O_\epsilon\!\left(\mathfrak S(N)x\,\alpha(1+\log(\epsilon/\alpha))\right)
       +o_\epsilon(\mathfrak S(N)x).                            \tag{6}
\]
One can use the same real two-form upper proof as §1, but now the only possibly adverse label is in the outer strip. For \(d\) above, the entire moving own-square-root strip is contained in a fixed ratio enlargement of \([\sqrt x/p,\sqrt x]\), so its harmonic mass is \(O_\epsilon((1+\log p)/L)\), not a charge independent of \(p\). Keep \(p,q\) in the resulting outer reciprocal sums. Since \(p\ge z\), ordinary prime partial summation and Mertens give
\[
 \frac1L\sum_{\substack{z<p\le x^\alpha\\p\ {\rm prime}}}
       \frac{1+\log p}{p}
       \sum_{\substack{p<q\le1.5x^\epsilon\\q\ {\rm prime}}}\frac1q
 \ll \alpha(1+\log(\epsilon/\alpha))+o_\epsilon(1).
\]
For example the inner sum is \(O(1+\log((\epsilon L+O(1))/\log p))\), and
\(\sum_{\log p\le t}(\log p)/p\ll 1+t\). Integration by parts, or the integral of \(1+\log(\epsilon/t)\) on \((0,\alpha)\), yields the claim; the contributions of the \(1\) in \(1+\log p\) are negligible since \(\log p\ge L/\ell^2\). The two logarithmic weights and local corrections are exactly as in (2). This proves (6) for all actual ranks in the selected family, not just finitely many angular boxes.

For the part not paid by (6), define \(\mathcal T_{\epsilon,\alpha}(N)\) to be the following literal signed oblique quantity:
\[
 \frac12
 \sum_{\substack{ y=p q d v\in[x,1.5x],\ y\ {\rm squarefree}\\
          p,q\ {\rm prime},\ x^\alpha\le p<q<C_y\\
          P^-(dv)\ge C_y,\ \sqrt y/p<d\le\sqrt y}}
          A(N-y)(\log y)\bigl(\mu(d)-\mu(v)\bigr).               \tag{7}
\]
Each macro divisor label is counted as such; \(p,q\) are the two unique smallest actual prime labels, and no factorization independence is claimed. Every input of (7) is polynomially rough, since \(p\ge x^\alpha\) and the other factors are \(C_y\)-rough. The sum of the original exactly-two-small \(B_{\rm gap}\) contributions has the lower bound
\[
 -\mathcal T_{\epsilon,\alpha}(N)
 -O_\epsilon\!\left(\mathfrak S(N)x\,\alpha(1+\log(\epsilon/\alpha))\right)
 -o_\epsilon(\mathfrak S(N)x).
\]
The positive drift in (5) can of course be retained, rather than thrown away in this lower bound. Thus even parity, the entire all-rank clock shoulder in this family, and arbitrarily tiny first labels are removed from the adverse part. The unproved signed statistic (7) is the remaining pair-specific test for this family. It is not a disguised binary-prime count, as both \(d,v\) are real rough factor groups and only \(N-y\) is required prime. A useful new bound would have to retain the difference of their Möbius signs against that **same** reflected prime; a separate Selberg upper supplies no such comparison.

Other families with three or more eligible small primes, including the higher-rank calibration payer and their clock shoulders, are not controlled here. Consequently even a strong small positive upper on (7) by itself would not prove strong Goldbach. The present gains are uniform at fixed true targets and scoped to this exactly-two-small score.
