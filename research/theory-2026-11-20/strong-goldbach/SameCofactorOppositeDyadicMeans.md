# Opposite genuine dyadic means after macro-core regrouping

The two lines of equation (4) in [SameCofactorPhysicalMacroCore](SameCofactorPhysicalMacroCore.md) will be denoted \(P_N\) (pure macro) and \(B_N\) (mixed core), with their signs exactly as printed there. This note gives their actual \(M_N\)-weighted means over all even targets of a dyad. In particular the mixed term alone cannot be kept below the full .00659 allowance: its mean is already \(>.068\). This is not an obstruction to the **joint signed** bound.

Fix the original marker \(\delta\in(0,.001]\). For real \(X\to\infty\) sum over even \(N=2x\) with integer \(x\in[X,2X]\). The following are ratios of sums, not unweighted means of the pointwise ratios:
\[
 \frac{\sum P_N}{\sum M_N}\longrightarrow-J_\delta(H_2+H_3),\qquad
 \frac{\sum B_N}{\sum M_N}\longrightarrow+J_\delta(H_2+H_3),                 \tag{1}
\]
where \(J_\delta\) is the literal reference (1) of [SameCofactorVaughanCenter](SameCofactorVaughanCenter.md), and
\[
 H_2=\log 3,\qquad H_3=\frac12
      \int_{\substack{a,b\ge1/4\\a+b\le3/4}}\frac{da\,db}{ab}>0.
\]
Since \(\kappa_\delta(t)=\log[(.5-2\delta)/(.5-t+2\delta)]\) decreases in \(\delta\), \(J_\delta\ge J_0>.06282\) by the rational certificate of that note. Also \(\log3>1.09\). Thus in every sufficiently large dyad some actual \(N\) has \(B_N>.068M_N\). Neither (1) nor that consequence gives a pointwise sign for \(P_N+B_N\).

## 1. Genuine source measures after averaging

Write \(L_X=\log X\), \(n=su\), \(m=N-n\), \(y=n/X\), \(z=m/X\). All real source integers \(n\) and true reflected prime, rough, and macro-product integers \(m\) here are odd for large \(X\). Thus the sum over even targets is exactly the unrestricted sum over these \(n,m\) in
\[
             \mathcal D=\{2\le y+z\le4,\ y\le z<3y\}.                  \tag{2}
\]
There is no extra parity factor in this change of variables. Variables are in compact intervals bounded away from zero. The unit requirement \((n,N)=1\) when used in the pure-macro line removes only \(o(X^2/L_X)\) weighted pairs: \((n,N)=(n,m)\), and any common prime divisor is at least \(X^{.10}\) up to a fixed factor. The crude count
\[
       \sum_{cX^{.10}\le p\le 3X}O((X/p+1)^2)
                     =O(X^{1.9}+X\log X)
\]
even with all integer bases pays any fixed log weights. The small mark is genuinely unique, so no power-size multiplicity is hidden.

Freeze the source's exponent parameter \(x\) at \(X\), keeping all actual prime and semiprime labels. The \(s\) endpoints change by only fixed multiplicative factors; these boundary windows have reciprocal prime harmonic \(O(1/L_X)\). For the quotient lower cutoff \(X^{.5+2\delta}/s\), the change also lies in a fixed multiplicative window, with reciprocal prime harmonic \(O(1/L_X)\) at each actual \(s\). It can affect only the balanced semiprime branch. Count its other factor by ordinary prime upper bounds at its remaining polynomial scale. These bounds show that the sum of the absolute source differences over possible \(n,s,u\), even taking the union over all \(x\) in the dyad, is \(O(X/L_X^2)\). The central interval in (2) itself is not frozen. The smooth weight \(f(\log s/\log n)=f(\log_X s)+O(1/L_X)\) costs likewise \(O(X/L_X^2)\) over true source rows.

For any fixed interval \([c,d]\) in the compact \(y\)-range, this frozen source measure satisfies
\[
   \sum_{cX\le n\le dX} C_X(n)
       =(d-c)\frac{X}{L_X}\,(J_\delta+o(1)).                        \tag{3}
\]
The analogous unsigned mass is \(O(X/L_X)\). Here \(C_X(n)\) is the sum of the frozen \(C_s(n/s)\) over genuine \(s\); it is not a sequence defined by removing the true quotient condition. To check (3) explicitly, let \(Y=X/s,\ \sigma=\log_X s\), and \(\lambda=.5-\sigma+2\delta\). The prime quotient count on \([cY,dY]\) is \((d-c+o(1))Y/((1-\sigma)L_X)\). In the distinct semiprime branch take its smaller factor \(p>X^\lambda\). The constant-factor strip \(p\asymp\sqrt Y\) in which the larger-factor lower endpoint can cross \(p\) costs \(O(Y/L_X^2)\) by two ordinary prime upper bounds. Else the larger factor prime count on \([cY/p,dY/p]\) is the usual PNT main, uniformly since both factors are polynomially long. Prime Mertens or partial summation of the PNT on the smaller factor gives multiplicative ratio to the prime count
\[
 (1-\sigma)\int_\lambda^{(1-\sigma)/2}
       \frac{dt}{t(1-\sigma-t)}
       =\log\frac{.5-2\delta}{.5-\sigma+2\delta}.
\]
The error is \(o(Y/L_X)\) uniformly in \(s\) on the fixed band. Multiplying by \(1-f(\sigma)\) and \(-1-f(\sigma)\), respectively, then using the prime reciprocal density \(d\sigma/\sigma\) on \(s\), gives precisely (3). Thus both true quotient branches are present with their actual opposite signs.

## 2. Reflected factor measure and normalization

For the pure-macro line the reflected logarithmic measure of \(m\) with exactly \(j=2,3\) true distinct prime factors and all factors \(>U=x^{1/4-(\log x)^{-.49}}\) has limiting mass \(H_j\) per unit length. One can freeze the moving exponent to \(1/4\): for any fixed \(\eta>0\), all possible changes lie in factor-exponent strips \([1/4-\eta,1/4+\eta]\) relative to \(X\), for large \(X\). Their weighted product PNT mass is \(O(\eta X)+o(X)\), uniformly in the dyad; let \(\eta\downarrow0\) after the \(X\)-limit. Here is the elementary product PNT for this application. For a fixed interval \(m\in[cX,dX]\), open \(j-1\) labelled prime factors and use the PNT on the last prime \(q\) in \([cX/P,dX/P]\), \(P\) the product of the opened labels. Its weighted \(\log m\) main is \((d-c)X/[P(1-\log_X P)]\), up to a uniformly small relative error off a fixed tiny boundary strip. This follows from \(\log m=L_X+O(1)\), \(\log q=(1-\log_X P)L_X+O(1)\). All eligible exponents remain bounded away from 0. The prime harmonic measure on each opened label tends to \(dt/t\) on its log exponent. First approximate the compact angular constraints by finitely many boxes, then remove their boundaries by dominated convergence. Repeated primes are negligible by square support above \(X^{1/4-\eta}\) with at most a fixed number of factorizations. Divide by \(j!\) for distinct unordered factors. The resulting density is
\[
 H_j=\frac1{j!}\int_{\substack{t_i\ge1/4\\\sum_i t_i=1}}
                           \frac{dt_1\cdots dt_{j-1}}{\prod_i t_i}.
\]
For \(j=2\) integration gives \(\log3\); for \(j=3\) use \(1/(abc)=1/(ab)+1/(bc)+1/(ca)\). In particular the total reflected absolute measure in the dyad is \(O(X)\), which also pays the source-cutoff errors of §1. On the pure-macro line the \(R_Z\) guard is identically one. The \(\log m\) is the actual physical Vaughan weight.

The product measures of genuine \(n,m\) may now be summed over (2): approximate its boundary by a rectangular mesh, using (3) separately on the two nonnegative scored source branches and the reflected nonnegative measure. The boundary has zero Lebesgue measure. With \(w=(y+z)/2\in[1,2]\), the Jacobian is 2, and \(w/2<y\le w\), so \(|\mathcal D|=\int_1^2 w\,dw=3/2\). This yields
\[
       \sum P_N=-(3/2+o(1))J_\delta(H_2+H_3)X^2/L_X .
\]
Meanwhile \(\sum M_N\sim (3/2)X^2/L_X\). For the latter use the mean of \(\mathfrak S(2x)\) over integers \(x\), equal to 2. Indeed, expand the odd squarefree divisor product with local coefficient \(1/(p-2)\); the weighted divisor mean is \(\prod_{p>2}(1+1/[p(p-2)])\), canceling \(C_2\). Its mean series converges absolutely, and the floors are \(O(L_X^C)\) by the harmonic Euler product before taking a Cesàro limit. Partial summation supplies the slowly varying \(x/(2\log x)\) normalization. This proves the first limit of (1).

## 3. The whole-cell mean does not assume binary Goldbach

It remains to justify that \(\sum G_N=o(\sum M_N)\). This uses an **independent** reflected measure after summing actual targets, not a pointwise binary-prime assertion. Weighted true prime \(m\) contributes unit density on every fixed macroscopic interval by PNT. The literal \(R_Z(m)/V_0\) contributes the same unit density. To see this with the moving \(x\) in the dyad, freeze \(Z\) at \(Z_X=e^{L_X^{1/4}}\). The ratio of the largest to smallest cutoff is \(1+O(L_X^{-3/4})\). The union of possible guard differences is contained in multiples of integer bases in that interval; their count is \(O(X L_X^{-3/4}+\exp(O(L_X^{1/4})))\), and their normalized weight is \(O(L_X^{1/4})\). The \(V_0\) factor also changes by only a relative \(O(L_X^{-3/4})\) using the same reciprocal range. Thus the total reflected difference at any chosen dyadic targets, after multiplying by the unsigned source mass \(O(X/L_X)\), is \(o(X^2/L_X)\). With fixed \(Z_X\) the rough density follows by ordinary Bonferroni at depths \(\asymp L_X^{1/4}\): the floor cost is \(\exp(O(L_X^{1/2}))\) and the factorial main tail is smaller than every log power. Both the true prime and this rough source are supported on odd \(m\), so the same domain (2) is exact in each case.

By (3) and the rectangular mesh, the prime and rough terms in \(\sum G_N\) have the same leading integral. Hence the stated mean zero follows. Summing the uniform error \(O_\delta(M_N(\log x)^{-.46})\) in the macro-core reduction is \(o(\sum M_N)\), so the other mean in (1) must be the opposite. A successful bound must retain actual paired signed compensation; separate nonpositive control or full-budget positive caps on the mixed term contradict (1).
