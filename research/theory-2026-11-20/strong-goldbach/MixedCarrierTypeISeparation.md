# One mixed low carrier above the square-root Type I level

This uses Jain's [arXiv:2611.21136v1, Proposition 3](https://arxiv.org/html/2611.21136v1#S3.SS1) on the carrier of a positive mixed cell of the new polynomial log marker. The result is a Type I estimate and an exact signed Type II isolation for **this one unweighted cell**. Neither its remaining Type II estimate nor the analogue for the entire signed low residual is established.

Retain \(N,x,L,I,M_N,a,b,y,Z,V_0,F,K_{P_2},K_{P_3}\) from [PolynomialLogConservationMarker.md](PolynomialLogConservationMarker.md) and the notes cited there. Take \(s\) fixed sufficiently large, in particular \(\varepsilon<.023,\delta<.001\). Use exponent intervals with half-width \(10^{-8}\) about .24 and .25 for two macro prime labels \(A,B\); use nine disjoint prime exponent intervals of half-width \(10^{-9}\) about \(.054+(j-5)10^{-7}\) for \(q_1,\ldots,q_9\). Let \(C(n)\) be the indicator of
\[
 n=A B q_1\cdots q_9 v\in I,\qquad
 P^-(v)\ge y,\qquad |\log_x v-.024|\le10^{-6}.
 \tag{57}
\]
The suffix interval is redundant for such products in \(I\) once \(x\) is large: the marked exponents sum to \(.976+O(10^{-7})\) and \(\log_x n=1+O(1/L)\). It is imposed independently, not as a condition depending on \(q_j\). Its factors cannot meet any labelled interval. Consequently (57) is a \(0,1\) indicator, not a count of several representations. Write \(A_C=\sum_{n\in I}C(n)\), and let \(J=\{m:N-m\in I\}\).

This is a positive on-scale mixed carrier. On its squarefree members the old \(F=0\), since just the two macro primes qualify and their product exponent is near .49. Every small tuple of degree at most three containing one of the nine labels moves the cutoff past the macro pair, but not past either singleton. Indeed .49+.054 is strictly above \(\beta\) and \(.25+3\cdot .055<\beta\). The shifted \(F\) for each such tuple is \(-1\). In the polynomial formulas the tuples using only suffix primes have total error at most \(\sum_{j=1}^{3}|c_j|(.025)^j\), while the entire small log mass is .51 up to \(o(1)\) and the narrow macro bands. Thus \(K_{P_i}>.86\) for \(i=2,3\), as in §4 of the polynomial note. As \(N\) tends to infinity at fixed \(s\), then \(s\) grows, the \(b\) reference mass is asymptotic to a strictly positive constant times \(M_N/\varepsilon\). Fix the eleven labelled primes, apply the uniform Buchstab formula to the rough suffix whose exponent stays within \(10^{-6}\) of .024, and sum their reciprocals by PNT, exactly as in the prior note. Squareful exceptions cost \(o_s(M_N)\).

## 1. Full-carrier large-residue Type I

For every \(B_0>0\) the following holds uniformly in the even \(N\), with constants depending on the fixed \(s\) and on \(B_0\):
\[
 \sum_{r\le x^{.573}}\sup_{t}
  \left|\sum_{\substack{m\in J\\m\le t,\ r\mid m}}C(N-m)
       -g_N(r)\!\!\sum_{\substack{m\in J\\m\le t}}C(N-m)\right|
       \ll_{s,B_0} xL^{-B_0},
 \qquad g_N(r)=1_{(r,N)=1}/\varphi(r).
 \tag{58}
\]
No factorizability of progression weights is required in this unweighted modulus sum. The source is the **general threefold Proposition 3**, not Jain's theorem for the indicator of all smooth numbers.

For \(r\le x^{.49}\), ordinary prime-product BV applies directly after decomposing the suffix by its bounded rank at fixed \(s\). Partition its factor positions by fixed bins separated from the eleven named slots; product endpoints can be handled by Mellin separation as below. Equivalently, one can use the classical BV theorem for a convolution of Siegel–Walfisz sequences with an independent prime slot: any additional suffix weights are bounded. For the prime-product version, the suffix factors are in \([y,x^{.025}]\), disjoint from the named slots, so for each fixed rank use the permitted prime intervals in [Liu–Park–Song, Theorem 3.2](https://link.springer.com/article/10.1007/s40993-017-0089-3#Sec3) and the proof by convolution dyadic boxes. In this range the repeated-prime suffix part may be removed at the progression level: sum the trivial count \(O(x/(rp^2)+1)\) on \((r,p)=1\) over \(p^2\mid n,\ p\ge y,\ p\le\sqrt x\), and use the \(r\)-multiple harmonic bound on the remainder. Alternatively keep repeats in the bounded suffix sequence and convolve by the standard bilinear BV estimate. In the first choice, the suffix restriction on its own product is redundant on \(I\), and \(r\) coprime to \(p\) is the only case needed for replacing the coprime total when \(p\) shares a modulus prime. For \(r\) sharing \(p\) in the residue condition, either \(p\nmid N\) gives zero or \(p\mid N\) is included in the noncoprime disposal below. Maximal prefixes follow from the uniform proof or the grid argument below.

For larger \(r\), use the following three groupings. A notation \(kq\) means a product of \(k\) different assigned labelled slots, with every slot assigned exactly once in a row. \(R\) is the dyadic modulus size. The letters \(M_0,U_0,V_0'\) are the three factor lengths in Jain's notation \(M,N,L\), with no relation between \(V_0'\) and the sieve normalization \(V_0\).
    
| \(M_0\)-group | \(U_0\)-group | \(V_0'\)-group | central exponents \((m,u,v)\) | modulus exponent \(\log_xR\) |
| --- | --- | --- | --- | --- |
| \(A(4q)\) | \((3q)v\) | \(B(2q)\) | \((.456,.186,.358)\) | \([.49,.542]\) |
| \(B(3q)v\) | \(3q\) | \(A(3q)\) | \((.436,.162,.402)\) | \([.538,.562]\) |
| \(A(3q)v\) | \(3q\) | \(B(3q)\) | \((.426,.162,.412)\) | \([.561,.573]\) |

Each group coefficient is 0 or 1 by unique factorization, since the bounded rough suffix cannot meet a marked interval. Thus Jain receives three 1-bounded coefficients. Decompose them into dyadic group intervals; there are \(L^{O(1)}\) boxes, and each contributing box has \(x'=M_0U_0V_0'\asymp x\). Impose \(x/2<n\le x\) and any endpoint inside it by a smooth Mellin cutoff with width \(xL^{-B_1}\) and transform \(L^1\) norm bounded by a fixed power of \(L\). For example smooth the indicator in \(\log(n/x)\) at width \(L^{-B_1}\); two differentiations bound the integral of the transform. Mellin twists multiply each group by a phase and preserve the 1-bound in Proposition 3. The transition error in each actual residue class is \(O(xL^{-B_1}/r+1)\) because \(C\le1\); in the expected coprime term it is \(O((xL^{-B_1}+1)/\varphi(r))\). One may first apply Proposition 3 to the smoothed endpoint with the low-character correction, then bound that correction directly as below, and compare only the actual and principal terms at the transitions. Thus no extra \(D^2\) factor for the low-character subtraction is needed in this transition. Choose \(B_1\) sufficiently large. For the maximal prefix, mesh endpoints with \(O(L^{B_2})\) points spaced at most \(xL^{-B_2}\), use the pointwise estimate with arbitrary larger log saving on every grid point, and then use the same per-modulus transition bound before summing. This handles both sharp endpoints uniformly. Dyads crossing a seam can be assigned to either adjacent interval by the overlaps in the table; \(\log_x2=o(1)\).

Here are all the exponent checks for (3.1) of the primary theorem. With \(\theta=7/32,\ r_*=\log_x R\) and \(a_1=N,\ a_2=1\), the required limiting inequalities are \(u>0\), \(u+v<2/3\), \(v<m\), and
\[
 r_*\in(m,u+v),\quad
 r_*>2u+3v-1,\quad
 r_*>\frac{(7-4\theta)u+(4-\theta)v-2+2\theta}{2+\theta},
 \quad r_*>\frac{7u+4v+\theta-2}{2}.
\]
For the three central rows the last four lower endpoints (starting with \(m\)) and upper endpoint \(u+v\) are respectively
\[
\begin{array}{c|ccccc}
 1& .456&.446& .41935212\ldots &.476375&.544\\
 2& .436&.530& .42808451\ldots &.480375&.564\\
 3& .426&.560& .44512677\ldots &.500375&.574 .
\end{array}
\]
In particular the smallest margin across the prescribed modulus ranges is .001. All group exponent perturbations can be taken \(<10^{-5}\) from the label and suffix widths and \(\log_x2=o(1)\). Normalizing instead by \(\log x'\) changes them by \(O(1/L)\); also \(\log_{x'}|a_1|=1+O(1/L)\). The inequalities hold with the required strict losses on choosing Jain's \(\varepsilon_{\mathrm{Jain}}=10^{-4}\): the last three exponent inequalities retain \(>\!0.0008\) before the \(10^{-4}\) loss, and the margins \(2/3-(u+v)\) and \(m-v\) are \(>\!0.01\). This proves all (3.1) conditions with common slack.

Jain's Proposition 3 removes conductors up to \(D_0=x^\eta\), with \(\eta>0\) chosen smaller than his allowed cutoff exponent, \(\varepsilon/10\), and \(10^{-3}\). The upper bound then has a fixed power saving. Sum the dyadic group (and modulus) boxes with only log-power loss. For \(1<d\le D_0\) primitive, the conductor \(d\) can induce at most one character in each multiple modulus \(r\), with
\[
 \sum_{r\le x^{.573},\ d\mid r}\frac1{\varphi(r)}\ll \frac{L}{\varphi(d)}.
\]
Replacing the induced coprimality factor by the primitive character costs at most
\(O(xD_0^2 L/y)\) in total: every full product on the carrier has prime factors \(\ge y\), and the number divisible by \(p\mid r\) is \(O(x/p)\); sum \(1/\varphi(r)\) over its multiples and \(\sum_{p\ge y}1/[p(p-1)]\ll1/y\). This is power saving. Physical nonreduced classes with \((r,N)>1\) contribute zero if the common prime is \(<y\), and otherwise their raw summed \(O(x/r+1)\) bounds over divisors of \(N\) are \(O_s(xL^2/y)\) through \(x^{.573}\). Similarly restore the full coprime total in each reduced principal term at total \(O(xL/y)\).

For the remaining primitive character sums, fix all factors but any one of the nine marked primes \(q_1\). Their product \(h\) includes the suffix \(v\) chosen beforehand in its independent range. On a nonempty \(q_1\)-interval cut by the endpoint and the box, \(X_h=x/h\) is \(x^{.054+O(10^{-6})}\). The ordinary maximal primitive mean-value form of Bombieri–Vinogradov gives, uniformly in this scale,
\[
 \sum_{1<d\le D_0}\frac1{\varphi(d)}
       \sum_{\chi\bmod d}^{*}
       \max_{Y\le 2X_h}\left|
          \sum_{\substack{q\le Y\\q\ {\rm prime}}}\chi(q)\right|
 \ll_{A} X_h L^{-A}.
\]
See the maximal Vaughan mean value estimate in [Akbary–Hambrook](https://arxiv.org/abs/1309.2730), combined with Siegel–Walfisz for the smaller conductors and partial summation. There is ample power room \(D_0\ll X_h^{1/20}\), for example with the above \(\eta\). The smoothed endpoint is permitted either by variation (smooth an interval by convolution with a positive bump, retaining bounded variation), or by the same dyadic interval supremum. The factors fixed in \(h\) have reciprocal sum \(O_s(L)\): all named prime reciprocal sums are bounded, and the integer suffix reciprocal sum is \(O(L)\). Multiplying by \(\chi(h)\) and summing in \(h\) loses only log powers. This completes (58). No weighted primitive mean value estimate is required here.

## 2. What (58) removes in actual prime detection

Define a signed weight on \(m\in J\) by
\[
 c_N(m)= C(N-m)-\frac{2A_C}{x}\frac{1_{P^-(N-m)\ge Z}}{V_0},
 \qquad Z=e^{L^{1/4}},\quad V_0=\prod_{\ell<Z}(1-1/\ell),
\]
extended by zero outside \(J\). The constant multiplier matches the **whole** carrier mass, but not each individual prefix. This causes no difficulty: for any prefix \(t\) let \(E_N(t)\) be the difference of the two unconditional prefix masses. For the Vaughan logarithmic Type I term below one only needs \(\sum_r \sup_t|\sum_{r\mid m,m\le t}c_N(m)-g_N(r)E_N(t)|\), and also that integration against the logarithmic variation of \(E_N(t)\) is small. Use instead a proportional reference with the same prefix density by conditioning on slightly finer intervals as explained in the next paragraph. This avoids inferring pointwise prefix shape from progression equidistribution.

Partition \(J\) into intervals of length at most \(x L^{-B_3}\), with all but the last of common length and the last absorbed into the penultimate interval if necessary. In each interval \(J_j\) replace \(2A_C/x\) by \(A_{C,j}/|J_j|\), where \(A_{C,j}=\sum_{m\in J_j}C(N-m)\) and \(|J_j|\) is its integer length. The multiplier is in \([0,1]\). For a prefix *inside a mesh cell*, the unconditional discrepancy of the two masses is at most \(O(|J_j|\log Z)\), since the first carrier is bounded by 1 and \(V_0^{-1}\ll\log Z\). Fully covered cells have total discrepancy \(O_A(xL^{-A})\) by the CRT calculation of the subpower-rough reference, after an extra log-power reserve absorbs the number of cells. The same CRT estimate, now on divisibility by each \(r\le x^{.573}\), has polynomial room \(x^{.573+o(1)}\) for the floor errors, and main \(g_N(r)\) up to arbitrarily small log-power error; see (3) in the original criterion. Apply (58) to each subinterval and sum the log-power number of cells. Hence with this **mesh-matched** \(c_N\), for every prescribed \(A>0\), taking \(B_3\) large enough,
\[
 \sum_{r\le x^{.573}}\sup_t
       \left|\sum_{m\le t,\ r\mid m}c_N(m)\right| \ll_{A,s}xL^{-A}.
 \tag{59}
\]
Equivalently a fixed exponent \(B_3\) sufficiently large for a fixed desired \(A\) suffices below. This accounts for the possible moving prefix of the carrier; a global constant normalization alone would not justify (59).

The mesh reference has prime-weighted integral \(\mathfrak S(N)A_C+o_s(M_N)\) by the same subpower Bonferroni progression calculation as (4) in the original criterion. Its maximal BV errors summed over a log-power number of cells cost an arbitrary log power by choosing reserves; no prime asymptotic in intervals of power-short length is needed. The reference \(b\) on \(C\) from the polynomial note has that same leading mass with error \(o_s(M_N)\). Prime powers on \(m\in J\) cost \(O(x^{1/2}L^C)\), using the bounded carrier and the subpower reference bound. Therefore \(\sum_m c_N(m)\Lambda(m)=\sum_{n\in I} C(n)w(n)+o_s(M_N)\).

Set \(U=V=x^{.286}\). The exact Vaughan identity is
\[
 \Lambda=\mu_{\le U}*\log+\Lambda_{\le V}
       -\mu_{\le U}*\Lambda_{\le V}*1+\mu_{>U}*\Lambda_{>V}*1.
\]
The second term vanishes on \(J\). For the first use (59) with partial summation at cost \(O(L)\); the third uses moduli \(d\ell\le UV=x^{.572}\) and coefficients at most \(\sum_{\ell\mid m}\Lambda(\ell)=\log m\) after collecting that modulus. Both are \(o_s(M_N)\), with no divisor-weighted Type I required. Consequently
\[
 \sum_{n\in I} C(n)w(n)
   = \sum_{\substack{d>U,\ k>V}}\mu(d)
          \left(\sum_{\substack{\ell\mid k\\\ell>V}}\Lambda(\ell)\right)
          c_N(dk)+o_s(M_N).
 \tag{60}
\]
This is a precise bounded-factorization, fixed-large-shift Type II problem with \(dk\in J\), so both variables are between \(x^{.286}\) and \(O(x^{.714})\). No \(M_N\)-scale cancellation in (60) is proved. In particular the fact that \(C\) has ordinary moduli up to \(x^{.573}\) doesn't imply exchangeability with real primes or control the additional variable weight \(K_{P_i}(n)\) on this cell. The latter would require its own endpoint separation or a one-sided argument. Above-BV distribution feeds the known terms in (60), not the parity-sensitive remainder.


## 3. A more specific parity-sensitive remainder

Put \(Q=x^{.573}\) and \(D_1=x^{.560}\). The factor \(\sum_{\ell\mid k,\ \ell>V}\Lambda(\ell)\) vanishes for \(k\le V\), so we may allow every \(k\) in (60). For \(U<d\le D_1\), expand that factor as \(\log k-\sum_{\ell\mid k,\ \ell\le V}\Lambda(\ell)\). The \(\log k\) part and all terms with \(d\ell\le Q\) are Type I by (59), exactly as in §2. In the other terms, \(\ell>Q/d\ge x^{.013}\). Prime powers \(\ell=p^j,\ j\ge2\) there cost \(o_s(M_N)\): using \(|c_N|\ll\log Z+1\), their absolute total is at most
\[
 O\left(xL^{O(1)}\sum_{\substack{\ell=p^j>x^{.013}\\j\ge2}}\frac{\Lambda(\ell)}{\ell}\right),
\]
which has power saving by splitting \(p\ge x^{.0065}\) and \(p<x^{.0065}\) and summing the prime-power geometric tail. Thus in the lower-\(d\) block (60) has precisely the remaining signed sum
\[
 -\sum_{\substack{U<d\le D_1,\ Q/d<p\le V\\ p\ {\rm prime}}}
      \mu(d)\log p\,\sum_{h\ge1}c_N(dph)+o_s(M_N).
 \tag{61}
\]
Its short cofactor satisfies \(h\ll x^{.427}\). The upper-\(d\) block \(d>D_1\) still has the original signed coefficient and \(k\ll x^{.440}\). These supports suggest switching by a short cofactor in (61), but do not give its estimate.

If the block in (60) is dyadically restricted to \(d\asymp D', k\asymp K', D'K'\asymp x\), Cauchy in \(d\) bounds its square by \(O(D')\) times
\(\sum_{d\asymp D'}|\sum_{k\asymp K'}\beta(k)c_N(dk)|^2\), where \(\beta(k)=\sum_{\ell\mid k,\ell>V}\Lambda(\ell)\). The diagonal \(k_1=k_2\) is \(O(xL^{O(1)})\) before the \(D'\) factor, giving \(O(x^{.857}L^{O(1)})=o(M_N)\) after taking square roots. The open difficulty is the **off-diagonal quotient-weighted covariance** with \(n_i=N-dk_i\); although \(n_1-n_2=d(k_2-k_1)\) cancels \(N\) in the difference, the weights still depend on the quotients \(k_i\) and on the common progression at the original target. Proposition 3 controls only unweighted sums down that progression; replacing the two \(\beta(k_i)\) by their means here is a further unproved arithmetic step, not a consequence of (58).
