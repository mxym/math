# Balanced signed columns and selected mixed rows at a fixed target

This is a scoped application of [Maynard, *Primes in arithmetic progressions to large moduli III*, Theorem 1.2](https://arxiv.org/pdf/2006.08250) ([accepted version](https://ora.ox.ac.uk/objects/uuid%3Ada3b7279-d413-4ab1-962e-afa5d67507c2)) to the common-index covariance of [Pham, *Uniformity, Local Structure and Boundary Correlations in Goldbach Representations*, Appendix D](https://www.preprints.org/manuscript/202610.3061). There are two complementary results. Sections 1–3 show signed cancellation for a complete row test on a large common-\(k\) family. Sections 4–5 prove the selected anchored variance of Appendix E on the same shape of family in the *physical slope* \(d\), yielding the actual mixed \(AB\) estimate with arbitrary \(e\) and \(e\)-dependent endpoints. Neither supplies the remaining true-prime \(AA\) estimate in the two-slope covariance of Proposition D.5. This is not a Goldbach lower bound.

Let \(N=2x\) be a prescribed even integer, \(Y=\sqrt x\), \(L=\log x\), \(\ell=\log L\), \(z=\exp(L/\ell^2)\), and \(V_z=\prod_{p\le z}(1-1/p)\). Set
\[
 a(n)=\log n\,1_{n\ {\rm prime}},\quad b(n)=V_z^{-1}1_{P^-(n)>z},
 \qquad g(n)=a(n)-b(n).
\]
All row and column variables range in fixed positive compact multiples of \(Y\). Impose \((de,N)=1\) and the physical cuts \(x/2<dk,ek\le x\). Restrict the common \(k\) to
\[
 {\cal K}_N=\{k:(k,N)=1,\ p_2p_3\mid k\text{ for some primes }p_2,p_3,\quad
        (u,v)=(\log p_2/L,\log p_3/L)\in\mathcal W\},
 \quad \mathcal W=\{.003\le u\le .048,\quad .1005-u\le v\le .0995-.6u\}.
\]
There is no squarefree or smooth-modulus assumption on \(k\).

Let \(J_{d,k}\) be any interval of \(e\) in the allowed range, clipped to \(x/2<ek\le x\). For each \(j\le x^{.00001}\) allow one residue \(e\equiv h_j(d,k)\pmod j\) or none, and a complex coefficient \(|c_j(d,k)|\le\tau(j)^F\), all chosen arbitrarily. Retain prescriptions only if \((N-kh_j,kj)=1\) or \(P^+(j)\le z\). In the nonunit prescriptions of the latter kind the original summand is zero. In particular \(h_j=0\), \((j,N)=1\), is allowed. If \(|u_{d,k}|\le\tau(d)^F\) is arbitrary, then for every fixed \(F,A\),
\[
 \left|\sum_{k\in{\cal K}_N}
 \sum_{\substack{d,\ (d,N)=1\\x/2<dk\le x}}u_{d,k}g(N-dk)
 \sum_j c_j(d,k)
 \sum_{\substack{e\in J_{d,k},\, (e,N)=1\\e\equiv h_j(d,k)\bmod j}} g(N-ek)\right|
 \ll_{F,A} x^{3/2}L^{-A}.                                             \tag{1}
\]
This holds also excluding \(d=e\). When \(j=1\) it genuinely cancels a signed sum of \(AA-AB-BA+BB\) in Pham's notation, allowing one complete \(e\)-interval and arbitrary opposite coefficients. In that case \(e\) may additionally be required to be \(z\)-rough. No independent arbitrary Möbius or true-prime mask on the \(e\)-row is claimed.

**Size of the block.** For example, take \(k\in[Y,1.1Y]\) and \(d,e\in[.65Y,.8Y]\), \(j=1\), and unit weight. All the physical cuts hold. The four individual nonnegative terms, summed on this same \(k\)-family, each equal
\[
 (.15Y)^2\sum_{\substack{k\in[Y,1.1Y]\\ k\in{\cal K}_N}}
     (k/\varphi(k))^2+O_A(x^{3/2}L^{-A}).                             \tag{2}
\]
Its main exceeds \( (0.12+o(1))\) times the full unit reference in the same geometry, uniformly in \(N\). The same fraction holds with fixed nonnegative bounded-variation weights on \(d/Y,e/Y,k/Y\) and the actual physical cuts, provided their reference volume is positive. This is a fraction of the expected unsigned mass, not of the unknown signed residual, and the comparison is relative to \((k,N)=1\), not to all \(k\). The actual unsigned scale in (2) is \(\gg x^{3/2}\varphi(N)/N\). A prime pair counted in \(AA\) cannot itself sum to \(N\): modulo its common unit \(k>1\) the sum is \(2N\), not \(N\).

## 1. The actual progression at the balanced scale

Choose one valid pair \(p_2,p_3\) canonically for \(k\). For each selected \(h=h_j(d,k)\) the prime row is in the progression \(N-kh\bmod kj\). In Maynard's theorem set
\[
       q_2=p_2,\quad q_3=p_3j,\quad q_1=k/(p_2p_3).
\]
Assigning \(j\) to the last factor ensures that the class on \(q_1q_2\) is \(N\bmod q_1q_2\), independent of \(q_3\). This holds even when \(h\) varies and factors overlap. It is a unit class on \(q_1q_2\), since this product divides \(k\). The theorem bounds
\[
 \sum_{q_1\le Q_1,q_2\le Q_2}
 \sup_{(b_0,q_1q_2)=1} \sum_{q_3\le Q_3}
 \sup_{\substack{(a_0,q_1q_2q_3)=1\\a_0\equiv b_0\bmod q_1q_2}}
 |\pi(X;q_1q_2q_3,a_0)-\pi(X)/\varphi(q_1q_2q_3)|
 \ll_{A,\delta} X(\log X)^{-A}.
\]
This is a sum of absolute errors for true primes, with no smoothness, squarefreeness or coefficient assumptions on the modulus slots in its statement. Take \(\delta=.00002\). For each prefix \(X\asymp x\) use dyadic upper endpoints \(Q_2,Q_3\) for the corresponding factors and let \(Q_1=X^{1/2+\delta}/(Q_2Q_3)\). There are \(O(L^2)\) packets. As \(kj\ll x^{.50001}\), one has \(q_1\le Q_1\) in every packet for large \(x\); enlarging the two other bounds costs at most 4. Their log exponents are \(u+o(1)\), \(v+\log j/L+o(1)\) for a point of \(\mathcal W\), and strictly satisfy the theorem's inequalities
\[
 .0008<\log_X Q_2<.04986,\qquad
 .10024-\log_X Q_2<\log_X Q_3<.09992-.6\log_X Q_2 .
\]
The two wedge edges give fixed slack \(.00026\) in the lower inequality and at least \(.00041\) in the upper after including \(j\). The \(Q_2\) range also has fixed slack at both ends. Thus the product and all individual bounds, not just the physical value of \(kj\), are met. Each nonempty dyadic packet has an actual point of \(\mathcal W\), so the fact that we use both independent upper endpoints costs only \(O(1/L)\) in these constraints.

A single factor tuple can come from several \(p_3\mid q_3\), hence from at most a divisor power of \(q_1q_2q_3\) different \((k,j)\). Insert that and any fixed additional divisor-power coefficient by Cauchy--Schwarz: the other factor uses the trivial error \(O(x/(kj)+1+x/\varphi(kj))\) with twice the fixed divisor weights. Its sum is \(xL^{O(1)}\), by \(\sum_{m\le x}\tau(m)^C/m\ll_C L^{O_C(1)}\) and \(m/\varphi(m)\ll\log\log(3m)\). The arbitrary-log bound on the first factor pays every weight and packet. Prefixes can be maximized after a fixed log-fine mesh of spacing \(xL^{-M}\) in \([x,3x/2]\). An interval between mesh nodes costs \(O(x/(kjL^M)+1)\) per class by counting integers and \(O(x/(\varphi(kj)L^M))\) in the main. Their weighted sums are \(O(xL^{-M+O(1)}+x^{.501})\); choose \(M\) sufficiently large. Partial summation gives the sum of \(\log p\) without any prime-power replacement. The ordinary prime number theorem to arbitrary log accuracy changes its principal on an \(e\)-interval of length \(H\) to \(kH/\varphi(kj)\). Real endpoints \(N-kv,N-ku\) for \(e\in(u,v]\) cause only \(O(L)\) per class floor errors, also covered. Consequently both \(h\) and the two moving endpoints can be maximized jointly for each \((k,j)\).

If \((N-kh,kj)>1\), the offending prime divides \(j\). In the allowed prescriptions with \(P^+(j)\le z\) the whole class is then zero for both \(a\) and \(b\), since the prime variable is at least \(x\). Otherwise the prescription must be a unit by assumption. No comparison of a reduced prime residue with a nonunit rough residue is made.

## 2. Exact rough principal and row multiplication

On the \(v\)-progression variable with \(e=h+jv\) there is exactly one forbidden residue for each prime \(p\le z\) not dividing \(kj\), and none for primes dividing \(kj\) in a unit class. Thus the rough-principal term is
\[
 \frac{H}{j V_z}\prod_{\substack{p\le z\\p\nmid kj}}(1-1/p)
 =\frac{H}{j}\prod_{\substack{p\le z\\p\mid kj}}(1-1/p)^{-1}.            \tag{3}
\]
Bracket the sieve indicator by two consecutive Bonferroni truncations with order \(\lceil K\ell\rceil\). Their expected error is at most
\((\sum_{p\le z}1/p)^{\lceil K\ell\rceil}/\lceil K\ell\rceil!\), bounded by any requested \(L^{-M}\) on choosing \(K\) sufficiently large: the prime sum is \(\le\ell+O(1)\). The floor and endpoint errors are \(z^{O(K\ell)}=x^{o(1)}\) per \(k,j\), even with \(V_z^{-1}=O(L)\) and the fixed divisor weights. Over \(k\sim Y\) and \(j\le x^{.00001}\) these cost \(x^{.50001+o(1)}\); the sum of the harmonic main errors uses \(\sum_j\tau(j)^C/j\ll L^{O_C(1)}\). Removing from \(kj/\varphi(kj)\) the primes \(>z\) perturbs the prime principal by at most \(O(L/z)\) relatively, uniformly.

The \((e,N)=1\) condition is automatic for true prime terms. If \(r\mid (e,N)\) is a prime then \(N-ke=r\) must be prime. Here \(N-ke\ge x=N/2\); the only possible \(r\mid N\) is \(r=x\). This would force \(ke=x\) prime even though \(k,e>1\). For the rough row the condition is automatic for \(r\le z\); for every \(r\mid N\), \(r>z\), at most \(O(Y/(jr)+1)\) discarded rows in the prescribed \(e\)-class occur when \(r\nmid j\). If \(r\mid j\) and \(h\equiv0\bmod r\), this is a nonunit prescription with a prime factor of \(j\) exceeding \(z\), and so was disallowed. Summing these removals over \(k,j,r\) with their weights and \(V_z^{-1}\) costs \(L^{O_F(1)}(x/z+x^{.50001})\). This proves the match of the two principals uniformly after summation.

For \(j=1\), imposing \(P^-(e)>z\) expands by the same Bonferroni bracketing into short divisibility projections \(e\equiv0\bmod j'\), \(j'\le z^{\lceil K\ell\rceil}\le x^{.00001}\) eventually. Terms with \((j',N)>1\) are absent. The actual error in this expansion costs at most \(O(L)\), a bound on \(|g|\), times the sum of the next binomial divisor count over the full \(e\)-range. Its harmonic factorial bound and \(x^{o(1)}\) floor cost give \(O_M(YL^{-M})\) per \(k\), for each prescribed \(M\). This does not presume anything about primality of \(e\).

In total
\[
 \sum_{k\in{\cal K}_N}\sum_{j\le x^{.00001}}\tau(j)^F
  \sup_{J,h}\left|\sum_{\substack{e\in J,\,(e,N)=1\\e\equiv h\bmod j}}g(N-ek)\right|
  \ll_{F,A}xL^{-A}
\]
with the same prescription rule and clipped intervals. The arbitrary opposite row costs at most \(O(Y L^{O_F(1)})\) uniformly, by \(|g|\ll L\) and the ordinary divisor moments on \(d\sim Y\). This proves (1), including choices varying with both \(d\) and \(k\). To remove \(d=e\), a crude absolute cost \(O(x^{1.00001}L^{O_F(1)})\) suffices: even if every one of the \(x^{.00001}\) chosen lifts activates the diagonal at a given \(d,k\), the divisor moments and prime log bound pay it. In the \(j=1\) case this is \(O(xL^{O(1)})\).

Both \(a\) and \(b\) separately have the complete-row principal \(H k/\varphi(k)\) for \(j=1\) with total \(k\)-absolute error \(O_A(xL^{-A})\). Their actual column sums and principals are \(O(Y L)\) uniformly. Hence the products differ from the products of the principals by \(O_A(x^{3/2}L^{-A})\), which gives (2) without relying on cancellation among its terms.

## 3. Explicit fraction, including physical geometry

For \(h_0(k)=(k/\varphi(k))^2\), write \(h_0=1*g_0\) with \(g_0\) supported on squarefree integers, \(g_0(p)=(1-1/p)^{-2}-1=O(1/p)\), and \(g_0\ge0\). On a \(k\)-interval of length \(H_K\) in the compact scale \(Y\), the full target-unit weighted count is
\[
 H_K\frac{\varphi(N)}{N}
       \prod_{p\nmid N}(1+g_0(p)/p)+O_\epsilon(x^\epsilon).             \tag{4}
\]
Expand \(g_0(r)\) and count coprimality in the free variable \(k/r\) by inclusion–exclusion, with error \(O(\tau(N))\) per \(r\). The elementary bound \(g_0(r)\ll_\epsilon r^{-1+\epsilon}\) sums those errors and pays completion of the absolutely convergent principal product. If specified distinct mark primes outside \(N\) of product \(m\) must divide \(k\), write \(k=ml\) and use \(h_0(ml)=h_0(m)\sum_{r\mid l,\,(r,m)=1}g_0(r)\). The result is (4) multiplied in its main by
\[
              \prod_{p\mid m} \frac{h_0(p)}{p(1+g_0(p)/p)},            \tag{5}
\]
with the same \(O_\epsilon(x^\epsilon)\) error for up to four marks: the completed tail starts at \(r\gg Y/m\) and is multiplied by \(Y/m\). These are counts on the physical integers, not postulated independence.

Let \(M(k)\) count the admissible ordered mark edges \(p_2,p_3\mid k\) satisfying \(\mathcal W\), with the orientation fixed by the disjoint exponent ranges \([.003,.048]\) and \([.0525,.0977]\). Define the section integrals
\[
 B_2(u)=\log\frac{.0995-.6u}{.1005-u},\qquad
 B_3(v)=\log_+\frac{\min(.048,(.0995-v)/.6)}{\max(.003,.1005-v)}
\]
on those intervals respectively, and put
\[
 \mu=\int_{.003}^{.048} B_2(u)\frac{du}{u},\qquad
 I_2=\int_{.003}^{.048} B_2(u)^2\frac{du}{u},\qquad
 I_3=\int_{.0525}^{.0977} B_3(v)^2\frac{dv}{v}.
\]
Equation (5) gives limiting first moment \(\mu\). The second factorial moment is \(\mu^2+I_2+I_3\): the two distinct edges either have four distinct labels, share just the \(p_2\) label, or share just the \(p_3\) label. These are ordered choices in \(M(M-1)\). Each harmonic product can be evaluated by fixing one label and using PNT uniformly at the resulting two endpoints in the other compact exponent interval, then ordinary partial summation for the section lengths (including the piecewise formula for \(B_3\)). Excluding label coincidences in the disjoint term and omitting all target primes and local modifications of \(1/p\) cost \(O(Lx^{-.003})\). The largest product or crude total number of four labels required in the floor errors has exponent at most \(2(.048+.0977)=.2914\). Thus the unnormalized floor error in each moment is \(O_\epsilon(x^{.292+\epsilon})\), uniformly on all the relevant \(k\)-intervals. It is \(O(x^{-1/6})\) relative to \(Y\varphi(N)/N\) when, for example, \(\epsilon=.01\). The harmonic errors have arbitrary inverse-log accuracy.

For integers \(M\ge0\), \(1_{M\ge1}\ge M-\tfrac12M(M-1)\). The uniform weighted main fraction is therefore at least
\[
 \mu-(\mu^2+I_2+I_3)/2+o(1)> .12+o(1).
\]
The accompanying exact rational checker bounds \(.197<\mu<.200\), \(I_2<.030\) and \(I_3<.080\). It uses outward rounding on 1024 equal subintervals of each axis. The section \(B_2\) is increasing, as \(.0995-.6(.1005)>0\); on a \(v\)-cell the ratio for \(B_3\) is bounded by its numerator at the left endpoint and denominator at the right. The logarithm for a ratio \(q>1\) uses eight positive terms of \(2\sum_{i\ge0}t^{2i+1}/(2i+1)\), \(t=(q-1)/(q+1)\), with remainder bounded by \(2t^{17}/(17(1-t^2))\). This gives exact directed bounds without numerical quadrature assumptions.

For the actual physical cuts and fixed nonnegative bounded-variation weights \(f_D,f_E,f_K\) on normalized indices the full modeled main is \(Y^2\sum_{(k,N)=1}B(k/Y)h_0(k)\), where
\[
 B(s)=f_K(s)\left(\int_{1/(2s)}^{1/s}f_D(v)\,dv\right)
           \left(\int_{1/(2s)}^{1/s}f_E(v)\,dv\right).
\]
The functions are extended by zero outside their compact intervals. The matched row estimates in Sections 1–2 transfer to the actual weighted columns by partial summation, giving this main restricted to \({\cal K}_N\) in every one of the four terms. The same partial summation integrates (4)–(5) against \(B\); the total cumulative floor contribution is bounded by \(O(x^{.302}(\|B\|_\infty+\operatorname{Var}B))\) before division by \(Y\varphi(N)/N\). The harmonic terms factor in every fixed interval, so the lower fraction applies whenever \(\int B>0\). No such fraction is claimed for arbitrary target-selected weights concentrated outside this \(k\)-family.

## 4. Selected anchored variance on the physical slope, and absolute mixed estimates

This result restricts \(d\), rather than \(k\), to \({\cal K}_N\). It allows the full balanced \(k\)-interval and arbitrary \(e\sim Y\), \(e\ne d\), with \((de,N)=1\). For every fixed \(F,A\), it gives
\[
 \sum_{\substack{d\in{\cal K}_N,\ e\ne d\\(de,N)=1}}
 \tau(d)^F\tau(e)^F
       |AB_{d,e}-H_{d,e}C_\infty(N;d,e)|
 \ll_{F,A}x^{3/2}L^{-A}.                                             \tag{6}
\]
Here \(I_{d,e}\) is **any** of the actual intervals of \(k\) allowed in Pham's Appendix D, varying freely with \(d,e,N\), \(H_{d,e}=|I_{d,e}|\), and
\[
 \begin{split}
 AB_{d,e}&=V_z^{-1}\sum_{k\in I_{d,e}} a(N-dk)1_{P^-(N-ek)>z},\\
 C_\infty(N;d,e)&=\prod_p\frac{1-\nu_p/p}{(1-1/p)^2},\qquad
 \nu_p=\#\{k\bmod p:(N-dk)(N-ek)\equiv0\bmod p\}.
 \end{split}
\]
The reflected assertion for \(BA\) holds with \(e\in{\cal K}_N\).

**Selected variance.** Take all \(m\le x^{.00001}\) with \((dm,N)=1\), which includes the prescribed finite Bonferroni collection eventually. For \(q=dm\) let \(\Delta_0(q,a_0)\) be the maximal discrepancy between the true prime-log count in \([x,U)\), \(x\le U\le3x/2\), in reduced class \(a_0\), and \((U-x)/\varphi(q)\). Write \(\mathcal A(d,m)\) for the selected lifts of Appendix E, i.e. the reduced classes with \(\gcd(N-a_0,dm)=d\). They all satisfy \(a_0\equiv N\bmod d\). In Section 1 replace \(k,j\) by \(d,m\); assign \(q_3=p_3m\) and \(q_2=p_2\) from the canonical wedge factors of \(d\). The base residue \(a_0\bmod q_1q_2\) is \(N\bmod q_1q_2\), no matter which lift, \(m\), or interval is later used. The theorem, including all the same factor bounds and the divisor-weighted, maximized-prefix transfer, gives
\[
 \sum_{\substack{d\in{\cal K}_N,\ m\le x^{.00001}\\(dm,N)=1}}
 \tau(dm)^C\max_{\substack{(a_0,dm)=1\\a_0\equiv N\bmod d}}
               \Delta_0(dm,a_0)\ll_{A,C}xL^{-A}.                      \tag{7}
\]
The modulus \(dm\) need not be squarefree; shared small factors of \(d,m\) do not change its value or the fixed-base condition. Reconstructions of \(d,m\) from a factor triple cost only a divisor power, as in Section 1.

The key square bound does **not** multiply (7) by the number of lifts. For every \(d,m\),
\[
 \sum_{a_0\in\mathcal A(d,m)}\Delta_0(dm,a_0)
 \le \sum_{\substack{x\le p<3x/2\\p\equiv N\bmod d}}\log p
        + \frac{\#\mathcal A(d,m)\, x}{2\varphi(dm)}
 \ll YL.                                                            \tag{8}
\]
To see this even with separately selected intervals, bound each individual maximal prime count by its entire containing macroscopic interval on its own class. These classes are disjoint inside the one class modulo \(d\). The main terms number at most \(m\), and \(xm/\varphi(dm)\ll Y\log\log x\). Thus \(\sum_{a_0}\Delta_0^2\le (\max_{a_0}\Delta_0)\sum_{a_0}\Delta_0\), so (7)–(8) prove
\[
 \sum_{d,m}\tau(dm)^C\sum_{a_0\in\mathcal A(d,m)}
           \Delta_0(dm,a_0)^2\ll_{A,C} x^{3/2}L^{-A}                    \tag{9}
\]
on the stated wedge slopes. The actual distinct \((q,a_0)\) version in Proposition E.3 is no larger. In fact its reconstruction of \(d=(N-a_0,q)\), \(m=q/d\), is exact. There is no extra subpower factor counting possible residues, no average in \(N\), and no joint maximization that changes the disjointness in (8).

**Actual passage to the mixed term.** One can now use Pham's Proposition E.3 on the restricted \(d\) side. Here is also a direct first-moment proof keeping all local factors. Expand \(1_{P^-(N-ek)>z}\) in \(AB\) by squarefree sieve divisors through order \(\lceil K\ell\rceil\). The deterministic absolute truncation error after multiplication by \(\log p\) is \(O_A(YL^{-A})\) per \(d,e\) after choosing \(K\). If \(p\mid e\) and \(p\mid m\), the forced congruence is impossible since \((e,N)=1\); otherwise each tested divisor gives exactly one class modulo \(m\). Thus the binomial-tail/floor argument of Section 2 proves this uniform error with no prime input. Multiplication by \(V_z^{-1}\) and fixed weights on both rows costs only logarithmic powers.

For retained \(m\), solve \(k\equiv k_0=N\bar e\bmod m\); the literal prime class is \(a_0=N-dk_0\bmod dm\), on the actual interval with endpoints \(N-dv,N-du\) when \(I_{d,e}=(u,v]\). Nonunit terms have zero prime mass because every prime factor of \(dm\) is \(<x\). The reduced terms are exactly \((m,eN(e-d))=1\). In every reduced term \(k_0\) is a unit at \(m\), hence \((N-a_0,dm)=d\). Endpoints and lifts may depend on \(e\); their discrepancy is bounded by twice the maximal one in (7) plus endpoint floors already covered there. Summing first over that \((d,m)\) discrepancy times \(\tau(d)^F\) and then trivially over all possible \(e\) with \(\sum_e\tau(e)^F\ll_F YL^{O_F(1)}\) gives the error in (6). This upper bound remains valid for arbitrary additional coefficients bounded by the product of the fixed divisor-power envelopes. The Bonferroni signs are not assumed well-factorable: (7) controls the **absolute** \(dm\) discrepancies.

The exact prime main before extension in \(m\) is \(H_{d,e}\, d/(V_z\varphi(dm))\) per retained coefficient \(\mu(m)\). The discarded absolute Euler tail is arbitrarily log-small by \(\sum_{p\le z}1/(p-1)\le\ell+O(1)\) and the same factorial bound. The completed principal, divided by \(H_{d,e}\), is
\[
 \frac{d}{V_z\varphi(d)}
       \prod_{\substack{p\le z\\p\nmid eN(e-d)}}
                   \left(1-\frac{\varphi(d)}{\varphi(dp)}\right).
\]
At \(p\mid d\) the inner ratio is \(1/p\); otherwise it is \(1/(p-1)\). Including the two external factors yields the stated 0-, 1-, or 2-root factor at every \(p\le z\). Indeed: \(p\mid N\) gives one coincident root; if \(p\nmid N\) and \(p\mid d,e\) then no root, if just one of \(d,e\) is zero or the two nonzero slopes are equal modulo \(p\) then one root, and otherwise two. At \(p>z\), the extra \(d/\varphi(d)\) factors and the unaccounted exceptional factors change the main relatively by \(O(L/z)\): exceptional primes divide \(Nde(d-e)\), whose log is \(O(L)\), and the generic deviation from 1 sums as \(O(1/z)\). This proves (6). The same local per-row power of \(\log\log x\) bounds \(C_\infty\) uniformly, using the finite exceptional factor product.

Finally \(BB_{d,e}=H_{d,e}C_\infty+O_A(YL^{-A})\) independently of any wedge restriction, as in Pham's Theorem D.2. Directly count the allowed residues of both forms together: at \(p\le z\) there are exactly \(\nu_p\le2\) forbidden classes, so the Bonferroni tail is bounded by \((2\sum_{p\le z}1/p)^r/r!\) for \(r\asymp K\ell\), with CRT floors \((2z)^{O(K\ell)}=x^{o(1)}\). Normalize by \(V_z^{-2}\), spend the same fixed log reserves, and complete the product. On the two-slope wedge \(d,e\in{\cal K}_N\), the **true** \(AA-AB-BA+BB\) consequently differs from \(AA-H_{d,e}C_\infty\) by weighted total absolute error \(O_{A,F}(x^{3/2}L^{-A})\). This is a reduction of the actual discrepancy, not a bound on the remaining \(AA-H_{d,e}C_\infty\).

## 5. How much of the mixed benchmark is evaluated

For a fixed nonnegative bounded-variation geometry given by weights on \(d/Y,e/Y,k/Y\) and their actual cuts (so \(H_{d,e}\) can be the weighted integral in \(k\)), the benchmark in (6) is
\(\sum_{d\ne e,(de,N)=1}H_{d,e}C_\infty(N;d,e)\) with those weights. It has the same \(>12\%\) lower fraction on the evaluated single-slope family, and \(>1.44\%\) on the family where both mixed terms are evaluated, provided the reference geometry has positive volume. We do not claim a density lower bound for arbitrary adversarial interval choices from (6).

To verify this for the **pair** singular weight, take \(w=L/1000\), \(W=\prod_{p\le w}p\). The elementary Chebyshev estimate \(\sum_{p\le w}\log p\le4w\) gives \(W\le x^{.004}\) for large \(x\). For \(d\ne e\) all large exceptional primes divide \(Nde(d-e)\); there are \(O(L/\log w)\) such primes \(>w\). The product \(C_w\) of the local factors up to \(w\) is therefore a relative approximation \(C_\infty=C_w(1+O(1/\ell))\), with the generic factors beyond \(w\) contributing \(O(1/w)\). There are no zero factors: at 2 there is one forbidden residue by the unit and even-target conditions, and at every larger prime \(\nu_p\le2\). This approximation is uniform even for the exceptional target-divisor patterns.

For each residue \(b_0\bmod W\) compatible with the target-unit condition, a row on an interval \(J\) has unweighted main
\[
 \frac{|J|}{W}\kappa,\qquad
        \kappa=\prod_{\substack{p\mid N\\p>w}}(1-1/p).
\]
The error is \(O(\tau(N))\) by inclusion–exclusion in the free progression. For any specified up to four distinct mark primes in the wedge not dividing \(N\), the main is multiplied by the reciprocal of their product, with the same floor bound: all these primes exceed \(w\). The same two factorial moments of \(M\), now **within every such residue class**, thus prove the lower wedge count \((.1239+o(1))|J|\kappa/W-O(x^{.302})\) for each interval separately. The floor exponent is as in Section 3; divided by \(Y\kappa/W\) the error saves a fixed power uniformly in the class and \(N\). The relative harmonic errors are uniform because the omitted target primes have total reciprocal weight \(O(Lx^{-.003})\). The positive bound \(0.1239\) is less than the checker output.

For completeness, integrate this classwise estimate over the actual geometry. For each fixed \(s=k/Y\), the available interval on one row is \((1/(2s),1/s]\) after its scaling and box restriction. Partial summation of the classwise moment identities against its bounded-variation weight gives the same main multiplied by its normalized interval integral; the absolute error is uniform in \(s\) and bounded by \(O(x^{.302})\) with constants depending only on the fixed weights. Take the product of the nonnegative classwise row estimates for the pair. If the main terms are \(M_D,M_E\ge0\), the product lower bound loses at most \(O(x^{.302}(M_D+M_E))\); this remains true near empty windows, using zero as a lower bound when needed. Multiply by the positive \(C_w(b_0,b_1)\) and integrate the remaining compact \(s\) variable against its weight. Relative to the full reference the error from floors is \(O(x^{.302}W/(Y\kappa))\) times a fixed geometry constant, tending to zero; the integral of the product of the two available row lengths was assumed positive. The full reference including its diagonal temporarily has size at least a fixed multiple of \(Y^3(\varphi(N)/N)^2\), since \(C_w\) is bounded below by a positive absolute constant. Its temporary diagonal costs \(O(Y^2(\log w)^2)\) by the same finite product upper bound, and hence is negligible. Restore \(C_\infty\) off the diagonal. This proves the pair-weighted fractions without assuming independence of the actual two prime forms.

## Scope

A squarefree, sufficiently smooth family could instead be handled by [Stadlmann, Theorem 1 and Corollary 2](https://arxiv.org/html/2309.00425) with coprime squarefree auxiliary factors, but the explicit wedge above has no smoothness requirement. Ordinary Bombieri–Vinogradov with a log gap below the root does not cover these balanced progressions, and Maynard I's fixed-integer-residue Corollaries 1.2–1.3 are not used with growing residue \(N\). The complete-row signed theorem does not give arbitrary \(\mu(e)\) on both rows; the two-slope mixed theorem does not evaluate the true \(AA\) term. Neither controls \(\sum_{d\ne e}|G_N(d,e)|\) in Pham's Proposition D.5. Gou–Wang–Xu's primitive conductors divide \(N\), whereas the basic physical indices in the present progressions are coprime to \(N\); no estimate on their missing primitive-character sign is inferred.
