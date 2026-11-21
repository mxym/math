# Universal cubic rank-four sign and a genuine fixed-target favorable occupation

This advances the exact cubic ledger of [OddPolynomialHalfProjection](OddPolynomialHalfProjection.md). It moves **all** reflected rank four to the favorable prime-source side, not just high reflected rank four, and proves a strict uniform lower for the actual favorable term by a marked weighted sieve. It identifies an adverse rank six and leaves the signed higher even ranks and most of the calibrated gap unresolved.

## 1. Literal revised score

Retain the variables, physical `s,q,m`, weights, central/unit masks, and `B_q,B_m,z_q,z_m` in the cubic projection, with `P(t)=t^3`. Write
\[
 R(m)=\sum_{d\mid m,\ d<\sqrt m}\mu(d)(1-2\log d/\log m)^3.
\]
The actual composite ledger from that note was \(Z_N=6J M_N+\mathcal S_c[W_s(\log m)T_q R]+o(M_N)\). For true squarefree \(m=\prod_{i=1}^k p_i\), put \(a_i=\log p_i/\log m\). Then \(R(m)\ge0\) for **every** rank 2, 3 or 4, and \(R(m)\le0\) for rank 6. Let \(H_N^*\) be the actual prime-\(q\) sum of \(W_s(\log m)R(m)\) over all reflected ranks \(2,3,4\), with the exact reflected rough guard and physical unit mask. Let \(D_{6,N}\) be minus the same actual prime-\(q\) sum over rank 6. Both terms are nonnegative. We have
\[
 Z_N=6J M_N-H_N^*+D_{6,N}+
   \mathcal S_c[W_s(\log m)T_q R\,1_{\Omega(m)\ge8\ \mathrm{even},\ P^+(m)\le B_m}]
   +o(M_N).                                                         \tag{1}
\]
For all sufficiently large even \(N\), uniformly in the target,
\[
                              H_N^*>.0033 M_N.                       \tag{2}
\]
This is a lower bound for the cubic ledger's own favorable term, not independent reserve in any prior representation. The remaining upper threshold is strictly below \((.010-5J)M_N\) for the signed terms after the explicit \(6J M_N\), unless other terms are also accounted for.

## 2. Whole signs and true prime-source transfer

Rank two has \(R=1-(1-2\min(a_1,a_2))^3\ge0\) and rank three has \(R=24a_1a_2a_3\), by the exact half identities. At even rank the full complementary representation is
\[
 R=\frac12\sum_{I\subseteq[k]}(-1)^{|I|}\left|1-2\sum_{i\in I}a_i\right|^3.
\]
Let \(U_i\) be independent uniforms on \([-1,1]\) and \(f_a\) be the density of \(\sum_i a_i U_i\). Repeated fundamental theorem of calculus for the signed differences, or convolution with the \(k\) centered uniform measures, gives
\[
 R=\begin{cases}
             96(\prod_i a_i) f_a(0),&k=4,\\
            384(\prod_i a_i) f_a''(0),&k=6.
          \end{cases}                                                \tag{3}
\]
Indeed the distributional fourth derivative of \(|t|^3\) is \(12\delta_0\), and its sixth derivative is \(12\delta_0''\). One can prove the evaluation by convolving with an even smooth approximate identity first; the uniform-box spline is continuous for \(k=4\) and twice continuously differentiable for \(k=6\). The centered uniform convolution remains symmetric and nonincreasing in the absolute value of its argument. This follows successively since convolution with a uniform on \([-a,a]\) has derivative proportional to \(f(t+a)-f(t-a)\), nonpositive for \(t\ge0\) when \(f\) is symmetric nonincreasing. Thus \(f_a(0)\ge1/2\) because its support is in \([-1,1]\), and \(f_a''(0)\le0\) when twice differentiable. This proves the advertised signs on the entire physical angular space.

Each fixed rank 2, 3, 4 or 6 transfers from \(\mathcal S_c\) with \(T_q\) to minus the actual prime-\(q\) sum just as the rank-three polynomial transfer in the odd projection. Here the half score at even ranks is a **piecewise** polynomial, not assumed separated. It is uniformly Lipschitz as a function of the fixed-rank prime logarithms normalized by \(L\), since the complete representation uses the global Lipschitz function \(|t|^3\), and \(\log m/L\ge1\). Use the same genuine-prime designation \(m=r v\): choose each actual \(r\ge x^{1/(2k)}\) with weight \((1+\#\{p\mid v:p\ge x^{1/(2k)}\})^{-1}\). Freeze \(\log r/L\) on intervals of width \(L^{-F}\), **only in the half-score test**, obtaining an independent bounded cofactor weight. Rounding changes the true expression by at most \(O_k(L^{-F})\) times a fixed divisor count, including on walls \(1-2\sum a_i=0\). The physical error, with the opened \(q\)-labels, is \(O(x L^{-F+O(1)})\) by Cauchy--Shiu on the same \(q,m=N-sq\) forms. The coprime-principal error is bounded by the same divisor moments and \(\sum_A \tau(A)^C/\phi(A)\ll L^{O(1)}\). There are log-power many intervals; their literal endpoints do not twist the prime SW slot. Apply both product BV and short fixed-cofactor ordinary prime BV branches at the previous modulus \(s\operatorname{lcm}(d_q,e_q)<x^{.4995}\) exactly as in the odd projection. The accidentally recombined repeated designated prime is on power-small square support as before. The true cutoffs and private unit masks are unchanged. After undoing the smooth/rounding weights, the same polynomial-endpoint \(\mu/\phi\) harmonic makes the all-\(q\) sum arbitrarily log-small; subtracting actual prime \(q\) proves the stated transfers.

Odd ranks above three vanish exactly. For a genuine high reflected prime \(r>B_m\), all divisors of the cofactor fall strictly below the mathematical half, and no divisor containing \(r\) does. Its full cubic moment vanishes if that cofactor has more than three distinct primes. This verifies the remaining largest-factor cutoff in (1) and places every relevant rank two, three, four or six in exactly one term.

## 3. Lower bound on actual favorable occupation

We count true source rows with an actual marked prime \(\ell\in(x^{.05},x^{.10})\) dividing \(m=\ell v\), with \(v\) squarefree, \(P^-(v)\ge x^{.105}\) and \(1\le\Omega(v)\le3\). Such \(\ell\) is **unique** on each counted row (not just a selected representative), because all other genuine primes exceed it. The actual \(q\) is prime in this whole count, not a rough replacement. Unit support requires \((\ell,N)=1\), and \(\ell\) is disjoint in size from both source primes.

Take \(u=.105\), \(w=.33\), and the level exponent \(D_0=.399\). For each \(\ell\) start from the nonnegative \(W_s(q)\)-weighted actual quotient source \(m=\ell v=N-sq\) with genuine \(s,q\). Its size parameter is \(X_\ell=\mathcal X/\phi(\ell)\), where \(\mathcal X=\sum_{s,q\prime}W_s(q)=(J+o(1))x/(2L)\) with the exact central and target-unit conditions. This follows from ordinary prime PNT on both slots; genuinely omitted prime divisors of \(N\) cost a uniform power saving by their size. The distribution in squarefree \(d\)-divisibility of \(v\) uses the actual equation \(n=sq\equiv N\pmod{\ell d}\), **including** the modulus \(\ell^2\) if \(\ell\mid d\). Apply full-scale product BV to the true \(s\) and \(q\) source up to \(x^{.499}\), since \(d\le x^{D_0}\) and \(\ell<x^{.10}\). A fixed divisor-power modulus multiplicity is enough when \(\ell\), a sieve divisor, and one penalty prime can give the same combined modulus. Use the standard weighted discrepancy interpolation and log-mesh treatment of \(W_s(q)\) from the joint projection. Errors summed over all these labels have arbitrary log reserve.

For a prime \(p\), the sieve probability on the \(v\)-source is
\[
 g_\ell(p)=\begin{cases}
              0,&p\mid N,\\
              1/p,&p=\ell,\\
              1/(p-1),&\text{otherwise}.
           \end{cases}
\]
Outside the case \(p\mid N\), this is the exact ratio \(\phi(\ell)/\phi(\ell p)\) in the reduced principal. To simplify the coprime model, \(q\) as a prime exceeds every individual modulus prime, while the omission of \(s\mid d\) is power-small after harmonic summation: at fixed source prime \(s\), summing \(1/\phi(\ell d)\) with \(s\mid d\) and a fixed divisor-power weight loses an extra \(O(L^C/s)\) factor uniformly, and \(s>x^{.10}\). If \((\ell d,N)>1\), the actual row is empty by units, as the zero factor requires. This gives the deterministic main \(X_\ell g_\ell(d)\) with summed log-small discrepancy. At a marked penalty prime \(p\ge x^u>\ell\), the moduli are \(\ell p d\) with \(d\le x^{D_0}/p\), and all sieve primes in \(d\) lie below \(x^u\) so \((p,d)=1\). The same modulus bound and exact density apply.

The dimension-one sieve product, uniformly for the needed fixed-power parameters, is
\[
 V_\ell(x^u)=\prod_{p<x^u}(1-g_\ell(p))
       =(1+o(1))\frac{e^{-\gamma}\mathfrak S(N)}{uL}.
\]
At \(p=2\) the sieve probability is zero; factoring the product against ordinary Mertens yields the binary factor 2 there. Other primes dividing \(N\) give the binary target ratios, and the tail of those target factors above \(x^u\) is uniformly \(o(1)\). The change at actual \(\ell\) from \(1/(\ell-1)\) to \(1/\ell\) is \(1+o(1)\). The required standard dimension-one inequality for partial products holds uniformly because excluding primes dividing \(N\), or decreasing the probability at \(\ell\), can only decrease the inverse product.

For \(v\) with no prime below \(x^u\) apply the Richert weight
\[
 1-\eta^{-1}\sum_{x^u\le p<x^w,\,p\mid v}(1-\log p/(wL)),
 \qquad \eta=4-.951/.33>0.
\]
It is at most 1, and when \(v\) is squarefree of rank at least 4 the penalty sum is at least \(4-\log v/(wL)\ge\eta\) for large \(x\), since \(v\le1.5x^{.95}\). This implication is **not** claimed using distinct-prime penalties on a general nonsquarefree \(v\). Instead delete the squareful rows: opening a repeated prime \(h\ge x^u\) gives \(h^2\mid v\) and at fixed \(s,\ell,h\) at most \(O(x/(s\ell h^2)+1)\) rows in the actual progression (ignore \(q\) primality only for this upper). Any conflicting \(s=h\) violates target units. The reciprocal sum saves \(x^{-u}\) and the floor term is \(O(x^{.14+.10+.475})\), since \(h\ll x^{.475}\). This is negligible at the unweighted \(M_N/L\) scale even after log weights. The remaining count with \(\Omega(v)\le3\) is at least the total Richert weighted sum plus this negligible cost. The cofactor is never 1 on these central scales.

Use the lower linear sieve for the initial term and upper linear sieve for each nonnegative penalty. For precise formulas see Matomäki--Zuniga-Alterman, [Weighted sieves with switching](https://doi.org/10.1017/S0305004125000258), Lemma 2.5 and (2.4)--(2.5), or their source Friedlander--Iwaniec (12.12)--(12.13). Use the usual sieve weights with their additive summed remainder, rather than assuming individual \(\ell\) or \((\ell,p)\) BV. All such remainder sums are covered by the label counts above. For the lower bound \(D_0/u=3.8\in[2,4]\); for the penalty the upper parameter \((D_0-t)/u\) with \(u\le t\le w\) lies in a compact subinterval of \((0,3]\). The case below 1 uses the same upper main by reducing the sifting limit to get parameter 2, as in that lemma. The lower minus upper bracket, after factoring \(2e^\gamma u\, X_\ell V_\ell(x^u)\), is
\[
 B=\frac{\log(D_0/u-1)}{D_0}
    -\frac1\eta\left[\frac{\log(w/u)}{D_0}
           +\left(\frac1{D_0}-\frac1w\right)\log\frac{D_0-u}{D_0-w}\right]
    >.69312.                                                        \tag{4}
\]
The integral in brackets is \(\int_u^w(1-t/w)/(t(D_0-t))\,dt\). Prime harmonic PNT gives it from the actual penalty prime densities; terms dividing \(N\) are harmless for this **upper**, and all local factors are uniform. The lower and upper sieve errors give \(o(\mathcal X\mathfrak S(N)/L)\) after summing the bounded \(\ell,p\) harmonics. Since \(\sum_{\ell}1/\phi(\ell)=\log 2+o(1)\) uniformly after omitting \(\ell\mid N\), the true occupancy counted with \(W_s(q)\log m\) is bounded below by \((2 B\log 2+o(1))J M_N\). The factor \(\log m/L=1+o(1)\) is uniform, and there is no duplicative \(\ell\)-count.

On this actual occupation, the mark's normalized logarithm \(a\) lies in \([.049,.101]\) for large \(x\); each other factor has normalized logarithm at least .104. In rank two the score is \(1-(1-2a)^3>.018\). In rank three the bound \(24a_1a_2a_3\ge24(.049)(.104)(.449)>.018\) holds. In rank four, (3) and \(f_a(0)\ge1/2\) give \(R\ge48\prod a_i\). For a fixed \(a\), the product of the other three is minimized when two equal the lower limit .104 and the third is \(1-a-.208\); this follows by reducing a pair with fixed sum toward an endpoint and iterating. Because \(a(1-a-.208)\) is increasing for \(a\in[.049,.101]\),
\[
 R\ge48(.049)(.104)^2(1-.049-.208)>.018.
\]
Thus (2) follows from \(.018\cdot2 B\log2\cdot J>.0033\), with a fixed strict margin. This is a uniform lower at the true cubic reference scale, not an averaged positive packet and not an estimate for \(D_{6,N}\) or the higher even tail.
