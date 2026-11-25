# A sparse prime-supported obstruction at the square-root modulus scale

This note tests the **numerical bounds**, not Dirichlet GRH itself. We construct one nonnegative weight supported on actual primes which obeys the linear character/Fourier bounds and centered short-frequency mean-square bounds used in the [square-root modulus reduction](DirectGoldbachGRHSquareRootModulusReduction.md). At an explicit sequence of dyadic targets the model has no prime-pair weight in the prescribed windows, even though it preserves all local off-target pair counts to near-square-root accuracy. The model is not the actual logarithmic prime weight, is not asserted to have its Euler products, and does not refute Goldbach.

## Sparse construction and linear discrepancy

Write \(w_0(p)=\log p\) on primes and zero elsewhere. Put \(N_j=8^j\), ignoring finitely many small \(j\), and \(J_j=[N_j/4,3N_j/4]\). In each \(J_j\) take only unordered genuine prime pairs \(\{p,N_j-p\}\). These are disjoint edges of a matching, with no prime midpoint. The shells are disjoint. For each edge independently put \(2w_0\) on one randomly chosen endpoint and zero on the other; leave \(w_0\) on every other prime. Call the result \(v\). Thus every product drawn from a target edge is identically zero. All fixed interior windows used here are supported in \(J_j/N_j\).

The usual [two-root Selberg upper sieve](https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/) bounds the number of edges by \(O(N_j/\log^2 N_j)\), since the Goldbach singular series is constant on powers of two. Accordingly the sum of squared signed coefficients on a shell is \(O(N_j)\). The same is \(O(X)\) over all affected primes up to \(2X\), because the shell scales form a geometric sequence and a shell intersecting \([1,2X]\) has \(N_j\le 8X\).

Fix any \(A>0\). For one interval of integers in \([1,2X]\), one Dirichlet character of modulus \(d\le X^A\), and one additive frequency, the real and imaginary parts of \(\sum (v-w_0)(p)\chi(p)e(\beta p)\) are sums of independent signed real coefficients of total square \(O(X)\). An edge with both endpoints present contributes a single coefficient, bounded in modulus by the sum of the endpoint logs. Hoeffding gives failure probability at most \(4\exp(-ct^2/X)\). There are polynomially many intervals, characters and grid frequencies with spacing at most \(X^{-4}\); between grid frequencies the derivative is \(O(X^2\log X)\), even trivially. Taking \(t=C_A\sqrt{X\log X}\), the probability of failure on dyadic scales is summable,. One realization therefore satisfies, for all large \(X\), uniformly over the stated tests,
\[
 \left|\sum_{p\in I}(v-w_0)(p)\chi(p)e(\beta p)\right|
 \ll_A \sqrt{X\log X}.
\]
One can require this for every fixed \(A\) with its own constant by taking the countable intersection of probability-one events. Bounded-variation smooth weight insertion follows by partial summation. For exponential smooth cutoffs at scale \(X\), the contribution from \(p\le X^{.49}\) is trivially \(o(\sqrt X)\), and on all larger dyadic pieces one may use a larger fixed character exponent (for example \(3A+1\)) and sum the partial-summation bounds with their exponential decay. At a target the ordinary prime weight square mass is changed by only \(O(N_j)\) on \(J_j\), because only \(O(N_j/\log^2 N_j)\) positions change by \(O(\log N_j)\).

## Every other local pair sum at once

At \(N=N_j\), take the two fixed smooth, bounded test functions \(w,g\) of the square-root reduction and write
\[
 R_u(M)=\sum_{p+p'=M}u(p)u(p')w(p/N)g(p'/N).
\]
For \(M\ne N\), distinct primes contributing to this sum either use independent signs or have at most one random endpoint. Their expectation is unchanged. The only possible diagonal \(p=p'\) changes the expectation by \(O(\log^2 N)\), and is absent for disjoint windows. In contrast \(R_v(N)=0\) identically.

Flipping one edge sign changes at most four ordered products at any fixed \(M\), each by \(O_{w,g}(\log^2 N)\). The bounded-differences inequality with \(O(N/\log^2 N)\) independent signs gives failure probability \(\le 2\exp(-ct^2/(N\log^2 N))\) at deviation \(t\) from the mean. There are only \(O(N)\) relevant integers \(M\); summing failure probabilities over these and \(j\) shows the same global realization can be taken to satisfy
\[
 \sup_{M\ne N_j}|R_v(M)-R_{w_0}(M)|\ll_{w,g} \sqrt{N_j}(\log N_j)^{3/2}.
\]
The same argument works for the weighted differences \(p-p'=h\ne0\), with the same or two bounded tests supported in the shell. The only biased distinct ordered pair can be \(p=(N+h)/2,\ p'=(N-h)/2\), contributing an expectation change \(O(\log^2 N)\). The mean at \(h=0\) is not claimed to be unchanged, but its change is \(O(N)\). The argument tolerates polynomially many predetermined bounded test pairs with common bounded sup norms, by increasing the constant in the union bound.

## The numerical inputs to the reduction are still valid

Work under Dirichlet GRH for the **actual primes**, so that the character estimates invoked by the reduction hold for \(w_0\). For \(v\) with exactly the same pole subtractions, the character prefix changes by \(O_A(\sqrt{X\log X})\), including the principal character. Orthogonality transfers this to a single reduced residue with no factor equal to the number of characters. For the short-frequency estimate, if \(E_{u,a}(\beta)\) is the pole-centered error in a reduced residue \(a\bmod d\) and \(P_\chi(\beta)\) is the smoothed character perturbation, then
\[
 \sum_a\int_{|\beta|\le b}|E_{v,a}(\beta)-E_{w_0,a}(\beta)|^2d\beta
 =\frac1{\varphi(d)}\sum_{\chi\bmod d}\int_{|\beta|\le b}|P_\chi(\beta)|^2d\beta
 \ll_A Xb\log X.
\]
There is no loss proportional to \(d\), and this perturbation bound holds at every width. Thus the corrected short-frequency rail used on actual weights is retained in full. The prefix and Parseval consequences used for the mixed terms and \(|H_d|\) are retained. Local unit identities, the exact delta identity and its main-term coefficients are unchanged: they only require support on the relevant units, and repeat the same pole. Upper sieve domination survives since \(0\le v\le2w_0\). The already established estimate for the switched aliases uses the above numerical bounds, not any explicit formula applied anew to \(v\). Choosing the fixed logarithmic losses in the reduction large enough as before gives, at \(X=N_j\),
\[
 \sum_{T/L^B<q<2T}(1-\chi(q/T))D^{(v)}_q
 =-(1-\kappa)X\mathfrak S(N_j)I(0)+o(XT/Q).
\]
Here \(\chi\) denotes the smooth cutoff, not a Dirichlet character. Since \(1-\kappa\asymp T/Q\) and \(I(0)>0\), the signed band can spend the **whole** positive budget in a model obeying those bounds.

This distinguishes the outstanding problem from improving the calculation of an individual shifted sum or reusing the existing GRH-size rails. It rules out any positivity deduction using only inputs shared by this model; it says nothing about a stronger estimate encoding the actual arithmetic of the prime weight.

## Aggregate stability of the actual nonzero offsets

One can also compare the two weights directly below the reduced budget, without applying GRH anew. Consider any bounded deterministic weights \(W_q\) on the constant-kernel moduli \(2Y<q\le Q\) of the root-scale reduction. There the divisor switch for \(u=w_0,v\) gives factor \(c_Q/Q\) and terms \(W_{md}\mu(m)C_{md/Q}H_d^{(u)}/m\). In \(H_d^{(u)}\) the prime-pair term is \(\sum_k R_u(N+kd)\). By the uniform estimate above the **entire nonzero-offset difference**, after summing over \(m,d\), is
\[
 \ll \frac{X^{3/2}L^{3/2}}{Q}\sum_{md\le Q}\frac1{md}
 \ll \frac{X^{3/2}L^{7/2}}{Q}.
\]
This uses \(O(X/d)\) nonzero offsets from the compact physical support and the bound for the divisor harmonic sum. The mixed terms in \(H_d\) have difference
\(O(X\varphi(d)^{-1}\tau(d)\sqrt{XL})\) by opening the unit constraint on the reflected prime and applying the linear discrepancy for each resulting progression. Their aggregate difference is \(O(X^{3/2}L^{9/2}/Q)\) using \(d/\varphi(d)\ll L\), \(\sum_{d\le Q}\tau(d)/d\ll L^2\), and \(\sum_{m\le Q}1/m\ll L\). The pure lattice term is unchanged. The exact zero-offset coefficient is obtained from \(\sum_{m\mid q}\mu(m)/m=\varphi(q)/q\). Thus the full signed change equals
\[
 -R_{w_0}(N)\frac{c_Q}{Q}\sum_q W_q C_{q/Q}\frac{\varphi(q)}q
 +O(XL^{-K+9/2}),
\]
uniformly in \(|W_q|\le1\). The remainder is \(o(XT/Q)\) for sufficiently large fixed \(K\). For the root-scale reduction one can take \(B\) a fixed constant first, then \(K\) large enough that \(T/L^B>2Y\); in particular this direct comparison applies to the whole remaining band. The \(R_{w_0}(N)\) factor is not determined by the comparison.
