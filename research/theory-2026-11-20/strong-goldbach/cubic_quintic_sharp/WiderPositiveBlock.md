# A larger true positive rank-two/three block of the sharp cubic–quintic score

Use the identical own-log cubic–quintic \(H=V-\Pi\), uniform even target \(N\), interval \(J\Subset(0,1)\), \(L=\log N\), \(M=|J|N\mathfrak S(N)\), and true \(R_J\) of [the sharp detector](CubicQuinticSharp.md). Only actual target-unit pairs \(x+y=N,\ x\in NJ,\ (x,N)=1\) are in the scores. Nothing is transferred from a different profile.

Let \(a=.123\). Define \(\mathcal P_a\) to be the **literal** rows where each argument is squarefree of rank 2 or 3 and every actual factor exceeds \(N^a\). Let \(\mathcal A\) be the actual union where some negative arm has least factor \(>N^{.105}\), as in the [signed negative-arm proof](NegativeArmUnion.md).

**Theorem.** With the original full score on each actual row,
\[
                \sum_{\mathcal P_a}H(x)H(y)>1.2976M+o(M).
 \tag{1}
\]
The true \(\mathcal P_a\) is disjoint from \(\mathcal A\), so the same sharp identity gives
\[
 R_J\ \ge\ .804M+
       \sum_{(x,y)\notin\mathcal P_a\cup\mathcal A}H(x)H(y)
       +o(M).                                                    \tag{2}
\]
This **replaces** the earlier \(.575485M\) lower on the smaller positive-only rank-two/three block at \(.150\); no old positive block or whole rough block is added. Every adverse row still in the exterior of (2) has an actual factor \(\le N^{.105}\) on its negative arm. The signed exterior is not estimated here.

## 1. One genuine common ambient, now with both ends bounded

Let \(\mathcal B_a\) be the physical both-\(N^a\)-rough ambient with squarefree arguments and genuine target units. The two affine forms \(x,N-x\) have two distinct bad roots at \(p\nmid N\) and one root at each \(p\mid N\), including \(2\). Use the unweighted dimension-two DHR lower and upper with \(D=N^{.999}\), as in [the actual fixed-target DHR calculation](../sextic_true_tag_rebate/ExactDHRZeroTag.md). In particular this is [Diamond–Halberstam, Theorem 9.1](https://www.cambridge.org/core/books/abs/higherdimensional-sieve-method/sieve-method-for-1/5A00D3EA4C00B3B10D3CB8521D68D10C), in the explicit form of [Franze–Kao, §4](https://arxiv.org/pdf/1812.11280). Here the genuine sifting argument is \(v=.999/a\), above both certified switch points. The local normalizer is \((1+o(1))e^{-2\gamma}\mathfrak S(N)/(a^2L^2)\). The fixed-dimensional condition follows from the actual one- and two-root Euler product, with uniform upper on the ratio because missing a root at a target prime can only decrease it. The off-target quadratic factors have uniform convergent tails. The actual progression floors, with \(\lambda\)-support at level \(D\) and root errors at most \(2^{\omega(d)}\), cost \(O(DL^{O(1)})=o(M/L^2)\). On the lower, argument squares above \(N^a\) and the leftover nonunit residues for \(p\mid N,\ p>N^a\) remove \(O(N^{1-a+o(1)})+O(N^{1/2})\) rows, uniformly. The same removals can only improve the upper. Thus
\[
 (B+o(1))M/L^2\ \le\ |\mathcal B_a|\ \le\ (C+o(1))M/L^2,\quad
 B=e^{-2\gamma}f_2(v)/a^2,\quad C=e^{-2\gamma}F_2(v)/a^2.
 \tag{3}
\]

For a fixed threshold \(t\), let \(E_t\) be the squarefree rank-two/three source of floor \(N^a\) with \(H(n)/\log n>t\). The true unopposed log-weighted mass is \(m(E_t)\), using compact genuine prime product boxes. The genuine opposite rough count is at least \((k\,m(E_t)+o(1))M/L^2\), and the corresponding upper for **any** nonnegative compact source of the same total normalization is \(U\) times its ordinary mass, with
\[
 k=e^{-\gamma}f_1(.499/a)/a,\qquad U=e^{-\gamma}F_1(.499/a)/a .
\]
These are true product BV plus the linear sieve, not independence. An actual prime slot and the grouped remaining real primes give the genuine distribution at the residue \(N\); each actual divisor modulus is \(\le N^{.499}\). The local quotient densities are \(1/(p-1)\) off \(Nx\) and zero on \(Nx\). The compact real source factors have floor \(N^a\), so their omissions in the local product are \(1+o(1)\). The two directions use \(J\) and \(1-J\) of the same length. This is the marginal argument in §4 of the sharp detector, now with the full \(f_1,F_1\) delay values since \(.499/a>4\).

The ordinary rough source can include all its genuine ranks \(1\) through \(8\); rank 1 is the true prime source, with the same below-root distribution. Its ordinary normalized count is
\[
           m_{\rm all}=\sum_{r=1}^8 b_{r,a}(1),\qquad
       b_{r,a}=(1_{u>a}\,du/u)^{*r}/r! .
\]
This follows from the actual genuine prime boxes and largest-prime PNT, not a model for the two-arm pair. The count is \((m_{\rm all}+o(1))|J|N/L\). The recurrence for the reciprocal-label density is
\(t\,b_{r,a}(t)=\int_0^{t-a}b_{r-1,a}(u)\,du\) at \(r\ge2\); \(b_{1,a}(t)=1_{t>a}/t\). It follows by splitting the total angle among the \(r\) labels in the convolution. The checker uses positive integer-tick upper rectangles, whose slightly extended final interval gives a conservative upper \(m_{\rm all}<4.566568\). This includes **all** rough ranks and both positive and negative scores before testing membership of \(E_t\).

## 2. Both signs of the occupancy estimate

For an actual ordered pair of thresholds \(t,s\), supply whole-cell lower ordinary masses \(\underline m_t,\underline m_s\) on \(E_t,E_s\). Their actual marginal lower estimates and the single common upper ambient in (3) give the intersection lower \(k(\underline m_t+\underline m_s)-C\) in normalized count units \(M/L^2\).

There is also a different true lower on the **same intersection**, using the lower ambient in (3). On each source arm the entire unwanted rough set has ordinary mass \(m_{\rm all}-m(E_t)\), and its actual rough-opponent count is at most \(U\) times that mass. This includes actual primes and every unwanted rank or sign. For the source bound one may approximate known angular cuts by compact product boxes first: the divisors and squarefree masks are literal, the score is a continuous angular function at fixed rank, and at every fixed threshold \(t>0\) used below the amplitude wall has zero angular measure (the finite rank-two polynomial is nonconstant, and the exact rank-three polynomial is nonconstant). Thus subtracting the two **upper** unwanted marginals from the common lower ambient gives \(B-U(2m_{\rm all}-\underline m_t-\underline m_s)\). These are real two-sided count inequalities. They use no positive copy of \(R_J\) on the right, no separate prime-pair subtraction credit, and no independence of actual ranks. We use the largest of zero and these two valid lower bounds, not their sum.

## 3. Outward angular layers and the precise replacement

At this true floor all rank-two and rank-three scores are positive. Rank two is \(1-F(u)\) in normalized own-log angles; rank three is \(16\prod u_i(3-5\sum u_i^2)\) by the exact global formula. Its sum of squares is at most \((1-2a)^2+2a^2=.598774<.6\). The rank-three amplitude is \(<1\), as in the sharp proof; rank two is at most \(1\). The target-log floor and own-log floor differ by \(O_J(1/L)\), with the same true finite-rank angular collars as there. This never changes the sign, by the strict upper on the sum of squares.

Use the \(200\) true amplitude layers \(t_j=j/200\). At mesh \(1/1000\) the code takes only actual interior ordered rank-2/3 boxes with lower score **strictly** above \(t_j\); each angular coordinate denominator is upper-rounded. For rank three the score is \(1-\sum_i P(1-2u_i)\), with \(P(z)=2z^3-z^5\) increasing on \([-1,1]\), so use the lowest allowed endpoint for each angle. For the dependent last angle this is \(1-u_{1,+}-u_{2,+}\). All score lower bounds are genuine over each whole box. Actual boundary removal and positive rough upper on compact collars justify using these strict layers at the physical \(NJ\) and its reflection. The ordered coordinate integral has no extra factorial because physical unordered factorization has already been ordered.

At an actual positive pair the sum of included layer-weights in each coordinate is bounded above by its true normalized amplitude. Therefore the normalized positive paired weight is at least the \(200^{-2}\) times sum over \(j,\ell\) of the actual intersection lower in §2. The attached exact rational checker propagates outward DHR ticks from the established switch enclosures \(5.3577<\alpha_2<5.3578,\ 4.2664<\beta_2<4.2665\). It computes the Dickman-2 denominator \(\mathcal G\) and the \(A(v)=v^2e^{-2\gamma}F_2(v),\,B(v)=v^2e^{-2\gamma}f_2(v)\) delay enclosures exactly as in the linked DHR proof, now both branches needed. Through the \(\alpha_2\) switch upper-bound \(A(\alpha_+)\) by \(\alpha_+^2/\mathcal G(\alpha_-/2)\), and through the uncertain \(\beta_2\) cell bound the lower increment by zero and the upper by its full positive derivative. For the linear delay \(A_1(v)=ve^{-\gamma}F_1(v),\,B_1(v)=ve^{-\gamma}f_1(v)\), use \(A_1=2\) up to 3, \(B_1=0\) up to 2, and the respective delays \(A_1'=B_1(v-1)/(v-1)\), \(B_1'=A_1(v-1)/(v-1)\) on the remaining inputs. Every delay numerator is rounded by its two monotone endpoint values; its positive denominator by the opposite endpoint. The physical ratios are rounded downward so they enclose the increasing lower sieve functions from below and decreasing upper functions from above.

The values are \(B>20.7916331\), \(C<20.881873\), \(k>4.4784588\), \(U<4.651445\), and the combined genuine layer lower is \(1.29767616131\ldots\). The checker also reports the valid \(1.25011511621\ldots\) from the first intersection inequality alone. Neither number is a product of independent ordinary masses. Both orientations of actual ordered \(x,y\) are already included in the single common ambient argument; there is no second factor of two.

Use only the enlarged actual \(\mathcal P_a\) lower (1) and the previously proven complete \(-.493039M\) lower on \(\mathcal A\). Their literal signs exclude any overlap, and \(1.2976-.493039>.804\). All other rows are kept with their original signed scores in (2); no previous positive block or whole rough block is reused. This is not a lower on the full signed score or a proof of a prime pair.

Run:

    python3 -OB check_wider_positive.py
