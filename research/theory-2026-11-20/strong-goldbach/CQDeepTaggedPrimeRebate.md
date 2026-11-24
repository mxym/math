# Actual deep two-tag prime rebates and one common signed exterior ledger

Keep pinned 989aea5 canonical sharp \(H=V_{\rm raw}-\Pi\), one fixed even \(N\), \(x+y=N,\ (x,N)=1,\ x/N\in J\Subset(1/3,2/3)\), \(M=|J|N\mathfrak S(N)\), \(L=\log N\), and \(R_J=\langle H,H\rangle+o(M)\). All prime crossings are on this same actual target in each orientation; no no-pair hypothesis is assumed. This extends [the pinned MiddlePrimeRebate](cubic_quintic_sharp/MiddlePrimeRebate.md) to disjoint deeper labels using a factored rank-four signed amplitude.

## Deep true tags and genuine prime lower

Set \(\beta=1/5000=.0002\). Form half-open true first-label cells \((N^{t_0},N^{t_1}]\) by partitioning \((\beta,.040]\) on mesh .001 (first cell \((.0002,.001]\)), and second-label cells \((N^{v_0},N^{v_1}]\) within \((.005,.170]\) on the .001 mesh, with \(t_1\le v_0\). Put
\[
 X_0=1-t_1-v_1,\ X_1=1-t_0-v_0,\quad
 B=.499+v_0/2,\ E=B-t_1-v_1,\ z=\max(X_1/5,v_1)+.0001 .
\]
Retain cells with \(2z<E<4z\) and the strictly positive amplitude test below. For each actual squarefree argument in a retained cell the *literal quotient* by \(pq\) must be \(N^z\)-rough. Because \(z>v_1\) the named real primes \(p,q\) are automatically its exact two least labels. Since \(5z>X_1\) the quotient has one to four genuine factors, so the accepted source has actual ranks 3 through 6. Let \(C=-H\) on this true union and zero elsewhere. Its support has \(\beta<\log P^-/L\le .040\); its negative sign is established below.

The analytic proof of MiddlePrimeRebate §1 applies to the real opposite prime, including the actual \(pqd\) progression and modified well-factorable lower weights. For HB moderate \(Y\) set \(A_0=Y N^{-10^{-6}}, P_+=N^{t_1},D=N^E\). When \(A_0\ge P_+\), split the two-way weights at \(A_0/P_+\), \(DP_+/A_0\), putting variables in \((pd_1,q,d_3)\); otherwise use the split \(A_0,D/A_0\) with slots \((d_1,q,pd_3)\). Actual \(p,q\) are independently boxed, and the tagged \(q\) slot keeps exponent \(v_0\ge.005\). \(DP_+=N^{B-v_1}>N^{.4}>Y\), and \(D>P_+\) by \(E>2z>.316\) and \(t_1\le.04\). The strict exponent rails of Lichtman Proposition 5.2 used in the pinned proof remain
\[
2\,10^{-6}+2B-v_1<.999,\quad
2B+3v_1+\tfrac7{32}+10^{-6}<1.9,\quad
2B+3v_1+\tfrac7{16}(B-v_0-v_1)+(1+\tfrac7{16})10^{-6}<1.935.
\]
These depend on \(v_0,v_1=v_0+.001\le.170\), not on the now smaller \(t_0\). The original one-/two-long HB cases still have \(B\le.584\). Repeated labels or sieve factors force a genuine square of a prime \(>N^\beta\); their total is \(O(N^{1-\beta+o(1)}+N^{.170+o(1)})\) with fixed divisor-power weights, and the reciprocal model error is power-small too. The target-unit masks, omitted reciprocals of primes dividing \(N\), and local singular coefficient work exactly as in the pinned proof, now with the fixed power \(\beta\). Thus each cell has actual opposite prime log-weighted count at least
\[
 \frac ML\left[\frac{2\log(E/z-1)}E\log(t_1/t_0)\log(v_1/v_0)+o(1)\right].
\]
There is no numerical lower at a growing/sinking label floor and no per-fixed-\((p,q)\) equidistribution claim.

## Rank-four equalization compares every possible remaining pair

Fix the true first widths \(0<t\le v\), and let the other two widths have sum \(X=1-t-v\). The canonical exact score identity is
\[
 h_4/\prod u_i=96 b_4(0)-1920\,\mathbb E|W|.
\]
Here \(b_4,W\) are the analytic density and the sum of centered intervals of the given widths. Four distributional derivatives give \(F^{(4)}=96\delta_{1/2}-3840(1/2-u)_+\), and centering turns the latter expectation into \(\mathbb E|W|/2\).

For free widths \(a\ge b,\ a+b=X\), the two-interval sum density on the positive half is \(1/a\) on \(0\le x\le(a-b)/2\), followed by \((X/2-x)/(ab)\) until \(X/2\). The equal pair density is \(4(X/2-x)/X^2\). Equal minus unequal starts nonnegative and is decreasing on the first piece, then nonpositive on the second by \(ab\le X^2/4\). Both densities are even and integrate to 1, so the equal pair puts more mass in *every* centered interval. Convolution with the two fixed centered interval densities preserves this order: the conditional chance that a translate lands in a centered interval is an even function decreasing in the absolute translate; integrate its centered-interval layers. Therefore the equalized four-sum has \(b_4(0)\) no smaller (shrinking centered intervals), and \(\mathbb E|W|\) no larger (integrating nonnegative tails). Hence the normalized \(h_4/\prod u_i\) is maximized by equal free widths. No arithmetic factor-angle distribution is assumed.

With \(\psi(u)=2(1-2u)^3-(1-2u)^5\) and \(P(x)=2x^3-x^5\), the equalized folded score is \(F_4(t,v)=1-\psi(t)-\psi(v)+\psi(t+v)-2P(t+v)+2P(v-t)\). Factoring *before* interval rounding gives
\[
 F_4(t,v)/(tv)=-32+192t+168v-320v^2-480tv-320t^2
 +180v^3+320tv^2+360t^2v+160t^3-\frac{4t^2(2-t^2)}v .
\]
Round each positive monomial at its upper endpoints, each negative monomial at lower endpoints, and the last term at \(t_0,v_1\) using the monotonicity of \(t^2(2-t^2)\). If this upper \(P_4^+\) is negative, \(F_4\le U_4=t_0v_0P_4^+<0\). Transfer from the equal-score normalization back to an actual unequal pair with both widths \(\ge z\): its product is at least \(z(X-z)\ge z(X_0-z)\), whereas the equal product is \(X^2/4\le X_1^2/4\). Thus the actual negative lower is \(K_4=(-U_4)4z(X_0-z)/X_1^2\). This is not restricted to central shapes.

The other actual amplitude lowers are
\[
 K_3=16t_0v_0X_0[5(t_0^2+v_0^2+X_0^2)-3],\quad
 K_5=1920t_0v_0 z^2(X_0-2z),\quad
 K_6=5760t_0v_0 z^3(X_0-3z).
\]
In rank six the four quotient widths are each \(\ge z>X_1/5\), so their maximum is \(<.4X_1\le.4\), and the true tags are smaller. The density–variance bound of the balanced-rank-six note gives \(b_6(0)\ge1/\sqrt{\sum u_i^2}\ge1/\sqrt{\max u_i}>3/2\), and \(b_6''(0)\le0\); this gives the coefficient 5760. The other product bounds put all slack above \(z\) in one quotient width. Use the strict cell test \(K=\min K_i>0\); thus all accepted scores are actually negative. Fixed genuine target-angle vs own-log collars have the usual \(O_J(1/L)\) change and rank conditions \(z>v_1,5z>X_1\) are strict.

Insert \(K\) or \(K^2\) on exactly those actual prime crossings, without multiple use of a label pair; each accepted composite has just one pair of actual two least primes. The squared conversion uses the uniform \(\log n/L=1+O_J(1/L)\). The directed BigInt runner uses 14 positive atanh terms per log and \(10^{-15}\) downward ticks separately for the two sums. The 5970 retained cells give, **in each orientation**,
\[
 \langle C,\Pi\rangle\ge .092609478893615\,M+o(M),\qquad
 \langle C^2/L,\Pi\rangle\ge .001281239179835\,M+o(M).
\]
These are joint true rank-3–6 bounds. The rank furnishing the cell minimum need not be the actual realized rank. There is no rank-six-only rebate.

## One unified true two-label receiver for C

On every actual accepted cell \(0\le C/\log n\le100\,tv\) for the genuine two least own angles \(t,v\). In rank three the exact formula with \(\sum u_i^2\le1\) gives cap \(32tv\); rank five gives \(1920tv(X/3)^3<72tv\) by AM–GM. In rank four take integral differences on the two distinguished smallest widths; they leave \(F''\) and the two remaining signed shifts. The explicit polynomial is \(F''=48x-80x^3\) for \(x=1-2u\in[0,1]\), hence \(F''\in[-32,15]\), and \(F''=0\) at or above \(u=1/2\). The term shifted by both other widths vanishes because \(X=1-t-v>.79\); thus the possible negative amplitude is \((32+2\cdot15)tv=62tv\). In rank six use the cube-slice bound \(b_6(0)\le\sqrt{12}\), plus \(|b_6''(0)|\le2\|b_4\|_\infty/(u_5u_6)\) by differentiating the two longest widths. The surviving four-density is a probability convolution with a uniform of width \(u_4\), so \(\|b_4\|_\infty\le1/u_4\). After inserting the true product, the derivative term costs \(\le192tvu_3\le48tvX\), since \(u_3\) is the smallest of the four remaining widths. The other term is at most \(3840\sqrt{12}\,tv(X/4)^4\); their sum is \(<100tv\) by \(\sqrt{12}<3.465\).

For any nonnegative genuine compact opposite source \(D\) open the two genuine tags on the \(C\) receiver. With \(\lambda=.499-t_1-v_1>0\), upper-sieve the quotient to physical cutoff \(N^{\lambda/3}\) at physical level \(N^\lambda\), ratio 3. This cutoff is below \(N^z\), as \((.499-t_1-v_1)/3<(1-t_0-v_0)/5\le z\), so every actual selected quotient survives. The conditional coefficient is \(2/\lambda\), with the same true local unit factors as earlier opened receivers. This time use ordinary compact product BV on the **genuine opposite source** of length \(\asymp N\) at each literal combined modulus \(pqd\le N^{.499}\), with grouped divisor multiplicities. There is no over-root input here and no use of a length-\(N\) theorem on a length-\(N/pq\) quotient sequence. The pointwise amplitude \(100tv\) cancels both genuine reciprocal label angles in Mertens summation; using own-log angles changes this bounded compact amplitude by relative \(1+o(1)\). For actually retained half-open cells the denominators may use their upper endpoints while keeping the actual \(tv\) in the harmonic sum. Thus for either orientation,
\[
 \langle D,C\rangle,\langle C,D\rangle\le U_C m(D)M+o(M),
 \qquad U_C=\sum_{\rm retained}\frac{200(t_1-t_0)(v_1-v_0)}{.499-t_1-v_1}
            <3.14046.
\]
The exact sum is \(3.140454036489198\ldots\). The compact-source hypotheses include \(C\), the residual middle negative weight, the older negative sources, and artificial fixed-floor truncations of the old \(|V_{\rm tiny}|\). No generic \(\beta\)-rough multiplier is needed for these \(C\) overlaps.

## Joint exact scope with the earlier middle band

Let \(B_0\) be the genuine middle negative magnitude with true least angle in \((.040,.105]\), after removing the one-arm supports of previously paid \(W,Z,G\): the high-rank/long rank-eight source \(W\), the extra rank-eight angular source \(Z\), and the rank-six plateau \(G\) with largest own angle at least .54. Every original accepted MiddlePrimeRebate cell (linear and squared) is physically inside \(B_0\). Its only actual ranks are 3–6, so none can be in \(W,Z\); in rank six the four quotient widths each \(\ge z>X_1/5\) force largest \(<.4\), excluding \(G\). Thus no earlier exact middle rebate is lost when deleting those one-arm shapes.

Write \(Y=B_0+C\). The two true one-arm supports are disjoint, so \(Y^2/L=B_0^2/L+C^2/L\) exactly. The verified genuine residual-middle linear constant .033390005752037 and squared constant .001027859535234 add to their disjoint deep counterparts, giving each orientation
\[
 \langle Y,\Pi\rangle\ge .125999484645652\,M+o(M),\qquad
 \langle Y^2/L,\Pi\rangle\ge .002309098715069\,M+o(M).
\]
The squared figure constrains a different true moment and is **not** also credited in the linear signed transfer.

Let \(\mathcal Y\) be the literal pair union with at least one \(Y\) arm, \(\Gamma_-=A+W+Z+G\) the old negative sources (\(A\) is floor .105), and \(T=H1_{P^-\le N^\beta}\) the original signed tiny arm. The older one-arm types and \(Y\) are mutually disjoint; all prior positive supports are excluded by actual signs. Their **pair unions can and do intersect in principle**. The exact contribution of \(\mathcal Y\) after excluding older paid rows is
\[
 \Delta_Y=-\langle Y,H\rangle-\langle H,Y\rangle-\langle Y,Y\rangle
 -\langle Y,\Gamma_-\rangle-\langle\Gamma_-,Y\rangle
 +\langle Y,T\rangle+\langle T,Y\rangle.
\]
The older negative crossings are positive products, the tiny intersection instead equals \(-\langle Y,T\rangle-\langle T,Y\rangle\). Every such intersection involves opposite arms of distinct literal types; no triple intersection of the new union with two older types is possible. Prime rows do not belong to any of these real old intersections, and the rebate is used in the transfer identity (not added as fictitious \(H\times H\) on a prime).

For a single common bound define \(c=m(C), b_0=m(B_0),q_0=m(B_0^2/L)\), \(\mathcal J=9.072193375\) the actual band bound for \((.04,.105]\), and \(U_h=4.651445(.123/.105)\) the old .105 upper. Write \(q_{\rm old}=m((W+Z+G)^2/L)<.001669\), since the three supports are disjoint and their genuine squared upper masses respectively .001459,.000196,.000014. The last follows from the plateau cap \(3840(.46/5)^5\) times \(m(G)<.000546\). Use the earlier actual tiny coefficients \(\alpha_T=.0063885+.0111568,\ B_X<.0033960,\ B_V<.1044\). On the same physical target the three current overlap bounds, each with \(o(1)\) after division by \(M\), are
\[
 \begin{aligned}
 \langle Y,Y\rangle/M
   &\le \mathcal J q_0+ U_C c+2U_C b_0,\\
 [\langle Y,\Gamma_-\rangle+\langle\Gamma_-,Y\rangle]/M
   &\le 2U_C m(\Gamma_-)+2(1.2)U_h b_0+
                               2\mathcal J\sqrt{q_0 q_{\rm old}},\\
 -[\langle Y,T\rangle+\langle T,Y\rangle]/M
   &\le 2\alpha_T(b_0+c)+2U_C B_V
                  +2B_X\sqrt{\mathcal J\cdot3390\,q_0}.
 \end{aligned}
\]
First expand the actual \(Y,Y\) into four products; use the true \(U_C\) receiver on \(C,C\) and the two distinct \(B_0,C\) orientations, and true band AM–GM on \(B_0,B_0\). Second, against \(C\) use the sum of the actual older negative sources as one nonnegative \(U_C\) source, not separate intersections of the same pair; for \(B_0,A\) use \(A\le1.2L1_{>.105}\), and against \(W+Z+G\), both weights in \((.04,.105]\), apply the same-band true Cauchy upper as in the prior paid overlap. Finally insert the old actual tiny decomposition \(T=C_{\rm stop}+E+V_{\rm tiny}-D_{\rm tiny}\), with its signed stop, zero \(E\) transfer and genuine defect bounds against the whole \(Y\le|H|\). For \(|V_{\rm tiny}|\) on the opposite arm, use \(U_C\) against the genuine fixed-floor compact truncations, with the old ordinary bound on their absolute masses before taking the original signed tiny limit. For \(B_0\) use the earlier real band-squared Cauchy, \(X\) channel versus true \((.04,.105]\), \(LY\) certificate channel versus \(B_0^2/L\); the coefficient is exactly \(.678/\beta=3390\). This splits only the two disjoint types of the \(Y\) arm in the one tiny pair intersection.

The genuine compact transfer against \(Y\le|H|\) therefore yields in the **same** canonical signed ledger
\[
 \Delta_Y/M\ \ge -4(b_0+c)+.251998969291304
     -\bigl[\text{the three actual upper budgets in the last display}\bigr]+o(1).
\]
The compensation comes from the linear moment once; do not add the squared moment or charge the previous reserve separately for the different displayed upper bounds. This is a genuine fixed-target signed constraint but not a positive lower on the entire incremental union, nor payment of the balanced rank-six chamber. The current upper overlap constants alone are too large for that.

Run the [exact replay](check_cq_deep_tag_prime_rebate.js) with Node.js. It checks the accepted cell count, the two true deep lower moments and the unified upper receiver, plus the exact addition to the already certified residual-middle moments; it checks arithmetic, not the cited distribution theorem.