# Same-target middle-overlap bound using both true prime directions

All sums on actual x+y=N, x∈NJ, (x,N)=1 with fixed central J, L=log N and M=|J|N𝔖(N). Use the literal sharp CQ H and Π actual prime logarithmic weight at pinned main 989aea5. Let
\[
 B(n)=[-H(n)]_+1_{\{N^{.040}<P^-(n)\le N^{.105}\}},\quad B_2(n)=B(n)^2/L,
 \quad R_a(n)=1_{\{P^-(n)>N^{.040}\}}.
\]
B₂ nonnegative; write b=m(B), b₂=m(B₂) for ordinary score masses in the usual |J|N units (fix actual floor). This closes an explicit inequality for the **same middle signed union** used in [MiddlePrimeRebate](cubic_quintic_sharp/MiddlePrimeRebate.md), not the whole CQ exterior.

## Actual overlap must miss the true prime receivers in both orientations

Pointwise on every physical pair,
\[
 B(x)B(y) \le \tfrac12\left[B_2(x)(L R_a(y)-\Pi(y))+(L R_a(x)-\Pi(x))B_2(y)\right].
\]
If both B are positive, both y/x rough and composite, and this is AM–GM for two actual nonnegative amplitudes. Otherwise LHS zero and both RHS summands are nonnegative, since every central prime is rough and its log≤L. Crucially this upper subtracts each true prime receiver from the available squared-score budget in its own orientation. No prime rows or marginal signs are being used as composite-pair contributions.

B₂ is a legitimate nonnegative fixed-rank compact **genuine squarefree angular source** for the pinned rough-opposite upper sieve. Indeed B vanishes unless squarefree; least factor >N^.040 forces rank≤24 (rank 25 with strict > would exceed N); normalized amplitude on each fixed rank is the square of the negative part of the true CQ angular polynomial/piecewise polynomial, sign cut continuous in its magnitude and the genuine floor cuts Jordan boundaries. Angles ≥.040 on the central interval; log n/L=1+O_J(1/L) converts B²/L to log n times the squared angular amplitude at negligible error for such bounded compact sources. Ordinary angular masses of B₂ agree in the reflected intervals. Do not apply this to H² over arbitrary ranks or to the noncompact tiny sector. Use the genuine compact product BV/linear rough upper (WiderPositiveBlock §1, with positive polynomial floors; no requirement of Z≤|H| for this marginal upper), with D=N^( .499·.040/.123 )<N^.5 for the .040 gate. This fixes s=.499/.123, the already checked upper sieve ratio, and gives
\[
 \langle B_2,L R_a\rangle,\ \langle L R_a,B_2\rangle
 \le U_{.04} b_2 M+o(M),\qquad
 U_{.04}<4.651445\cdot .123/.040=14.303193375 .
\]
The actual sieve moduli now have strict exponent about .1623; no new distribution level. Positive score normalization means this is an upper with sign as written. Thus for the same N,
\[
 \langle B,B\rangle\le U_{.04}b_2M-\tfrac12(\langle B_2,\Pi\rangle+\langle\Pi,B_2\rangle)+o(M).
\]

## Exact true prime second-moment lower and the signed middle union

The original MiddlePrimeRebate lower proof supplies in each of 5858 accepted genuine (p_1,p_2) cells a true prime-cross count lower and a uniform cell lower k>0 on B/log n, from the minimum of its K₃,K₄,K₅,K₆. Thus on exactly the same disjoint true ordered cells B₂≥k²(1+O_J(1/L))L, instead of B≥k(1+O_J(1/L))L. The quantitative proof uses precisely the same lower sieve count addressed to the true prime on the other side, with no new factorability claim. With the existing first atanh lower for log and separate downward rounding to 10^-15 per cell, the sums were independently replayed in BigInt-rational arithmetic:
\[
 c_1=33390005752037/10^{15},\qquad c_2=1027859535234/10^{15}.
\]
First coincides with the pinned checker's own exact c₁; second gives ⟨Π,B₂⟩, ⟨B₂,Π⟩≥c₂ M+o(M), each orientation, not two independent targets. To replay from the [original arithmetic checker](cubic_quintic_sharp/check_middle_prime_rebate.py), keep all acceptance tests and replace its coefficient line by `coeff=(k*k)*2*loglo(E/z-1)/E`, and its final threshold by `req(Z == Q(1027859535234, 10**15), 'squared rebate replay')`; leave ordinary division, half-open true cells and per-cell rounding unchanged. This checks arithmetic, not the external analytical count theorem.

Let U_B be the **full original signed H(x)H(y) union** where at least one arm belongs to B's negative support. Pointwise H=−B there, so exact U_B=−⟨B,H⟩−⟨H,B⟩−⟨B,B⟩. The compact signed transfer of NegativeArmUnion / MiddlePrimeRebate gives ⟨B,H⟩=2bM−⟨B,Π⟩+o(M), and reflected. Combining with the one-target overlap cap above, not adding rebates from unrelated estimates, gives
\[
\boxed{\quad U_B\ge (-4b-U_{.04}b_2+2c_1+c_2)M+o(M),
 \qquad 2c_1+c_2=67807871039308/10^{15}>.06780787.\quad}
\]
One can also use the unweighted companion band itself, which is disjoint from all primes, to obtain a different upper for BB by applying upper .040 rough minus lower .105 rough to both B₂ marginals. The two approaches are alternatives, not additive (the second already excludes the prime receivers). In particular the original whole exterior includes other signs. The middle union may intersect the already paid >.105 or tiny **paired** unions on opposing arms although their one-arm sets are disjoint. No addition to the whole exterior until those actual intersections are addressed. The inequality is unconditional in R_J, so in particular valid if the target has no pair.

## Simultaneous capacity matrix with actual positive block (framework)

For any fixed common rough floor a that contains the literal supports of P,B (a=.040 for the middle, or .123 for a narrower negative subset), let Ω be the same actual both-rough target-unit ambient, measure ν = counting divided by M/L². For symmetric fixed J, interchanging x,y preserves Ω. Let Ω_cc be its composite-by-composite part, f=P/L, g=B/L, and µ=ν restricted to Ω_cc. Positive P and negative B supports are disjoint on each arm, hence fg=0. Put
\[
m=\int(f(x),g(x))^T d\mu,quad D=\mathrm{diag}(\int f(x)^2d\mu,\int g(x)^2d\mu),\quad
Q=\int(f(x),g(x))^T(f(y),g(y))d\mu,quad c=\mu(\Omega_{cc}).
\]
By symmetry Q is symmetric. All entries are measured on the same target, not replacement marginals. Under true no-pair on this symmetric interval, c=ν(Ω)−ν(Π_x)−ν(Π_y) exactly with unweighted prime indicators (subtract both disjoint prime occupancies); ordinarily add ν(Π_x∩Π_y). The diagonal D entries are actual rough-side second moments minus the corresponding true prime-cross second moments (exact with binary prime flags; switching to log weights costs o(1)). Similarly m uses actual prime mixed PΠ and BΠ subtracted from the rough marginals. Thus the measured first/second rebates feed a **single** composite-side capacity.

For any real vector t, integrate |t·(f_x,g_x)−t·(f_y,g_y)|² and the centered square of the sum. This yields
\[
D-Q\succeq0,\qquad D+Q-2mm^T/c\succeq0 \quad (c>0).
\]
Consequently
\[
(PB)^2\le(D_P-PP)(D_B-BB),
\quad
(PB-2m_Pm_B/c)^2\le(D_P+PP-2m_P^2/c)(D_B+BB-2m_B^2/c),
\]
where PP/PB/BB here are normalized entries of Q. This is strictly stronger than independently bounding |PB| by sqrt(D_P D_B) if an actual lower PP>0 is supplied (e.g. wider positive block) and the relevant diagonal capacities are finite. It also links the two unknown mixed prime crossings via the same c, rather than treating two orientations as separate estimates. For nonsymmetric J the exact 4×4 block Gram has D_L, D_R and Q,Qᵀ, and centering subtracts the actual stacked first moments outer product /c. These are genuine necessary inequalities but no quantitative closure follows yet: at broad floor .040 current rough variance caps are large. Any improved mixed evaluation should be inserted into these same-domain entries before claiming a global signed gain.


## Distinct receiver bands give a stronger BB-only cap and a joint PB/BB budget

For the pure middle overlap there is an even stronger alternate (not additive) same-target receiver bound. Write R_l=1_{P^->N^.040}, R_h=1_{P^->N^.105}; let I=R_l−R_h (exact least-factor band, no central primes). Apply lower linear sieve to each nonnegative compact real source W=B₂ or P₂=P²/L at the higher floor .105 and level N^.42, using the same literal product BV as before. The sifting ratio is 4, giving K_h=2log3/.42>5.231 (atanh series z=1/2 certifies). Thus ⟨W,L I⟩ and its reflected orientation are ≤(U_{.04}−K_h)m(W)M+o(M) by subtracting the actual higher-floor lower from the same source's actual lower-floor upper. In particular
\[
BB/M\le (U_{.04}-K_h)b_2+o(1)<9.072193375\,b_2+o(1).
\]
Here and below BB=⟨B,B⟩. This already excludes true prime receivers (they are in R_h), so **do not subtract c₂ a second time**. The resulting alternate signed union lower is [−4b−(U_{.04}−K_h)b₂+2c₁]M+o(M). Indeed this scalar alternate is better than using the plain U_{.04}b₂−c₂ cap above: the repo's separate genuine compact angular prime upper 3.446b₂M (valid for B₂ by same compact fixed-rank/polynomial floors, and fixed interval position cuts) plus the measured lower forces b₂≥c₂/3.446. Consequently K_h b₂>c₂. The squared-rebate result is still useful for joint budgets, but cannot be advertised as the strongest standalone estimate for BB if the already available genuine bands are used.

Here is a simultaneous inequality where the squared true rebate and the two band capacities **do** reinforce each other without double-counting. Set J_h=L R_h−Π≥0 (composite high receiver up to the harmless O_J(1) log discrepancy on prime rows), p₂=m(P₂), D=U_{.04}−K_h. On actual rows B lies in I and P in R_h, both zero on primes. Split each oriented B₂ source's available mass into low I, composite high J_h, and true prime Π, so total exactly ⟨B₂,L R_l⟩. The elementary AM–GM bound gives
\[
2BB\le \langle B_2,L I\rangle+\langle L I,B_2\rangle.
\]
Cauchy–Schwarz on the genuine low-by-high **same reflected rows** gives
\[
\langle P,B\rangle^2\le (\langle P_2,L I\rangle)\,(\langle J_h,B_2\rangle),\quad
\langle B,P\rangle^2\le (\langle L I,P_2\rangle)\,(\langle B_2,J_h\rangle).
\]
Product units: P₂=P²/L, L I on opposite arm; the exact indicators of both supports shrink both Cauchy factors. J_h=L on all composite high rows and ≥0 elsewhere, true. Bound each P₂ low marginal by D p₂ M+o(M), with p₂>0. Summing the capacities and substituting the two true prime rebates yields the **same-N coupled moments constraint**
\[
\boxed{\quad
2\frac{BB}{M}
+\frac{(\langle P,B\rangle/M)^2+(\langle B,P\rangle/M)^2}{D p_2}
\le 2 U_{.04} b_2-2c_2+o(1).
\quad}
\]
This is not the independent sum of worst marginal bounds. Also ⟨B₂,J_h⟩/M≥(K_h−3.446)b₂+o(1) by high rough lower minus genuine prime upper; it is exact non-prime occupancy in the limit. For instance if BB approached the full low-band cap D b₂ M, the paired PB amplitudes' remaining squared pool would be at most 2K_h b₂−2c₂, rather than the larger independent high-band upper 2U_h b₂−2c₂. Conversely unusually large PB forces a compensating BB slack. Opposite-prime second-moment rebate is taken once inside the combined pool. This estimates a physically relevant BB/PB trade-off, not the whole signed exterior; no current bound makes the latter positive.
