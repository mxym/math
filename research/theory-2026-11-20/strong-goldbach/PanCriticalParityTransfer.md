# At the original Pan cutoff, transfer the rough mixed-row error to a bounded-rank all-composite covariance

Let \(P\) be a large even integer, \(I=[P/3,2P/3]\), \(X=P/3\), \(L=\log P\), \(Q=\sqrt P/L^{20}\), \(r=P-n\), and \(S=S(P)\) the even Goldbach singular series. Put \(B(m)=-\sum_{d\mid m,\,d\le Q}\mu(d)\log d\) and \(K(m)=\sum_{d\mid m,\,d\le Q}\mu(d)\). Use \(P^-(1)=\infty\); \(R_y(m)\) means \(P^-(m)>y\). Physical sums below have \(n+r=P,\ n,r\in I\), or \(r\in I\) in one dimension. Fix
\[
 \eta=1/2000,\quad \kappa=2/25,\quad z=P^\epsilon,\quad Z=P^\kappa,\quad
 s=\eta/\epsilon,\quad u=1/(2\epsilon),\quad b=b(u)=e^{-\gamma}\int_0^{u-1}\rho(t)\,dt .
\]
Here \(\rho\) is Dickman's function; \(\epsilon>0\) sufficiently small and \(s\) are fixed **before** \(P\to\infty\). Define the reflected prime–short row and a different, centered all-composite statistic:
\[
 T_z=\sum R_z(n)R_z(r)B(n)\Lambda(r),\qquad
 M_\kappa=X^{-1}\sum_{r\in I}R_Z(r)\mu(r)B(r),
\]
\[
 D_\kappa=\sum R_z(n)R_Z(r)B(n)\mu(r)B(r)-XS\,b\,M_\kappa .
\]
The exact one-variable mean \(M_\kappa\) is retained. **Theorem.**
\[
                    T_z=XS b-D_\kappa+O(XS u^4s^{-s/2})+o_\epsilon(XS).       \tag{1}
\]
The big-O constant is absolute. No prime on either side contributes to the physical sum in \(D_\kappa\), since \(B\) vanishes on every central prime. Nonzero right inputs are squarefree composites with at most 12 prime factors. For every fixed tolerance one may first make the displayed sieve error smaller than that tolerance times \(XS\), then let \(P\) grow. This concerns the *whole* mixed row at the genuine fixed cutoff. The [unmasked row](PanCriticalPhysicalRoughness.md) is \(XS+o(XS)\); proper powers can be omitted from \(T_z\) at power-saving cost. No sign or smallness estimate for \(D_\kappa\) is asserted.

## 1. Exact parity identity and the moving wall

For squarefree \(m>1\), \(Y=\sqrt m\), use subscripts for cutoffs different from \(Q\). There is the identity
\[
 B_Y(m)+(\log m)K_Y(m)
 =\sum_{d\mid m,\,d<Y}\mu(d)\log(m/d)
 =\mu(m)\sum_{k\mid m,\,k>Y}\mu(k)\log k
 =\mu(m)B_Y(m)+\Lambda(m).
\]
There is no equality at the wall. We justify using the fixed \(Q\) in the **summed** identity, not in the pointwise statement.

On pairs with \(R_z(n)R_z(r)\), a squareful argument or a nonunit with \(P\) costs \(P^{1-\epsilon+o(1)}+P^{1/2+o(1)}\) points, even with divisor-bounded weights: sum \(P/\ell^2+1\) over \(z<\ell\le\sqrt P\), or \(P/\ell+1\) over \(\ell\mid P,\ell>z\). The same argument works for one rough variable. On the rough set every divisor count is \(O_\epsilon(1)\), and each short weight \(B\) or \(LK\) is \(O_\epsilon(L)\). The same discards permit the asymmetric target-unit short weight instead of \(B\) on either fully rough input. All proper powers in the right \(\Lambda\) cost \(P^{1/2+o(1)}\).

Divisors that disagree at the two walls are rough \(d\mid r\) in \([Q,\sqrt{2P/3}]\). Their reciprocal sum is \(O_\epsilon((\log L)/L)\): on each of \(O(\log L)\) dyads the one-dimensional upper sieve bounds rough integers by \(O_\epsilon(D/L)\) for lower endpoint \(D\). For each such \(d\), \((d,P)=1\), sieve \(m=r/d\) against small primes on both \(m,P-dm\), on an interval of length \(\asymp P/d\). Every small prime is coprime to \(d\), so there are two excluded residues at \(\ell\nmid P\), one at \(\ell\mid P\). An ordinary upper sieve at level \(P^{1/10}\) bounds the count by \(O_\epsilon(PS/(dL^2))\): the dimension-two product is \(\ll S/(\log z)^2\) and summed CRT floor errors are \(O(P^{1/10}(1+\log P))\) per \(d\), absorbed uniformly. In one dimension sieve just \(m\), giving \(O_\epsilon(P/(dL))\). Thus the absolute costs of moving the wall in the identity times \(B(n)\), or in the one-variable identity alone, are \(O_\epsilon(PS(\log L)/L)\) and \(O_\epsilon(P(\log L)/L)\), respectively. The fixed \(B(n)\) is used throughout. Replacing \(\log r\) by \(L\) has respective cost \(o_\epsilon(PS)\) and \(o_\epsilon(P)\): the same upper sieves on all rough inputs give \(O_\epsilon(PS/L^2)\) and \(O_\epsilon(P/L)\) points, and \(\log r=L+O(1)\).

## 2. Three matched means

Put \(h=\log z,\quad V_0=\prod_{\ell\le z}(1-1/\ell)\), and
\[
 W_B=-\sum_{d\le Q,R_z(d)}\mu(d)\log d/d,\qquad
 W_K=\sum_{d\le Q,R_z(d)}\mu(d)/d .
\]
The signed prime-simplex calculation in [global rough transfer, §3](PanGlobalRoughTransfer.md) and [signed shell, §1](PanQuarterTwoSigns.md) gives at fixed \(\epsilon\)
\[
 V_0W_B=b+o_\epsilon(1),\qquad L V_0W_K=c+o_\epsilon(1),
 \qquad c=2u e^{-\gamma}\rho(u).
\]
The actual \(\log Q/h\to u\) is permitted by continuity. Mertens' product bounds the absolute squarefree rough divisor harmonic sum by \(O(u)\); weighting it with \(\log d\) or \(L\) costs at most \(O(u^2 h)\). Removing prime factors of \(P\) above \(z\), or common primes of two rough divisor variables, has \(o_\epsilon(1)\) normalized cost: mark a prime and use \(\sum_{\ell\mid P,\ell>z}1/\ell\le L/z\) or \(\sum_{\ell>z}1/\ell^2\ll1/z\). Direct multiplication gives the uniform relations
\[
 V_1=\prod_{\ell\le z,\ell\nmid P}(1-1/(\ell-1))=(1+o_\epsilon(1))S V_0,
 \qquad
 V_2=\prod_{\ell\le z,\ell\nmid P}(1-2/\ell)\prod_{\ell\le z,\ell\mid P}(1-1/\ell)
      =(1+o_\epsilon(1))S V_0^2 .
\]

First evaluate the one-variable mean of \(R_z(r)(B(r)+LK(r))\). Fix a rough divisor \(d\le Q\) and sieve \(r/d\) at level \(P^\eta\) with excluded densities \(1/\ell\). The beta-sieve main is \(X V_0/d\) of relative width \(O(s^{-s/2})\) uniformly for large \(s\) ([fundamental lemma, Theorem 2.2](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/superscars-for-arithmetic-point-scatters-ii/3CCB969E058792C1803466AE0EF29136)); floor errors sum to \(O(L Q P^\eta)\). Bounding the width with the **absolute** divisor coefficients costs \(O(X u^2s^{-s/2})\). The prime mean of \(R_z(r)\Lambda(r)\) is \(X+o(X)\) by the ordinary prime number theorem and the proper-power bound. Section 1 gives
\[
 X^{-1}\sum_{r\in I}R_z(r)\mu(r)B(r)= b+c-1+O(u^2s^{-s/2})+o_\epsilon(1).      \tag{2}
\]

Second, the unconditional bilinear estimate is
\[
 (XS)^{-1}\sum R_z(n)R_z(r)B(n)[B(r)+L K(r)]
           = b(b+c)+O(u^4s^{-s/2})+o_\epsilon(1).                              \tag{3}
\]
Here is the specific extension from the [critical both-composite sieve](PanCriticalCompositePolynomialSieve.md). Use its nonnegative smoothing at the central endpoints and its CRT upper/lower sieves over compatible pairs of short rough divisors. Use separate bilinear forms for \(B B\) and \(B(LK)\), replacing the right coefficient \(-\mu(e)\log e\) by \(L\mu(e)\) in the latter and likewise its absolute majorant. The independent weights are bounded by \(L\); their signed main is \(X V_2 W_B(W_B+L W_K)\) up to the negligible target/common-prime terms. Incompatible divisor pairs vanish upon retaining the right unit condition, permissible by §1. For each beta-sieve divisor assign its small primes to the two physical inputs (only to the left for target primes). The proof using [Bettin–Chandee Theorem 1](https://arxiv.org/pdf/1502.00769) in the critical sieve applies to the signed upper model **and** the unsigned bounding width between upper and lower, because the replacement right weight also factors with identical norm bound. It saves \(P^{.007}\) per allocation on lengths at most \(P^{.501+o(1)}\), before the \(\ll P^\eta L\) allocations. The total width is \(\ll X V_2 (u^2 h)^2 s^{-s/2}\). This proves (3). By §1, \(T_z+\sum R_z(n)R_z(r)B(n)\mu(r)B(r)\) equals the unnormalized left side of (3) up to \(o_\epsilon(XS)\).

## 3. Equidistribution of the tagged signed complement

Let \(\mathcal L=\{r:R_z(r),\,P^-(r)\le Z\}\),
\(f(r)=1_{\mathcal L}\mu(r)B(r)1_I(r)\) and \(F(r)=L\,1_{\mathcal L}\mu^2(r)\tau(r)1_I(r)\), so \(|f|\le F\). For both \(g=f,F\) and each fixed \(A>0\),
\[
 \sum_{\substack{q\le QP^\eta\\(q,P)=1}}
 \left|\sum_{r\equiv P\bmod q}g(r)-\frac1{\phi(q)}\sum_{(r,q)=1}g(r)\right|
                  \ll_{A,\epsilon} P L^{-A}.                                      \tag{4}
\]
The actual coefficients matter: (3) alone does not imply (4).

Tag one actual prime \(\ell\in(z,Z]\) of squarefree \(r=\ell m\) by \(1/(1+\omega_{(z,Z]}(m))\), where \(\omega\) counts distinct primes in the window. This weight depends only on \(m\) since \(\ell\nmid m\). The remaining rough mask is \(R_z(m)\). For \(F\) use \(\mu^2(r)=\mu^2(m),\ \tau(r)=2\tau(m)\); for \(f\) use \(\mu(r)=-\mu(m)\) and
\[
 B(\ell m)=B(m)+\sum_{d\mid m,\,d\ell\le Q}\mu(d)\log(d\ell).
\]
Split the last log as \(\log d+\log\ell\). The separated long coefficients include the multiplicity denominator, \(\mu(m)\) or \(\mu^2(m)\), roughness, and independent divisor weights after normalization by \(O(L)\); they are bounded by a fixed divisor-function power. Short coefficients are prime indicators in subintervals of dyads, optionally weighted by \(\log\ell/L\). Extending the separated sums across \(\ell\mid m\) costs \(P^{1-\epsilon+o(1)}+P^{1/2+o(1)}\) even after the modulus sum: use \(\tau(P-r)\) on progression rows and \(\sum_q1/\phi(q)\ll L\) on means; all added rows contain a squared prime \(>z\). Other summed tag or divisor counts cost \(P^{o(1)}\).

For the true central restriction and \(d\ell\le Q\), use independent multiplicative meshes of ratio \(1+L^{-J}\) in \(m,\ell\) and, when needed, in \(d\mid m\). Keep boxes contained in the product cuts. Boundary cells lie within relative \(O(L^{-J})\) of \(P/3,2P/3\) for \(r\), or of \(Q\) for some divisor \(b=d\ell\) of \(r\). The latter affect only \(O(P L^{-J}+P/Q)\) physical indices by summing \(P/b\); the former affect \(O(PL^{-J}+1)\). The summed costs of all multiplicities on these sets are controlled by fixed divisor powers of \(r\) and \(P-r\) and log powers, so Hölder with ordinary divisor moments makes the lost mass \(O_A(PL^{-A})\) for large \(J\). This is a union estimate, not an error paid on every box. The total number of mesh boxes is a power of \(L\).

Here are the actual dispersion hypotheses. Put \(C,M\) equal to the **lower endpoints of the fine intervals** for \(\ell,m\); supports fit \([C,2C],[M,2M]\), \(MC\ge(1-o(1))P/3\), \(4MC>P\). Split the short prime range at \(P^{.002}\). For the upper segment [Fouvry (1987), Corollaire 1, pp. 618–619](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf) (with \(x=4MC\)) works up to \(q\le P^{.5005}\). Its two upper exponents are \((1+\log C/L)/2\) and \(4/7-6\log C/(7L)\), strictly above .5005 throughout \([.002,.08]\) with fixed margins. The corollary is uniform in the common macroscopic residue \(|a|\le4MC\) and accepts arbitrary modulus signs. For the lower segment \(P^{\epsilon-o(1)}\le C\le P^{.002+o(1)}\), the same corollary covers \(q\le\sqrt P\), now with fixed margins depending on \(\epsilon\). On the remaining dyads \(\sqrt P\ll q\ll P^{.5005}\), use the macroscopic-residue variant of [Fouvry–Radziwiłł, §§3–6 and Lemma 8.1](https://arxiv.org/pdf/1811.08672) proved for prime short weights in [polynomial roughness §C](PanPolynomiallyRoughSurvivors.md), based on [the macroscopic-shift dispersion proof](PanUnbalancedCofactor.md). It is not the unmodified \(|a|\le MC/3\) theorem. For \(k\le .002+o(1)\), \(v\le.5005+o(1)\), the inequalities \(36k+33v<17,\ 15(k+v)<8\) hold, \(q>C\) on these dyads and \(M/q\) grows by a fixed power. The short-prime length exceeds every \(\exp(K L/\log L)\) eventually. Prime indicators satisfy the short Siegel–Walfisz hypotheses including any extra unit restriction: difference the PNT in progressions on intervals, use partial summation for the log weight, and remove the at most \(\omega(t)\) primes dividing the extra masked integer \(t\), as in the cited §C. No SW is required for the long sequence. Signed long weights and arbitrary modulus signs are admissible throughout; this gives the absolute discrepancy, not an average over target residues. Arbitrary-log savings pay for the mesh boxes. This proves (4), also for the positive envelope.

## 4. Sieve the opposite variable against the tagged convolution

For each rough \(d\le Q,\ (d,P)=1\), sieve \(n=P-r\) with \(d\mid n\) on the sequence of \(r\)'s in (4). There \(r\) is rough already; small target primes therefore never divide \(n\). At other small primes one unit class for \(r\) is forbidden, of density \(1/(\ell-1)\). Either beta sieve at level \(P^\eta\) leads to the true common residue \(r\equiv P\bmod dw\) with \(w\) small-prime supported and coprime to \(dP\). Each modulus has at most one such split: its entire small-prime part is \(w\). Both for \(f\) and \(F\), \((r,dw)=1\) is equivalent to \((r,d)=1\) on their support. Thus (4) pays the combined discrepancy terms, even with an outside factor \(L\). The exact signed sum can be replaced by the signed upper-sieve model, with absolute error at most the unsigned \(d\)-coefficients times the upper-minus-lower width on \(F\). The principal width is at most
\[
 O\!\left(s^{-s/2}V_1
          \sum_{d\le Q,R_z(d)}\frac{\mu^2(d)\log d}{\phi(d)}
          \sum_r F(r)\right).
\]
The \(d\)-restriction \((d,P)=1\) is permissible in the actual rough sum by §1, and is kept through the progression calculation. For an **absolute** constant times \(XS u^4s^{-s/2}\), note that \(\sum_r F(r)\ll X u^2\): on squarefree rough integers apply the divisor hyperbola \(r=ab,\ a\le\sqrt P\), counting the shorter side twice. For every such rough \(a\), dropping \(b\ge a\) enlarges the count, and the one-dimensional upper sieve gives \(O(P/(a h))\) rough \(b\) on the allowed central interval, of length \(\asymp P/a\gg\sqrt P\), using level \(P^{1/10}\). The squarefree rough \(a\)'s have harmonic mass \(O(u)\); multiply by \(L\).

The signed principal itself is \(V_1\sum_r f(r)\sum_{d\le Q,R_z(d),(d,Pr)=1}-\mu(d)\log d/\phi(d)\) up to this width. The inner sum is \(W_B+o_\epsilon(h)\) uniformly in \(r\in I\): on squarefree rough \(d\) one has \(d/\phi(d)=1+O_\epsilon(1/z)\) and marking a prime \(>z\) dividing \(Pr\) uses \(O(L/z)\) in reciprocal mass. Consequently
\[
 \sum R_z(n)B(n) f(r)
    = S b\sum_r f(r)+O(XS u^4s^{-s/2})+o_\epsilon(XS).                         \tag{5}
\]
This evaluates the true tagged physical contribution; it does not factor the untagged covariance.

Split the parity-weighted convolution in §2 into (5) and the hard part \(D_\kappa+XS b M_\kappa\). The ordinary light mean in (5) equals the complete mean (2) times \(X\) minus \(X M_\kappa\). Thus that full convolution equals \(D_\kappa+XS b(b+c-1)+O(XS u^4s^{-s/2})+o_\epsilon(XS)\). Subtract from (3); \(c\) cancels, proving (1).

For example, writing \(R_{3,z}\) for the central physically rough original asymmetric long–long remainder and \(G_I\) for its weighted true-prime pair count, (1) and the critical both-composite result yield \(R_{3,z}=G_I-2XS b+XS b^2+2D_\kappa+O(XS u^4s^{-s/2})+o_\epsilon(XS)\). Physical target-divisor/power exceptions are negligible on this rough set. Neither this consequence nor the equidistribution above proves positivity. Classical complementary-divisor identities, the dispersion ingredients cited above and [Huang–Li's different squarefree parity reduction](https://arxiv.org/abs/2005.03811) are antecedents. The finite-rank residual here is a physical composite–composite covariance with the moving-wall cost, roughness error and exact centering retained.

## Related 2026 work

[Pham's October v1](https://www.preprints.org/manuscript/202610.3061) formulates other reflected rough covariance comparisons and controls. [Bahbouhi's November v1](https://www.preprints.org/manuscript/202611.0975) uses a rough prime/semiprime Liouville separation. Here complementary divisors and a verified tagged progression treatment convert the entire rough mixed row at the original Pan cutoff into a centered covariance on composites, with an exact one-variable mean. Neither prior source is used as a proof of the remaining covariance estimate.
