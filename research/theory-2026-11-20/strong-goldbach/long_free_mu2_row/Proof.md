# A full long-free Möbius branch can be removed from the actual shared-index covariance

This is an unconditional fixed-target result for the same marked shared-index covariance as [the above-root transfer](https://github.com/mxym/math/commit/48786012bff7073486a373df69f35611a803e916). It removes an entire branch of an exact Möbius identity, including the entire squarefree semiprime part with least factor at most \(x^{.389}\) in the **new** covariance remainder. The resulting higher-rank signs need not improve. The signed covariance of all remaining rows, and binary Goldbach, are not settled.

Let \(N=2x\) be a prescribed even integer, \(Y=\sqrt{x}\), \(L=\log x\), \(\ell=\log L\), \(z=\exp(L/\ell^2)\), and \(R_z(n)=1_{P^-(n)>z}\). Keep
\[
 d,e\in[.65Y,.8Y],\quad k\in[Y,1.1Y],\quad (dek,N)=1,\qquad y=N-ek.
\]
Let \(\beta(e)\) be the number of ordered labels \(p_2p_3\mid e\), with actual primes
\[
 x^{.029}\le p_2\le x^{.031},\qquad x^{.075}\le p_3\le x^{.078}.
\]
The labels are independent of \(k\); they may also divide it. Use the literal above-root residual score
\[
 K(y)=R_z(y)\sum_{\substack{rs=y\\r>x^{.505}}}\mu(r)\log s.
\]
Put \(\mu_2=\mu*\mu\), \(T_s=x^{.766}/\sqrt{s}\), and
\[
 F(y)=-R_z(y)
 \sum_{\substack{sc a=y\\z<s\le x^{.389},\ a>T_s}}\mu_2(c)\log s .
 \tag{1}
\]
The integer \(a\) in (1) is not a prime variable and not restricted to being squarefree. It is the unique long free factor in the underlying Möbius expansion described below, not a large prime factor of \(y\).

**Whole branch transfer.** For any \(B>0\) and fixed \(D\), with any \(u_{d,k}\) such that
\[
 |u_{d,k}|\le L^D\tau(d)^D\tau(k)^D\tau(N-dk)^D,
\]
one has, on the displayed marked and unit region,
\[
 \sum_d\left|\sum_{e,k}\beta(e)\,u_{d,k}F(N-ek)\right|
 \ll_{B,D}x^{3/2}L^{-B}.
 \tag{2}
\]
Consequently \(\sum_{d,e,k}\beta(d)\beta(e)K(N-dk)K(N-ek)\) is unchanged up to \(O_B(x^{3/2}L^{-B})\) when both \(K\)'s are replaced by \(K-F\). This holds as a signed replacement against any one permissible opposite physical row, not just for the unweighted quadratic form.

**Physical consequences.**
* If \(y=s_0p\) is a squarefree semiprime with \(z<s_0\le x^{.389}\) and \(s_0<p\) (both actual primes), then \(K(y)=F(y)=-\log s_0\). Thus this entire actual low-side semiprime family vanishes from \(K-F\).
* If \(y=p_1p_2p_3\) is squarefree with all three actual prime exponents in \([.25,.389]\), then \(K(y)=\log y\), \(F(y)=-\log y\), and \(K(y)-F(y)=2\log y\). Thus the sign ledger is not a monotone improvement.
* In (2) take the opposite actual prime row \(u_{d,k}=\beta(d)(\log(N-dk))1_{N-dk\ {\rm prime}}\). Each of the positive and absolute negative **divisor-labelled** masses of \(F\) is \(\gg x^{3/2}\ell^4\varphi(N)/N\). This is a genuinely signed, not an unsigned, deletion. Two opposite labels may occur at the same physical \(y\).

## 1. Exact Möbius opening and original accounting

Let \(\mathbf1(n)=1\), \(\delta(n)=1_{n=1}\), \(U=x^{.24}\), and \(\mu_{\le U}(n)=\mu(n)1_{n\le U}\). The arithmetic function \(\delta-\mathbf1*\mu_{\le U}\) is supported on \(n>U\). Raise it to the fifth convolution power and multiply by \(\mu\). This gives, exactly for \(r\le U^5\),
\[
 \mu(r)=\sum_{j=1}^5(-1)^{j-1}\binom5j
          \big(\mu_{\le U}^{*j}*\mathbf1^{*(j-1)}\big)(r).
 \tag{3}
\]
It applies to every original \(r\le y<1.5x\) for sufficiently large \(x\), including nonsquarefree \(r\). On \(s\le x^{.389}\), a free \(\mathbf1\)-factor \(a>T_s\ge x^{.5715}\) can occur at most once in any original convolution tuple, since \(T_s^2>r\). Once it is chosen, the entire remaining product \(c=r/a<1.5 x^{.234}/\sqrt{s}<U\). Thus the other \(\mu_{\le U}\) restrictions disappear identically, and the remaining coefficient in the \(j\)-term is \(\mu^{*j}*\mathbf1^{*(j-2)}(c)=\mu_2(c)\) when \(j\ge2\), with \(j-1\) choices of the free position. The finite coefficient is
\[
 \sum_{j=2}^5(-1)^{j-1}\binom5j(j-1)=-1 .
\]
For these \(s\), \(r=y/s\gg x^{.611}\) so the old \(r>x^{.505}\) restriction is automatic. The exact sum of this long-free branch of (3) in \(K\) is (1); outside the stated \(s\)-range (1) changes no term. For \(R_z(y)=1\) there is no \(1<s\le z\) to consider, and \(s=1\) has zero log weight. The remaining \(K-F\) is a different signed coefficient, not the original \(\mu\) multiplied by a nonnegative cutoff. Both \(K\) and \(F\) are bounded by \(L\) times a fixed divisor power of \(y\), since \(|\mu_2(c)|\le\tau(c)\). Expanding the quadratic form and using (2) with the corresponding true opposite row proves the replacement assertion.

For the rank-two statement \(p\asymp x/s_0>x^{.611}/2\). The only nonzero divisor pair in \(K\) has \(r=p,s=s_0\); the only eligible free \(a\) in (1) is \(a=p,c=1\), since \(p\sqrt{s_0}\gg x^{.8055}\). For the rank-three statement, each singleton exponent is below \(.505\) and each pair has exponent at least \(.611+o(1)\) on \(y\asymp x\). Therefore exactly the three choices of singleton \(s\) contribute to \(K\). For (1) they are again the only possible \(s\). Each has \(a=r,c=1\) only: proper divisors of this \(r\) are individual primes below \(x^{.389}\), and \(r/T_s\gg x^{.0395}\). This proves the displayed signs.

## 2. Literal modulus, rough expansion, and cutoffs

For each fixed \(d\), expand \(e=p_2p_3h_0\) without replacing its multiplicity. Write \(A=kp_2p_3\) and
\[
 I_k=[N-.8kY,N-.65kY].
\]
For fixed \(k,p_2,p_3\) with \((A,N)=1\), the original conditions on the source are exactly
\[
 y\equiv N\pmod A,\qquad y\in I_k,\qquad(y,N)=1.  \tag{4}
\]
Indeed \(h_0=(N-y)/A\) is positive integral and \((h_0,N)=1\) is equivalent to \((y,N)=1\). All \(I_k\subset[1.12x,1.35x]\). In particular \(N-y\ne0\) on the genuine support. Any \(A\) involved has at most a fixed divisor-power number of \((k,p_2,p_3)\) decompositions, even if the labels divide \(k\). Uniformly on these \(A\)'s,
\[
 x^{.6038}\le A\le x^{.6092}
 \tag{5}
\]
for sufficiently large \(x\).

In (1), \(R_z(y)=R_z(c)R_z(s)R_z(a)\) exactly, with no pairwise coprimality requirement. Keep \((cs,N)=1\) on the independent \(c,s\) coefficients. The originally required \((a,N)=1\) may be dropped with arbitrary log saving. In the difference, some \(p>z\) dividing \(N\) divides \(a\), and hence \(y\). The number of such \(y\le1.5x\) is \(O(xL/z+L)\). Each physical \(y\) has fixed divisor-power product multiplicities on \(c,s,a\) and \(e,k,p_2,p_3\); the latter are bounded by a divisor power of \(N-y\). Ordinary divisor moments in \(y,N-y,N-dk\), with the extra free \(Y\) factor in \(d\), then give the arbitrary-log saving by Hölder and clipping \(\tau(N-dk)\) at a sufficiently large log power first. The same drop has negligible cost in any positive support estimate below. On every progression in (4) the three factors and any divisor of them are units modulo \(A\), since \(N\) is a unit.

Expand only the free rough factor \(R_z(a)\) by a truncated inclusion–exclusion of order \(J=\lceil C_B\ell\rceil\); call the squarefree divisors \(\lambda\) to distinguish them from the logarithm \(\ell\). Their support is \(\lambda\le z^J=x^{o(1)}\), with coefficients \(\mu(\lambda)\). The uniform pointwise error is bounded by \(\binom{\omega_{\le z}(y)}J\) (choose an adjacent order if necessary). For any fixed \(m\ge1\), expand its \(m\)th power and group the subsets by their union. Each prime in the union can have at most \(2^m-1\) labels, the union length lies between \(J\) and \(mJ\), and divisibility of \(y\) by its product costs \(O(x/q+1)\). Hence the \(m\)th moment is
\[
 \ll x\sum_{j=J}^{mJ}
     \frac{((2^m-1)\sum_{p\le z}1/p)^j}{j!}+x^{o(1)}.
\]
For sufficiently large \(C_B\) this is \(O_{B,m}(x L^{-B})\) at every desired \(B\). Hölder with fixed divisor moments on \(y,N-y\) and the original weight in \(d,k\) proves the claimed physical bound, also in the presence of \(\mu_2(c)\). This handles the signed sum; no unsigned sieve bracket is applied to it.

Here and in the following estimates, sharp product and moving cutoff tests can be separated by relatively \(L^{-J_0}\)-fine positive partitions, with \(J_0\) chosen for the desired log precision. Details are as follows. Divide \(k\) into bins, and all \(c,s,a\) lengths into ordinary dyadic then relative \(L^{-J_0}\) bins. Work with entire cells entirely on one side of \(ca s\in I_k\) and \(a\sqrt{s}>x^{.766}\). Replace \(a\)-interval indicators by smooth cutoffs supported within a relative \(O(L^{-J_0})\) extension, with derivatives \(O_j(L^{O_j(J_0)})\) in its normalized coordinate. Positive partitions can be used, or one can smooth each interval boundary with even narrower transition widths so the summed error is as follows. For the \(I_k\) endpoint cells, each \(e\) lies within relative \(O(L^{-J_0})\) of one of the two fixed \(e\)-endpoints. Unweighted there are \(O(x^{3/2}L^{-J_0}+x)\) triples \(d,e,k\) in these strips. For the other \(a\)-boundaries, fix \(c,s\) in dyads with lengths \(C,S\), and the \(a\)-dyad \(W\), so \(CSW\asymp x\). Each \(a\) lies in a set of length \(O(W L^{-J_0})\) at a fixed or \(s\)-dependent endpoint. Thus there are \(O(x L^{-J_0}+C S)\) affected \(c,s,a\)-triples per dyadic boundary (one can sum the additional cell boundaries first or use a smooth partition of unity). Use \(W\gg x^{.5715}\), and the fixed divisor moments with \(y=cas\) and \(N-y\) to restore the actual representations and extra \(d\)-length. This pays every log power as \(J_0\) grows. In more detail for simultaneously smoothing the many artificial cell boundaries: use transition widths \(O(W L^{-3J_0})\) throughout, so their total width at fixed other factors is \(O(W L^{-2J_0})\) plus at most \(O(L^{J_0})\) floor errors; the latter still save a power because \(CS\ll x^{.429}\). Endpoints for \(s,c\) may be sharp; the \(s\)-cell is one contiguous interval after the Cauchy step below. Distinct retained boxes cost a fixed log power.

For the corresponding zero-frequency integrals, replacing the cutoffs back by the original ones costs equally little. For fixed \(k\) a relative thickening of \(I_k\) gives \(y\)-length \(O(xL^{-J_0})\); for each \(c,s\), the approximated region in \(a\) differs by at most \(O(WL^{-J_0})\) at the \(T_s\) endpoint and by the same total width estimate at artificial mesh cuts. Summing with \(|\mu_2(c)|\log s\) costs fixed log powers in each dyadic rectangle, using \(\sum_{c\sim C}\tau(c)\ll C L^C\). The model is weighted by \(1/A\), and its divisor-weighted mark sum is \(O(1/Y)\) per \(k\) up to log powers, by \(\sum_{p_2,p_3}1/(p_2p_3)\ll1\). These floor/neck arguments leave the exact original window in the final principal, not a free approximation to it. All boxes with nonzero frequencies satisfy \(W C S\asymp x\), \(S\le x^{.389+o(1)}\), and \(W\sqrt S\ge x^{.766-o(1)}\).

## 3. Nonzero reciprocal frequencies: a uniform elementary power saving

Fix one smooth separated box and one \(\lambda\le x^{o(1)}\); put \(A\asymp Q\) dyadically. The retained \(a\)-weight is \(f(a/W)\) with the derivative bounds above. For \((\lambda cs,A)=1\), Poisson summation the way it actually occurs gives
\[
 \sum_{\substack{a\equiv N\overline{cs}\ (A)\\ \lambda\mid a}}f(a/W)
 =\frac{W}{A\lambda}\sum_{h\in\mathbb Z}
    \widehat f\left(\frac{hW}{A\lambda}\right)
           e_A\left(hN\overline{\lambda c s}\right).
 \tag{6}
\]
The Fourier convention is \(\widehat f(t)=\int f(u)e(-tu)\,du\) and \(e_A(t)=e(t/A)\). The displayed sign follows by Poisson on the progression for \(a/\lambda\). Fix \(\xi=.0001\). If \(W/(Q\lambda)\ge x^\xi\), every nonzero frequency contributes an arbitrarily strong power-tail bound by sufficiently many integrations by parts. Otherwise cut at \(H\asymp x^{2\xi}Q\lambda/W\ge x^\xi\), taking a common cutoff for the dyadic \(A\)'s. The omitted tails are again power-small after all factor and modulus sums. Truncated Fourier weights are \(O(1)\), and can depend on \(h,A\) without harming the following absolute estimates.

Drop the \(s\)-coefficient by Cauchy over its actual interval, but retain \((s,A)=1\). After the square is expanded, the diagonal equation is
\[
 hc'-h'c=0
\]
as an exact integer equality. Indeed \(HC=o(Q)\): using \(WCS\asymp x\) and \(W\sqrt S\ge x^{.766-o(1)}\), one has \(HC/Q\ll x^{2\xi+o(1)}\lambda x/(W^2S)\ll x^{-.531+o(1)}\). Thus a nonzero numerator is not divisible by \(A\). The rational-equality diagonal has \(O(HC\log(2HC))\) solutions: reduce each positive direction \(h/c\) to lowest terms of heights \(h_0,c_0\), and if it has at most \(U=\min(H/h_0,2C/c_0)\) lifts, write \(U^2=\sum_{j\le U}(2j-1)\); the latter sum over directions is \(\ll HC\sum_j1/j\). Negative \(h\) is handled separately; opposite signs cannot lie on the diagonal. Divisor weights on \(c\) and each other factor can cost \(x^{o(1)}\) on this power-saving step.

If \(\Delta=hc'-h'c\ne0\), the coefficient of \(\bar s\) in the squared phase has gcd with \(A\) exactly \((\Delta,A)\), since \(N,\lambda,c,c'\) are all units in that term. Fourier completion of the interval of \(s\)'s (length \(O(S)<A\)) and the classical composite-modulus Weil bound for complete Kloosterman sums give
\[
 \left|\sum_{\substack{s\in I\\(s,A)=1}}e_A(b\bar s)\right|
 \ll A^{1/2+o(1)}(b,A)^{1/2}.
 \tag{7}
\]
For instance Fourier inversion of \(1_I\) on the residue ring has normalized \(\ell^1\)-norm \(O(\log(2A))\), and for frequency \(j\) the complete sum is bounded by \(\tau(A) A^{1/2}(b,j,A)^{1/2}\) (the usual absolute constant at the small 2-adic powers is harmless). There is no assumption that \(A\) is prime or squarefree. Over \(A\asymp Q\), for each nonzero \(\Delta\) of size \(O(HC)=o(Q)\),
\[
 \sum_{A\asymp Q}(\Delta,A)^{1/2}
 \le\sum_{b\mid|\Delta|}b^{1/2}O(Q/b+1)
 \ll Q\,\tau(|\Delta|)=Qx^{o(1)}.           \tag{8}
\]
After positivity the actual marked moduli may be enlarged to all \(A\asymp Q\) here; their label multiplicity and weights add at most \(x^{o(1)}\) on this step. The coprimality and target conditions were used before that enlargement. In particular (8) does not treat the moving \(N\) as a varying gcd multiplier.

Writing the finite \(s,c,h\) sum before the factor \(W/(A\lambda)\) as \(B_A\), the preceding computation gives, upon summing in \(A\) and using Cauchy/Jensen on the off-diagonal square root,
\[
 \sum_{A\asymp Q}|B_A|
 \ll x^{o(1)}Q\big(S\sqrt{HC}+S^{1/2}Q^{1/4}HC\big).
\]
Restoring \(W/(A\lambda)\), these two errors divided by the natural \(W C S\asymp x\) are respectively
\[
 \ll x^{o(1)}\lambda^{-1}\sqrt{H/C},
 \qquad
 \ll x^{o(1)}\frac{Q^{5/4}x^{2\xi}}{W\sqrt S}.
 \tag{9}
\]
Here \(H/C\ll x^{2\xi+o(1)}\lambda Q S/x\le x^{-.0016+o(1)}\), and the exponent of the second bound is at most
\[
 \frac54(.6092)-.766+2\xi+o(1)=-.0043+o(1).
\]
Thus there is a fixed power saving, uniformly. This is why the actual s-limit \(.389\), the free cutoff \(.766-v/2\), and the two-mark interval (5) leave reserve throughout the proof. Summing the fixed log powers of boxes and the \(x^{o(1)}\) choices of \(\lambda\) preserves a power saving. For each fixed \(d\), the true bounded-divisor envelope in (2) is \(\ll x^{o(1)}\) after aggregation of a dyadic \(A\), so (9) pays it outright; the further sum in \(d\) costs \(O(Y)\). The sharper divisor moments needed for log-size clipping, necks, and tails were paid separately in §2.

## 4. The true zero frequency has signed cancellation

The \(h=0\) term of (6) only includes \((\lambda,A)=1\). Complete the truncated scalar sum \(\sum_{\lambda}\mu(\lambda)/\lambda\) to the finite Euler product
\[
 W_z(A)=\prod_{\substack{p\le z\\p\nmid A}}(1-1/p),
\]
using the same factorial tail as before; its error is arbitrarily log-small uniformly in \(A\). After restoring the exact window as in §2, the model for (1), at a fixed admissible \(k,p_2,p_3\), is
\[
 -\frac{W_z(A)}{A}
 \int_{I_k}\sum_{\substack{z<s\le x^{.389}\\(s,AN)=1}}
 \frac{R_z(s)\log s}{s}
 \sum_{\substack{c<y/(sT_s)\\(c,AN)=1}}\frac{\mu_2(c)R_z(c)}c\,dy .
 \tag{10}
\]
The measure \(dy/(cs)\) is the exact change from \(a\) to \(y=cas\) for fixed \(c,s\), including the true moving cutoff \(a>T_s\). Formula (10) is a progression zero mode with \(W_z(A)/A\), not an independently postulated prime reference. Missing a prime dividing \(A\) from this product is essential because only unit progressions were counted. The differently placed \(N\)-unit mask on \(c,s\) is still present; the \(N\)-unit mask on \(a\) was paid on the actual rough integers before inclusion–exclusion.

Here \(y/(sT_s)\gg x^{.0395}\) throughout. We use the uniform finite rough harmonic identity
\[
 \sum_{\substack{n\le T\\(n,D_1)=1}}
 \frac{\mu(n)R_z(n)}{n}
 \ll_{B,\eta,C} L^{-B}
 \quad\big(x^\eta\le T\le x^C,\ D_1\le x^C,\ \eta>0\text{ fixed}\big).
 \tag{11}
\]
For completeness its Dirichlet series is \(1/\zeta(1+w)\) times \(\prod_{p\le z\ {\rm or}\ p\mid D_1}(1-p^{-1-w})^{-1}\). Perron at a half-integer with height \(\exp(\sqrt L)\), initial line \(1/\log T\) and final line \(-c_0/\log z\), has no pole at \(w=0\) because \(1/\zeta(1+w)\) has a zero. Both vertical segments and horizontals use the classical zeta zero-free inverse bound, with \(\log z\gg \sqrt L\). The finite product on these contours is a log power uniformly: for \(p\le z\), use \(p^{c_0/\log z}\le e^{c_0}\) and Mertens; the other \(O(L)\) primes are \(>z\) so their product is \(1+o(1)\). The shifted vertical loss is at most \(\exp(-c_0\eta\ell^2)\) times log powers. With coefficients bounded by \(1/n\), truncated Perron has error \(O((\log T)^C e^{-\sqrt L}+T^{-1})\) at a half-integer, by splitting the sum near and away from that endpoint. This proves (11) without dropping any target-dependent local mask.

The same assertion for \(\mu_2\) follows from ordinary Dirichlet hyperbola: \(R_z\) and the unit mask are completely multiplicative indicators, so the exact masked harmonic coefficient is the convolution of the two masked coefficients in (11). In each hyperbola term one variable has endpoint at least \(\sqrt T\) with arbitrary log cancellation; the other has harmonic absolute sum \(O(L)\). Thus the innermost sum of (10) is an arbitrary inverse log, even when its endpoint moves and is a strict inequality. The total of (10) is \(O_B(xL^{-B}/A)\) per labelled modulus, using a larger reserve in (11). For each \(k\), \(\sum_{p_2,p_3}1/(kp_2p_3)\ll1/Y\), and \(\sum_{d,k}|u_{d,k}|\ll xL^C\) by the same moments. This proves (2) after adjoining the nonzero frequencies and earlier errors.

## 5. The signed removal occurs at real mass

Choose \(x^{.35}<s<x^{.38}\) with \(s\) still \(z\)-rough, and restrict \(y\) to the common radial interval \([1.22x,1.26x]\subset I_k\). The c-slices \(c=1\) and \(c=p\) with a genuine prime \(x^{.01}<p<x^{.02}\) both satisfy the free cutoff \(a>T_s\) with power slack: \(a=y/(cs)\), so \(a\sqrt{s}\gg x^{1-.02-.19}=x^{.79}\). The first slice has negative label \(-\mu_2(1)=-1\), and the second positive label \(-\mu_2(p)=2\). The proofs of §§2–3 apply unchanged to these nonnegative masses separately; only the \(c\)-coefficients are restricted. For the upper bounds in (9), if \(c=1\) then any used dyadic box with \(H\ge1\) still has \(H/C\le x^{-.0016+o(1)}\), which is impossible; hence such boxes are safely in the no-nonzero-frequency case. Equivalently the free length in the \(c=1\) slice is already well above \(A\).

In either slice the absolute zero mode is at least
\[
 \frac{x V_z}{A}\sum_{\substack{x^{.35}<s<x^{.38}\\(s,AN)=1}}
                   \frac{R_z(s)\log s}{s}
 \cdot c_1
 \gg \frac{x}{A}V_z^2 L^2
 \gg \frac{x}{A}\ell^4 ,
\]
where \(V_z=\prod_{p\le z}(1-1/p)\), and \(c_1>0\) comes from the reciprocal weight of \(c=1\) or of genuine \(c\)-primes in their fixed exponent band. Prime divisors of \(AN\) removed from that band have negligible weight. The rough harmonic lower for \(s\) follows by elementary Bonferroni in polynomially long dyads (or partial summation of their uniform rough counts), and removing the \(O(L)\) large primes dividing \(AN\) is negligible as in §2. There are order \(L\) dyads in the macroscopic \(s\)-range, and the test \(\log s\) supplies the second factor \(L\). The inequality uses \(W_z(A)\ge V_z\); no singular series lower is borrowed.

Finally \(\sum_{p_2,p_3:(p_2p_3,N)=1}1/(kp_2p_3)\gg1/Y\) for admissible \(k\). The established genuine marked opposite prime occupancy in [§3 of the earlier proof](https://github.com/mxym/math/commit/48786012bff7073486a373df69f35611a803e916) is \(\sum_{d,k:(dk,N)=1}\beta(d)a(N-dk)\gg x\,\varphi(N)/N\), with exactly these slope bands and windows. The separately transferred positive and negative slices therefore each have the stated lower mass with actual opposite primes. Additional labels of either same sign only increase that labelled absolute mass.

## Scope

This attacks the actual signed right side of the marked shared-\(k\) reduction, originally motivated by [Pham, October 2026, Appendix D](https://www.preprints.org/manuscript/202610.3061). It uses no new preprint distribution claim: the estimate (9) is elementary Poisson, the classical completed Weil bound and the elementary average of a nonzero gcd. The residual still contains all sharp HB branches with no free factor \(>x^{.766}/\sqrt{s}\) on the displayed \(s\)-range, plus the whole untouched support with \(s>x^{.389}\). In particular the balanced triprime test above shows why this is not a uniform one-sided bound for \(K-F\). A previously priced unbalanced semiprime and its compensating cross terms in the original \(K\) ledger cannot be credited again after this replacement. Narrow applications of stronger triple-convolution theorems to other literal coefficients are separate unless the intersection with (1) is itself controlled.
