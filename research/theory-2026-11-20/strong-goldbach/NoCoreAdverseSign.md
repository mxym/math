# The no-core reflected macro-rough sector has an adverse net sign

Keep the **equal-cutoff** exact artificial row, \(Y=x^{.070}\), and the reflected half coefficient \(C^\dagger\) in [WholePositiveSmallCore.md](WholePositiveSmallCore.md), with \(\kappa_s=1\), whole prime \(s\)-band \(x^{.10}<s<x^{.14}\), and real \(W_s(q)=K_{P_3}(sq)\). All primes/integers in a physical term retain \(sq\in I\) and \((sq,N)=1\). Write \(M_N=\mathfrak S(N)x/(2L)\).

The **whole** no-core sector
\[
             P^-(q)>x^{.070},\qquad P^-(m)\ge x^{.120},\qquad m=N-sq
\tag{1}
\]
has signed contribution **at least \(+.030M_N\)** for every sufficiently large even \(N=2x\). Here \(q\) is the actual unrestricted integer in the opened row. Thus the negative rank-four subpatch inside this sector does not determine its net sign. This is a lower bound for the adverse sign in this particular opened sector, not a lower bound of this size for the whole residual or any statement about binary Goldbach being false.

For a second exact complement statement, take any collection \(\mathcal Z_-\) of actual cores \(1<z\le x^{.14}\) with \(R_Y(z)<0\) and no forbidden high power as in [WholePositiveSmallCore.md](WholePositiveSmallCore.md). Its whole reflected \(m\)-macro-rough sector has contribution at least
\[
  +.90\,M_N\!\!\sum_{\substack{s,\ z\in\mathcal Z_-\\(s z,N)=1}}
        W_s^\circ\, \frac{|R_Y(z)|}{(s-1)z}
                      \frac{\mathfrak S(Ns z)}{\mathfrak S(N)}
             - O_D(xL^{-D})
\tag{2}
\]
for every fixed \(D>0\). In particular negative cores of this size have the opposite overall sign to the previous positive-core estimate, not a zero-for-free approximation. No bound for their reconciliation with positive or larger cores is asserted.

## 1. Improved uniform density upper for positive even ranks

On \(P^-(m)\ge x^{.120}\), the exact cutoff errors in [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md), (10), vanish; \(C^\dagger(m)\) equals the symmetric min sum
\[
                         F(m)=\sum_{a\mid m}\mu(a)
                                        \min(\log a,\log(m/a))
\]
up to \(O(\tau(m)\log H)\), with \(H=\exp(L^\eta)\), \(0<\eta<1\). Repeated primes \(p\ge x^{.120}\) have power-small total cost, via square divisibility and the physical divisor multiplicities in \(n,m\). For the remaining squarefree inputs, rank is at most 8. Odd rank has \(F=0\) by complementary divisors, and rank one contributes zero exactly even before the limit, as already checked in the previous note. Rank two has
\[
 C^\dagger(m)=-2\log p_{\min}+O(\log H)
\]
uniformly, and its true PNT product density with positive weight \(2\log p_{\min}/L\) is \(D_2=2\log(44/25)>1.12\).

For rank four write \(a\le b\le c\le d\) for logarithmic exponent coordinates with sum 1 in the PNT simplex. The positive part of \(F/L\) occurs only on \(d<.5\), and equals \(2\min(2a,1-2d)\), by the exact four-prime formula in [NegativeRankFourCompensation.md](NegativeRankFourCompensation.md) and the zero sum when the largest prime is on the long side. Hence its PNT integrand is bounded by
\[
                  \frac{2\min(2a,1-2d)}{a b c d}
                                \ \le\ \frac4{b c d}\ \le\ 288 .
\tag{3}
\]
Here the minimum of \(bcd\) over the allowed shape is at least \(1/72\), as follows. For fixed \(a\in[.12,1/6]\), on the polytope \(b,c,d\in[a,.5]\), \(b+c+d=1-a\), its minimum is attained at a vertex by concavity of \(\log b+\log c+\log d\). The only feasible vertex pattern up to permutation is \((a,.5-2a,.5)\), and its product \(.25a-a^2\) is at least \(1/72\) at both endpoints of this \(a\)-interval, hence throughout. For \(a\in[1/6,.25]\) the upper .5 bound is automatic, and the minimum vertex pattern is \((a,a,1-3a)\). Its product \(a^2(1-3a)\) has no interior minimum on that interval and is at least \(1/72\) at the endpoints. This verifies (3) without optimizing over an unverified numerical shape. The unordered volume of the region \(t_i\ge.12,\ t_i\le.5,\sum t_i=1\) is \((.52^3-4(.14)^3)/144\) by the corner calculation in the preceding notes. Thus the true upper density of positive rank four is at most
\[
                       U_4' = 288\,\frac{.52^3-4(.14)^3}{144}
                               = .259264.
\tag{4}
\]
The actual moving half endpoint differs from \(x^{.5}\) by a fixed factor; standard product PNT box approximation gives the same density and all boundary mass is \(o(x/L)\).

For rank \(k=6,8\) we improve the crude size bound by exact pairing with its least prime \(p\): for each \(a\mid m/p\), pair \(a\) with \(p a\). Their \(\mu\) signs are opposite, and the function \(\min(t,\log m-t)\) is 1-Lipschitz in \(t\). Thus
\[
              |F(m)|\le 2^{k-1}\log p \le (2^{k-1}/k)\log m .
\]
The uniform PNT simplex volumes and denominator bounds from [TwoMarkNegativeCompensation.md](TwoMarkNegativeCompensation.md) now give upper positive density \(16807/(6\cdot262440)\) at rank six and \(1/(8\cdot555532992)\) at rank eight. With (4) their sum is \(<.270\), an exact rational inequality. The \(O_k(\log H)\) term, in every used fixed rank, is negligible by the same compact product upper sieves below. This proves the claimed improved upper density on the actual \(m\)-side, not a pointwise asymptotic on the shifted-prime pair.

## 2. True rough-composite lower, rough total upper

In (1), \(C_{q,Y}^{\rm hi}(q)=\Lambda(q)-\log q\) exactly by [WholePositiveSmallCore.md](WholePositiveSmallCore.md). True prime \(q\) contributes zero; ordinary composite \(q\) of at least two distinct prime factors gives ratio \(-1\); other proper prime powers cost \(x^{.57+o(1)}\) in counts and power-small after physical weights. Thus the \(m\) semiprime terms give positive contributions, while the adverse-to-this-lower-bound terms can be bounded by upper-sieving the nonnegative positive \(m\)-part over **all** rough \(q\). This does not infer any positive contribution from actual prime \(q\).

For the true weighted semiprime product weight of density \(D_2\), apply the same \(m\)-side full-scale BV and dimension-one \(q\) sieve as in [NegativeRankFourCompensation.md](NegativeRankFourCompensation.md), at fixed \(s\nmid N\). For \(e\mid q\), the true class is \(N\bmod s e\); only primes not dividing \(Ns\) are sifted, with \(g(p)=1/(p-1)\), all \(m\)-factors \(\ge x^{.120}\). The reference is independent of \(e\) except \(1/\phi(e)\) if sifting primes are \(<x^{.119}\); as before the reduced \(N,s\) units are kept explicitly. Distribution errors summed over all \(s,e\) are \(O_D(xL^{-D})\) by true moduli \(s e\le x^{.495}\) and product BV, using one genuine prime SW factor and an independent genuine prime or product at polynomial length. A weighted log-min \(m\) factor and the true central product cut are separated as in [TwoMarkNegativeCompensation.md](TwoMarkNegativeCompensation.md). For the \(m\) ranks used in the upper bound the same source applies (one prime, plus complementary product at polynomial scale), including the rank-four cap \(\sqrt{3x/2}\).

Use lower linear sieve at \(Y=x^{.070}\), \(D_{\rm lo}=x^{.280}\), so \(u=4\); use upper sieve for the actual prime \(q\) at \(x^{.119}\), \(D_{\rm p}=x^{.355}\), so \(u=.355/.119<3\). Boundary \(P^-(q)>Y\) is implemented with cutoff \(\lfloor Y\rfloor+1/2\), which leaves the limiting parameter \(4\) and continuous \(f(4)\) unchanged. The same mixed local factor is \(e^{-\gamma}\mathfrak S(Ns)/\log(\text{sifting scale})\), uniformly for every \(N\). Every genuine prime \(q\!\asymp x/S\) passes the upper sieve. Subtracting that upper from the lower rough count, and removing the proper prime powers, gives the positive rough-composite count factor
\[
                 \Delta_0=\frac{\log 3}{.140}-\frac2{.355}>2.20 ,
\tag{5}
\]
relative to \(\mathfrak S(Ns)/L\) times the genuine semiprime product mass divided by \(s-1\). The strict estimate follows for example from \(\log3>1.098\). Both sieves use the **same** \(m\) weighted sequence and local normalization.

For the adverse positive \(m\)-ranks use upper rough sieve at \(Y\), \(D_{\rm up}=x^{.350}\), parameter \(5+o(1)\). The usual differential-delay formula of the classical linear sieve gives
\[
 \frac{e^{-\gamma}F(5)}{.070}
       =\frac{2}{.350}\left(1+\int_2^4\frac{\log(t-1)}{t}\,dt\right)
       \le\frac{2}{.350}\left(2-\tfrac12\log3\right)<8.30.
\tag{6}
\]
Indeed on \(t\in[2,4]\), \(\log(t-1)\le (t-2)-(t-2)^2/(2(t-1))\), which follows by differentiation from \(\log(1+v)\le v-v^2/(2(1+v))\) at \(v\ge0\). Integrate to get \(1-\tfrac12\log3\) for that integral bound. The coefficients \(f,F\), their error control, and uniform root model are exactly the same Rosser--Iwaniec theorem as in the preceding notes. All progressions used in (6) also lie below the \(.495\) physical exponent cap.

## 3. Common true weight and no-core normalization

The true \(W_s(q)\) differs from \(W_s^\circ=(1-\log_x s)(1-2\log_x s)^2\) by \(O(1/L)\). On the rough macro-\(m\) domain this differs by only \(o(M_N)\) in the weighted count: the checked rough upper (6) gives a true product count \(O(\mathfrak S(N)x/L^2)\) over the finitely many relevant \(m\) ranks, with \(C^\dagger=O(L)\) there. The same upper pays all moving-neck errors \(O_k(\log H)\) and the odd rank contributions. Thus use the same positive \(W_s^\circ\) in both the lower and the competing upper. As before masks \((m,Ns)=1\) cost power-small mass on these product-model means, \(s\) prime outside \(N\) gives \(\mathfrak S(Ns)=\mathfrak S(N)(1+O(1/s))\), and \(\sum_sW_s^\circ/(s-1)>.44\cdot .336\) eventually. The actual phase-space factor \(x/(2L)\) in every \(m\) product density normalizes these weighted counts to \(M_N\), because the true \(C^\dagger\) weight is \(L\) times its normalized test. Combining (4)--(6), the no-core macro-rough sum has a net positive factor at least
\[
          \bigl(1.12\cdot2.20-.270\cdot8.30\bigr)\cdot.44\cdot.336
                            >.0329
\]
on \(M_N\), before \(o(M_N)\). This proves the safe \(+.030 M_N\). The negative rank-four patch for rough \(q\) is contained in this sector, so its previously proved \(-.012M_N\) must not be added or considered an independent net sign here.

## 4. Negative small cores

The proof of (3) of [WholePositiveSmallCore.md](WholePositiveSmallCore.md) used \(R_Y(z)>0\) solely to regard the outer arithmetic coefficient as nonnegative and divisor-bounded. It proves the same negative bound with **any** nonnegative weight \(\omega(z)\le\tau(z)^C\) in place of \(R_Y(z)\) in the expression with \(\omega(z)\log w/\log q\). In particular this applies to \(\omega(z)=|R_Y(z)|\) on \(\mathcal Z_-\), using exactly the same \(1/p\) local factor when \(p\mid z\) and the same log-small absolute error. On these physical cores the literal ratio is \(R_Y(z)\log w/\log q=-\omega(z)\log w/\log q\). Reversing the whole tested sum gives (2) with no statistical assumption. It controls the sign on this sector, although it does not upper-bound the entire adverse complement.

The whole opened row remains equal to its original true-prime counterpart \( \mathcal T_{\rm p}(C)\) as verified in the preceding note, but none of these sectors individually transfers to that true-prime row. The signs are genuine finite-target signs of two opened sectors, positive here and negative in the earlier notes. Their accounting with the other cores, with \(m\) having smaller prime factors, and ultimately with the actual binary Goldbach target is still open.

## Scope relative to parallel work

The classical distribution and linear-sieve inputs do not break parity. Related 2026 sources include [Arneth's quartic/Vaughan reassembly](https://zenodo.org/records/23504447), [Pham's reflected mixed rough estimates](https://www.preprints.org/manuscript/202610.3061), and [Bahbouhi's prime/semiprime survivor identity](https://www.preprints.org/manuscript/202611.0975). These address related decompositions or rough comparisons; this note concerns the signed complete no-core sector of the project's equal-cut two-sided coefficient and its scope is limited to that sector.
