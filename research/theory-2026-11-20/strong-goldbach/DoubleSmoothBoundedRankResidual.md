# Two smooth Vaughan cutoffs localize the actual opened residual to bounded ranks

Use the fixed even target \(N=2x\), \(L=\log x\), \(I=(x/2,x]\), and \(n=sq\in I,\ m=N-sq,\ (sq,N)=1\) from [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md). The short factor \(x^{.10}<s<x^{.14}\) is a true prime throughout. Take the exact \(W_s(q)=K_{P_3}(sq)\) and \(M_N=\mathfrak S(N)x/(2L)\). The genuine prime-quotient row is \(\mathcal T_{\rm p}\). Its reflected coefficient \(C\) is the original one in that note. Take the equivalent smooth reverse coefficient \(B_f(q)\) in [SmoothReverseCoreShield.md](SmoothReverseCoreShield.md), with fixed \(Y=x^{.070}\) and fixed smooth cutoff \(f\).

Independently choose \(0<\alpha_0<\alpha_1<1/2\), a fixed smooth probability density \(\psi_m\) compactly supported in \((\alpha_0,\alpha_1)\), and
\[
  f_m(t)=\int_{\alpha\ge t}\psi_m(\alpha)\,d\alpha\quad(t\ge0),
  \qquad g_m(t)=(2t-1)f_m(t).
\]
As in the reverse note, take any smooth compact extensions with those values on \([0,\infty)\). Define the literal composite coefficient
\[
 Z_m(m)=
 \begin{cases}
  (\log m)\displaystyle\sum_{d\mid m}\mu(d)g_m(\log d/\log m),
                                &m\text{ composite and not a prime power},\\
  0,&m\text{ a prime power, including a prime}.
 \end{cases}
\tag{1}
\]
The scale \(M_N\) is unchanged. Uniformly at each sufficiently large even target, for any fixed \(0<\nu<1\),
\[
       \mathcal T_{\rm p}(C)
              =\sum_{s,q}W_s(q)Z_m(N-sq)B_f(q)
                    +O_{f,f_m,\nu}(M_N L^{\nu-1}).
\tag{2}
\]
Here \(q\) on the right is an **integer**, and the physical unit and central constraints are the same as above. The sum of absolute values on the right is \(O_{f,f_m}(M_N)\). For every \(x\)-dependent \(3\le T\le x^{.02}\), its **actual** absolute mass on \(\min(P^-(q),P^-(m))\le T\) is
\[
       O_{f,f_m}\!\left(M_N\frac{\log T}{L}\right)+O_D(xL^{-D}).
\tag{3}
\]
In particular one may reduce (2) to **squarefree** \(q,m\), both having all prime factors \(>x^\epsilon\), with proved error \(O_{f,f_m}(\epsilon M_N)+o(M_N)\) for any fixed \(0<\epsilon<.02\). The remaining ranks are bounded in terms of \(\epsilon\), without any prescribed macro-rough condition on the original \(m\). Neither a sign on that remaining row nor the required \(.010M_N\) upper for it is asserted. In (2)--(3) this is a global replacement of the whole row, **not** a sectorwise equality with the old sharp coefficients or with a true-prime \(q\)-row.

## 1. Whole centered replacement with the moving cutoff

For each \(\alpha\) in the fixed support, set \(U_\alpha(m)=m^\alpha\) and \(V=\exp(L^\nu)\), and define
\[
 C_\alpha(m)=\sum_{\substack{d\ell\mid m\\d>m^\alpha,\ \ell>V}}\mu(d)\Lambda(\ell),
 \qquad
 P_\alpha(m)=-\sum_{a\mid m,\ a\le m^\alpha}
                         (\mu*\Lambda_{>V})(a).
\tag{4}
\]
There is no separate product cut: the literal product condition \(d\ell>m^\alpha V\) is automatic. As \(\alpha_1<1/2\), the relevant short product and modulus scales below have a fixed power margin. Writing \(\mathcal T_f(F)=\sum_{s,q}W_s(q)B_f(q)F(m)\), for each fixed \(D>0\) we have, uniformly in \(\alpha\),
\[
 \mathcal T_{\rm p}(C_\alpha)=\mathcal T_{\rm p}(C)+O_D(xL^{-D}),
 \quad \mathcal T_f(C_\alpha)=\mathcal T_{\rm p}(C_\alpha)+O_D(xL^{-D}),
 \quad \mathcal T_f(P_\alpha)=O_D(xL^{-D}).
\tag{5}
\]

For the first estimate, the exact divisor rearrangement on this central \(m>V\) is
\[
 C_\alpha(m)=\Lambda(m)
      -\sum_{d\mid m,\ d\le m^\alpha}\mu(d)\log(m/d)
      +\sum_{d\ell\mid m,\ d\le m^\alpha,\ \ell\le V}\mu(d)\Lambda(\ell).
\tag{6}
\]
All short progression moduli are \(\le (3x/2)^{\alpha_1}V\). The genuine semiprime convolution \(s q\) has full-scale generalized BV by [Maynard I, Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733), used as in [FullScaleConvolutionBV.md](FullScaleConvolutionBV.md). Nonunit moduli with respect to \(N\) cannot divide \(m\) on the actual support. The exact reduced mean at each physical \(n=sq\) carries the mask \((d\ell,Nn)=1\). In the first short piece the finite uniform \(\mu/\phi\) moments (11) of [UnmarkedSemiprimeWholeTypeI.md](UnmarkedSemiprimeWholeTypeI.md) give \(\mathfrak S(Nn)\), with \(\log(m/d)=\log(m/U_\alpha)+\log(U_\alpha/d)\). In the second short piece fix \(\ell\), use
\[
 \frac{1}{\phi(d\ell)}
       =\frac{1-p^{-1}1_{p\mid d}}{\phi(d)\phi(\ell)}
                           \quad(\ell=p^j,\ j\ge1),
\]
and apply the same log-small constant moment both with the unrestricted coprime \(d\) mask and with the squarefree factorization \(d=p d'\), \((d',p)=1\). All endpoints there remain \(\gg x^{\alpha_0}/V\); summing \(\Lambda(\ell)/\phi(\ell)\) costs only a fixed power of \(L\). Thus these are precisely the old matched short centers, the second one zero, with arbitrary log reserve.

Here the moving comparison \(d\le m^\alpha\) can be frozen in physical-mesh intervals of length \(O(xL^{-K})\) using the midpoint. For each short \(d\asymp x^\alpha\) an erroneous physical term requires \(|m-d^{1/\alpha}|\ll_{\alpha_0}xL^{-K}\) and \(d\mid m\). Summing the unweighted floor envelope gives \(O(xL^{-K}+x^{\alpha_1})\) physical pairs, before any extra \(\ell\) selections. To pay divisor or log weights and multiple \(s,q\) decompositions, apply Cauchy to the physical values \(m,n=N-m\) and their standard divisor moments, with \(K\) enlarged. For frozen reduced means, at each fixed \(m\) the boundary interval for \(d\) has length \(O(x^\alpha L^{-K})\) and weighted harmonic mass \(O(L^C(L^{-K}+x^{-\alpha_0}))\). For the \(\ell\)-piece use \(1/\phi(d\ell)\le1/(\phi(d)\phi(\ell))\) and its harmonic \(\ell\)-sum; no count of the \(V\) values without their divisor/harmonic weight is used. This also handles the moving \(a\le m^\alpha\) cutoff in \(P_\alpha\), now by putting \(d=a\), and the true visible \(W_s(q)\) via the original partial summation. Thus the BV assertion is only for fixed mesh endpoints.

For the second estimate in (5), first use a single reverse cutoff \(U_q=Y^u\) in the fixed support of \(\psi\) from [SmoothReverseCoreShield.md](SmoothReverseCoreShield.md); \(V_q=Y\), and third short-product term empty at \(U_qY\). The two reverse short terms have modulus \(A=se\le x^{.28}\). For fixed \(A\) use the entire (6) before any section: ordinary maximal prime BV disposes of \(\Lambda(m)\) after centering. In (6), if the short modulus \(a=d\) or \(d\ell\) shares a prime with \(AN\) then actual \(a\mid m\) is impossible in the unit progression \(m\equiv N\bmod A\). Otherwise CRT with \((m,N)=1\) gives density \(\phi(N)/(N aA)\) and floor \(O(\tau(N))\). For each fixed outer tuple the moving \(d\le m^\alpha\) is exactly the single interval end \(m\ge d^{1/\alpha}\), so use ordinary one-variable summation by parts; cutoffs in \(W_s/\log q\) and \(\log(m/d)\) do not change the absolute floor bound beyond fixed log powers. Even counting every tuple separately, the total floor is \(x^{\alpha_1+.28+o(1)}\). In the integrated density, at each physical continuum \(m\) use the same finite harmonic moments but for \(\mu(d)/d\), with mask \(AN\). Now \(\phi(N)/(NA)\) times the first harmonic main \(AN/\phi(AN)\) equals \(1/\phi(A)\), and the second has log-small mean. These are the ordinary coprime moments used in §1 of [WholePositiveSmallCore.md](WholePositiveSmallCore.md). This centers the reflected coefficient in both reverse short pieces. Proper prime powers in replacing actual \(q\) by \(\Lambda(q)/\log q\) are power-small with the physical divisor bounds. Average over \(u\).

For the third estimate in (5), apply full-scale convolution BV with actual short SW prime \(s\) and divisor-bounded \(B_f(q)\). The mean short coefficient at each \(n\) equals \(-\mathfrak S(Nn)+O_D(L^{-D})\) by equation (7) of [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md) with upper endpoint \(m^\alpha\). Its \(V\)-truncated terms retain polynomial coprime endpoints. The moving cutoff is handled by the same mesh and boundary estimate proved above. The resulting \(-\mathfrak S(Nn)\) times reverse \(B_f(q)\) has total \(O_D(xL^{-D})\) by the exact small-\(g\) reverse harmonic center and divisor tail in §1 of [SmoothReverseCoreShield.md](SmoothReverseCoreShield.md); that proof is uniform in the reverse averaging parameters. This proves (5) with no restrictions on either factorization.

## 2. The exact averaged coefficient, including small powers

Add the expressions in (4), and use \(\mu*\Lambda=-\mu\log\). Because for \(\ell\le V\) dividing central \(m\) we have \(m/\ell>1\), \(\sum_{d\mid m/\ell}\mu(d)=0\). The exact resulting identity, after averaging \(\alpha\), is
\[
\begin{split}
 \int (C_\alpha+P_\alpha)(m)\psi_m(\alpha)d\alpha
      &=\Lambda(m)+(\log m)\sum_{d\mid m}\mu(d)g_m(\log d/\log m)
                                      +E_\nu(m),\\
 E_\nu(m)&=\sum_{\substack{\ell\mid m\\\ell\le V}}\Lambda(\ell)
       \sum_{d\mid m/\ell}\mu(d)
       \{f_m(\log d/\log m)+f_m(\log(d\ell)/\log m)}.
\end{split}
\tag{7}
\]
Indeed the original high chain with \(d>m^\alpha\) yields the full \(\log(m/d)\) minus its short \(\ell\) tail; the latter negated high-tail is identical to the same short \(\ell\) term with \(d\le m^\alpha\) by the displayed zero. The switched \(P_\alpha\) contributes \(\mu(d)\log d\) on \(d\le m^\alpha\), and its own short positive correction requires \(d\ell\le m^\alpha\). These are the two separate cutoff functions in \(E_\nu\). In particular there is no missing nonzero term from a small square inside \(m\).

If \(m\) is prime, \(g_m(0)=-1,g_m(1)=0\), so the first two terms cancel **exactly**, and \(E_\nu=0\). Physical proper prime powers \(m\) have total weight \(x^{1/2+o(1)}\) even after all admissible \(s,q\) factorizations, by the divisor envelope. On other composites \(\Lambda(m)=0\) and the second term is (1). We show below that the entire \(E_\nu\) sum, in absolute value against the actual opened weights, is \(O(M_N L^{\nu-1})\). This cost is required because a tiny \(\ell\) might remove the last copy of its base prime from \(m/\ell\).

## 3. A uniform two-linear-form Fourier envelope

For real frequencies \(t,u\) define strongly multiplicative nonnegative functions
\[
       A_t(m)=\prod_{p\mid m}|1-e(t\log p/L)|,qquad
       A_{u,y}(q)=\prod_{p\le Y,\ p\mid q}|1-e(u\log p/\log Y)| .
\tag{8}
\]
There are even rapidly decreasing envelopes \(a_m(t),a_f(u)\), fixed in \(x\), such that the absolute divisor sum multiplying \(\log m\) in (7) is at most \(\int a_m(t)A_t(m)dt\); each of the two sums inside \(E_\nu\) is at most \(\int a_m(t)A_t(m/\ell)dt\). To see this, use Fourier inversion for \(g_m(\lambda v)\), \(f_m(\lambda v)\) or \(f_m(\lambda v+b)\) with \(\lambda=L/\log m\in[1/2,2]\), \(b=\log\ell/\log m\in[0,1]\). The shifts and dilations range over compact sets, so each frequency density has common Schwartz decay. Expand the finite Möbius divisor sum as the Euler product in (8). Absolute reference to frequencies removes the dependence of \(\lambda,b\) on the physical point. The same reasoning and (4)--(6) of [SmoothReverseCoreShield.md](SmoothReverseCoreShield.md) give
\[
                     |B_f(q)|\le\int a_f(u)A_{u,y}(q)\,du
\tag{9}
\]
after the same power-small removal of \(q\) with a prime power \(p^j>Y,p\le Y,j\ge2\). On the no-core branch \(A_{u,y}=1\) and \(|B_f|\le1\) (including the fully rough actual primes and powers); choose \(\int a_f\ge1\). On \(w=1\) of the nontrivial-core branch the coefficient is zero. Nothing is assumed about the sign of the surviving no-core term.

Here is the precise uniform measure bound used with these envelopes. Use [Henriot, Theorem 5 and Corollary 2](https://arxiv.org/pdf/1102.1643), with the [published 2014 erratum](https://doi.org/10.1017/S0305004114000280), in particular its corrected exceptional set \(p\mid a^*D^*\) including leading coefficients. Apply it to the two irreducible primitive linear forms below and the multiplicative two-variable function given by the appropriate factor from (8) in each coordinate, times the two exact \(N\)-unit masks. Both functions satisfy the \(\mathcal M_2(A,B,\epsilon_*)\) condition uniformly in all frequencies and cutoffs: their local values are at most 2, and \(2^{\omega(a_1)+\omega(a_2)}\ll_{\epsilon_*}(a_1a_2)^{\epsilon_*}\) with a fixed constant. The associated minimal function \(G\) of Henriot equals \(F\) by multiplicativity. We may set the short-interval parameter \(1/2\), height exponent \(1/10\), and \(\epsilon_*=1/10000\), which satisfy his stated inequality for total degree 2.

For fixed \(s\) use \((Q_1(v),Q_2(v))=(v,N-sv)\) on the literal \(q\)-interval of length \(X\asymp x/s\). More generally:
* If \(\ell\mid m\) is forced, with \(\ell\) a prime power \(\le V\) or a prime \(\le x^{.02}\), the unit support forces \((\ell,Ns)=1\). Choose \(0\le q_0<\ell\) with \(s q_0\equiv N\pmod\ell\); use \(Q_1(v)=q_0+\ell v\), \(Q_2(v)=(N-sq_0)/\ell-sv\). These are exactly \(q,m/\ell\).
* If \(\ell=p\le x^{.02}\) divides \(q\), use \(Q_1(v)=v,Q_2(v)=N-s p v\), thus \(q/p,m\), and \(p\nmid N\).

The starting argument and length in both switches are \(\asymp x/(s\ell)\gg x^{.83}\) for large \(x\), with the hypotheses \(x_0^{1/2}<y_0\le x_0\) satisfied by dividing this comparable interval into at most a fixed number of comparable pieces if necessary. Polynomial coefficient norms are \(O(x^{1.15})\), safely within \(x_0>C_0\|Q\|^{1/10}\). Both forms are primitive: in the first switch \((q_0,\ell)=1\) and the constant in \(Q_2\) is coprime to \(s\), since \((N,s\ell)=1\). In the second switch \((N,sp)=1\). They have nonzero determinant of absolute value \(N\) in all three cases. At \(p\mid N\), all nonzero valuation terms of Henriot's exceptional local multiplier vanish thanks to the two unit masks; at primes dividing a leading coefficient outside \(N\), only one of the forms has a root, simple. Thus the inert exceptional multiplier is \(O(1)\), even in the erratum: the latter primes are among the true \(s\) and the one prime base of \(\ell\), and each adds at most \(1+O(1/p)\). There is no unbounded \(\tau(N)\) or second singular-factor loss.

The sifting product \(\prod_{2<p\le x_0}(1-\rho(p)/p)\) is \(\ll\mathfrak S(Ns\ell)/L^2\), as there are two roots except at primes dividing \(Ns\ell\), where there is one. The factor 2 is harmless here and already omitted in the product. The remaining positive Euler products of Henriot are bounded by \(O((1+|u|)^2(1+|t|)^2)\). For (8) this is the Mertens split as in (7) of [SmoothReverseCoreShield.md](SmoothReverseCoreShield.md), with \(e(t\log p/L)\) instead of \(e(t\log p/\log Y)\) for the full \(m\) product. The reverse product has local value one for \(p>Y\), which costs only \(\exp(\sum_{Y<p\le x_0}1/p)=O_y(1)\). One may replace a single prime's local value in either factor by 1 at cost \(O(1)\), and the same estimates apply. Hence the affine shifted sum of the two envelopes over its full interval is
\[
       \ll_y \mathfrak S(Ns\ell)\frac{x}{s\ell L^2}
                                    (1+|t|)^2(1+|u|)^2 .
\tag{10}
\]
Here \(\ell=1\) denotes the original unswitched case. The genuine \(\Lambda(q)\) component in (4) is not removed by this positive envelope. This is only an upper bound for a nonnegative weighted sum.

## 4. Size and localization of the actual residual

For each \(\ell\le V\) with \(\Lambda(\ell)\ne0\), use the first switch in §3. Integrate the rapidly decreasing envelopes in (10). Adjoining the prime base of \(\ell\) or the true \(s\) alters \(\mathfrak S(N)\) by bounded factors. Since \(\sum_s1/s\ll1\), (7)--(10) imply
\[
          \sum_{s,q}|W_s(q) E_\nu(m)B_f(q)|
         \ll \frac{\mathfrak S(N)x}{L^2}
                  \sum_{\ell\le V}\frac{\Lambda(\ell)}\ell
         \ll M_N L^{\nu-1}.
\]
The already removed reverse power exceptions and forward proper powers have arbitrary log reserve via divisor bounds. This proves (2). Use (10) at \(\ell=1\) and the \(\log m\) in (1) for the \(O(M_N)\) total absolute mass.

If there is a prime \(p\le T\) dividing \(m\), sum over that marked prime and use the first switch \(\ell=p\). Extract the factor \(|1-e(t\log p/L)|\) from \(A_t(m)\); in the quotient \(m/p\), replace the local value at \(p\) by 1, **also if \(p^2\mid m\)**. Similarly if \(p\le T\) divides \(q\), use the second switch and extract \(|1-e(u\log p/\log Y)|\) (as \(T<Y\)); reset its local value in the quotient \(q/p\). The same bound (10) holds. The additional factor summed against \(1/p\) in the two cases is
\[
        \ll_y(|t|+|u|)\frac{\log T}{L},
]
by Mertens and the elementary bound \(|1-e(v)|\le2\pi|v|\). Integrating proves (3), including arbitrary repeated small factors without any separate deletion assumption.

After deleting that sector, a nonsquarefree \(q\) or \(m\) requires a repeated prime \(p>x^\epsilon\) and hence \(p^2\mid n\) or \(p^2\mid m\). The count of possible physical \(n\in I\) in this union is \(O(x^{1-\epsilon})\), by summing positive multiples; there are at most \(\tau(n)\) possible short prime labels. The original exact coefficients have fixed divisor-power envelopes (including (1) and (5) in the reverse shield), so this additional deletion is \(x^{1-\epsilon+o(1)}=o(M_N)\). This completes the stated localization. It is possible instead to take \(T=\exp(L^\eta)\) for an \(o(M_N)\) small-factor removal, but then a uniform bounded-rank statement is not made.

What remains is a signed bound for this **actual** polynomially rough row, not ordinary progression distribution of either individual factorization. The \(O(M_N)\) absolute estimate is not the needed \(.010M_N\) upper, and the forward smoothing changes the actual coefficient (and can reintroduce contributions from odd ranks near the smoothing zone). The already proved sharp-cutoff sign slices cannot just be added to this new row. No Goldbach conclusion follows here.

## Comparison and scope

The earlier [true-prime, one-side smooth bound](SmoothedActualVaughanRough.md) controls the subset with many tiny factors and leaves a log loss at the natural scale. Here the whole-row reverse opening and the independent reflected smoothing permit an absolute first-small-factor bound on both actual variables. Related 2026 methods include [Pham's mixed-rough and sharp boundary estimates](https://www.preprints.org/manuscript/202610.3061) and the [November 1+1.75 manuscript's finite sifting and smooth progression charts](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf); neither supplies a sign for this bounded-rank residual. This note uses the stated classical input theorems and does not adopt the claimed conclusions of those manuscripts.
