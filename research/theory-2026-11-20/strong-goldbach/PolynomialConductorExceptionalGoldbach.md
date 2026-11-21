# Polynomial-conductor extension of the exceptional Goldbach criterion

**Literature status (2026-11-21).** These implications are retained as conditional calculations, not as coverage of any large even target. [Banks, Theorem 1.1 (October 2026)](https://arxiv.org/abs/2610.15483v1) gives a positive uniform lower bound for `(1 − β) log q₀` for primitive real Dirichlet characters; see also [Kerr's simplification](https://arxiv.org/abs/2610.21099v1). In the small-conductor window this product is bounded above by `c Δ₀ / √log N`; in the polynomial-conductor window it is at most `κ (log N)^(−A)` for fixed positive `A`. Both tend to zero. Thus Banks's result rules out the hypotheses for all sufficiently large `N`. This is independent of RH/GRH and does not settle ordinary binary Goldbach.

This extends the small-conductor result in [SmallConductorExceptionalGoldbach.md](SmallConductorExceptionalGoldbach.md). It does not assume the existence of a zero, prove the ordinary-no-exception case, or resolve binary Goldbach in general.

**Conditional theorem.** For any fixed \(A>0\) there exists an absolute \(\kappa=\kappa(A)>0\) (very small) such that, for all sufficiently large even \(N\), if a primitive quadratic character \(\chi\) of conductor \(q_0\) has a real zero \(1-\delta\) with
\[
             q_0\le N^\kappa,\qquad \Delta:=\delta\log N\le(\log N)^{-A},
 \tag{1}
\]
and if \(\chi(a)\chi(N-a)=-1\) on every doubly reduced class modulo \(q_0\), then \(N\) has a Goldbach representation with both primes in \((N/3,2N/3)\). The lower bound with log-weight on the majority prime is \(\gg \delta N\mathfrak S(N)\). In conjunction with Matomäki–Merikoski Theorem 1.4, the same existence conclusion (without a central restriction for that theorem's targets) holds for every sufficiently large even \(N\) in the window (1), including the other local strata. References to equation numbers without an explicit qualifier below are to the named small-conductor note.

## 1. A collective prime explicit formula, with the necessary relative reserve

Fix a desired exponent \(J\ge1\). There are \(\upsilon>0\), \(c_1>0\) such that the following holds at scale \(X\) if \(\delta\log X\) tends to zero and \(q_0\le X^{\upsilon/10}\). For a primitive character \(\psi\bmod f\), define
\[
 \mathcal E_X(\psi)=
 \sup_{X/4\le y\le 4X}
  \left|\sum_{n\le y}\Lambda(n)\psi(n)
    -1_{\psi=\mathbf1} y
    +1_{\psi=\chi}\frac{y^{1-\delta}}{1-\delta}\right|.
\]
The sum is over genuine primitive characters, including conductor 1. Then
\[
 \sum_{f\le X^{\upsilon/10}}\ \sum_{\psi\bmod f}^{*}\mathcal E_X(\psi)
       \ll X\big[(\delta\log X)^J+X^{-c_1}\big].                        \tag{2}
\]
This is a **collective** bound, not the weaker uniform maximum over individual characters followed by a count of their possible conductors.

To prove it, take \(T=X^\upsilon\), \(Q=\lceil 3T\rceil\), and use [Thorner–Zaman, arXiv:2208.11123v4](https://arxiv.org/pdf/2208.11123v4), Theorems 2.6 and 2.15 and Corollary 6.1. Their exceptional zero is the given one for all sufficiently large \(X\): it lies in their unique exceptional strip since \(\delta\log Q=o(1)\). The bound in Theorem 2.15 requires the exceptional conductor \(>400000\); this follows from their Lemma 2.2, or from the fact that finitely many fixed conductors do not have zeros tending to 1. With \(T\) in their theorem set to \(Q\), its denominator is \(104.645+70.996\log Q\), and the multiplier of \(\delta\) inside the numerator is \(670564.676+454935.78\log Q\). Thus for sufficiently large \(X\), every other zero with real part \(>1/2\) and height at most \(2T\) satisfies, for example,
\[
             (1-\beta)\log X\ge \frac{\log(1/(\delta\log X))}{200\upsilon}.
 \tag{3}
\]
For these constants, for large \(X\) the denominator is at most \(80\upsilon\log X\), and \(\log(1/(\delta(670565+454936\log Q)))\ge0.4\,\log(1/(\delta\log X))\); the slightly sharper limit \(70.996\) also leaves slack. Since \(\delta\log X\to0\), all fixed losses here are eventually harmless. Their unconditional Corollary 6.1 counts all primitive zeros at conductor and height \(\le Q\) and real part at least \(\sigma\) by \(O(Q^{127(1-\sigma)})\), uniformly for \(\sigma\in[3/5,1]\). Integrating \(X^\sigma\) against this counting bound, with the hard endpoint (3), gives
\[
 \sum_{\substack{f\le X^{\upsilon/10}\\\psi\bmod f\ {\rm prim.}}}
 \ \sum_{\substack{\rho\ne1-\delta,\ |\Im\rho|\le2T\\\Re\rho\ge3/5}}
          X^{\Re\rho}
 \ll X \exp\!\left(
       -\frac{1-130\upsilon}{200\upsilon}\log(1/(\delta\log X))\right).
 \tag{4}
\]
For clarity, put \(g=\log(1/\Delta_X)/(200\upsilon\log X)\) with \(\Delta_X=\delta\log X\). If \(1-g<3/5\) the sum is empty. Otherwise the endpoint estimate and the integral \((\log X)\int_{3/5}^{1-g}X^\sigma Q^{127(1-\sigma)}d\sigma\) are both bounded by the right side of (4), absorbing constants and using \(Q^{127}\le X^{130\upsilon}\) for large \(X\). Choose \(\upsilon\) so small that \((1-130\upsilon)/(200\upsilon)>J\).

A truncated Perron contour only needs zeros with \(\Re\rho\ge3/5\), where \(1/|\rho|\le5/3\). To see the uniform error rather than count a possible reflected zero near 0, for each primitive character choose a horizontal cutoff in \([T,2T]\) a distance \(\gg1/\log(fT)\) from zero heights in that range, and a left vertical line in \([3/5,2/3]\) a distance \(\gg1/(T\log(fT))\) from real parts of zeros with \(|\Im\rho|\le2T+1\). Both choices follow from the standard local zero count (respectively \(O(\log(fT))\) per unit interval and \(O(T\log(fT))\) overall); on the horizontal lines the logarithmic derivative is \(O(\log^C X)\) and on the vertical line \(O(T\log^C X)\) by the local partial-fraction formula. Positive and negative heights may be chosen separately, or simultaneously avoiding both sets. Truncated Perron at half-integer endpoints and those lines yields error \(O((X/T+X^{2/3}T)\log^C X)\) per character, uniformly on \(y\asymp X\). The usual endpoint change to an arbitrary \(y\) costs \(O(\log X)\). Summing over \(O(X^{\upsilon/5})\) primitive characters leaves \(O(X^{1-c_1})\), with \(c_1=\upsilon/2\) permissible for small \(\upsilon\). Separating the pole and the exceptional zero from the remaining crossed zeros, (4) proves (2). No part of this calculation invokes Dirichlet GRH.

## 2. High-conductor and cutoff errors in the actual main

Use the real Dirichlet-zero lower bound \(\delta\gg q_0^{-1/2}(\log(2q_0))^{-2}\) as in the base note. Under (1),
\[
                 \delta^{-j}\le N^{j\kappa/2+o(1)}
       \quad\text{for each fixed }j.                                  \tag{5}
\]
All parameters can be chosen successively as follows. Take sufficiently large \(J\) (depending on \(A\) and the log losses below), then the \(\upsilon\) in (2); take the signed ABL cutoff \(R=N^\omega\) with \(0<\omega<\upsilon/100\) and in the allowed ABL high-character range; take \(\eta>0\) with \(40\eta<\omega/11\) as in the base note, and \(0<\epsilon\ll\eta\) for its fixed dimension-two sieve. Finally take \(\kappa\) sufficiently small depending on all of these, with \(\kappa<\epsilon\upsilon/100\) and with fixed slack in the other comparisons below. We may use standard fundamental-lemma weights of size at most 1, so the exponents of the polylogarithmic factors from fixed divisor moments do not grow as these positive power exponents decrease.

Keep \(D=N^\eta,\ z=N^\epsilon\), the \(d=u v\) decomposition, \(w=[u,k]\), and the cutoff \(u\le N^{10\eta}\) from §2 of the base note. All conductor primes are \(<z\); \((w,q_0)=1\), \((v,q_0w)=1\) remain exact. In the high-conductor term one may still split **all** allowed prime residues modulo \(q_0\), as its bound has a power reserve. Use auxiliary \(c_1=d_1=q_0 w\) in (3) of the base note; in particular \(d_1\mid c_1^\infty\), and all residues chosen are reduced. The cost \(N^{33\eta+o(1)}\) previously written now becomes \(N^{33\eta+3\kappa+o(1)}\): the factor \(c_1^2\) from the estimate and the modulus partition costs \(q_0^2\), and choosing the prime residue costs at most \(q_0\). The auxiliary exponent is still within the fixed polynomial ABL allowance. The transfer to a dependent hyperbola cutoff uses a mesh of length \(N\delta^2 L^{-C_0}\), where \(L=\log N\) and \(C_0\) is a sufficiently large fixed constant. The number of endpoints is \(O(\delta^{-2}L^{C_0})\) and its floor error is \(O(N\delta^2 L^{-2}+N^{1/2+\eta+o(1)})=o(\delta N)\), by the same \(\sum |w_k|/[d,k]\) harmonic bound as before. By (5) the total high error, after this mesh, is
\[
     N^{\,1-\omega/11+33\eta+4\kappa+o(1)}=o(\delta N)
\]
with margin by shrinking \(\kappa\). The discarded \(u>N^{10\eta}\) part is still \(N^{1-9\eta/2+o(1)}\), and the continued harmonic tail on \(u\le N^{10\eta}\) now costs \(O(N^{1-1/2+10\eta+\kappa/2+o(1)})\) (the Pólya–Vinogradov parameter \(\sqrt{q_0}\) is no longer subpower). Both are \(o(\delta N)\). The elementary integer comparison now has at most \(N^{1/2+\eta+\kappa+o(1)}\) floor error, also sufficient.

## 3. Exact finite character reduction for the low ABL conductors

Do **not** sum the low-conductor errors over the \(q_0\) residue classes in absolute value. On units modulo \(q_0\), the indicator of admissible majority residues is
\[
    \frac{1-\chi(a)}{2}
       \begin{cases}
           1,&3\nmid q_0\text{ or }3\mid N,\\[2pt]
           (1+\varepsilon_3\chi_3(a))/2,&3\mid q_0,\ 3\nmid N,
        \end{cases}                                                   \tag{6}
\]
where \(\chi_3\) is the unique nonprincipal character modulo 3 and \(\varepsilon_3\) selects the one remaining reduced class. Indeed \(N-a\) is automatically a unit at every prime dividing both \(q_0\) and \(N\). The base note's exact local ratio proves that every prime factor of \(q_0\) except possibly 3 divides \(N\); this includes 2 for any conductor with 2-adic exponent 2 or 3. Thus no further filtering on the odd unit classes modulo 4 or 8 is introduced; their exceptional character dependence is retained exactly in \((1-\chi(a))/2\). The expansion (6) has at most four \(q_0\)-characters, each with coefficient of absolute value at most 1 (coincident terms can be combined). In particular the principal coefficient is \(\nu/\varphi(q_0)\), and the \(\chi\)-coefficient is \(-\nu/\varphi(q_0)\).

By CRT the character modulo \(q_0 w\) factors into a \(q_0\)-character and a character modulo \(w\). After summing accepted residues by (6), only that fixed finite list remains on the \(q_0\) side. Let the primitive conductors outside \(q_0\) be \(s_*\mid w,\ r_*\mid v,\ r_*\le R\); they are coprime to each other and to \(q_0\). Induction as in (7) of the base note, now with just \(w\) in place of \(d_1=q_0w\), bounds the total coefficient of each resulting primitive character by
\[
 \ll L^{O(1)}\,\frac{\tau(s_*r_*)^{O(1)}}{\varphi(s_*r_*)}
       \ll L^{O(1)}.
\]
The last inequality is uniform over all integers: for any fixed divisor power its ratio to \(\varphi(n)\) is bounded. Summing over splittings of \(s_*r_*\) adds another fixed divisor power. The product conductor remains the honest product of the fixed \(q_0\)-part's conductor and \(s_*r_*\); these are coprime, so the full primitive character and the choice of \(q_0\)-part determine the primitive character outside \(q_0\). There are at most four choices for that part, even when it has conductor 1, \(3\), \(q_0\), or \(q_0/3\). Thus there is no hidden factor \(\varphi(q_0)\) when converting the weighted error to the unweighted family bound (2). With \(\omega+11\eta+\kappa<\upsilon/10\), all these primitive conductors fit (2) at \(X\asymp N\) after leaving exponent slack. The imprimitive corrections (prime powers at primes dividing the modulus) cost a power saving by the same direct count of pairs of moduli as in the base note. No class-count loss is needed in these corrections either; even the old polynomial class-count would be harmless here.

It follows that the entire low error, with all endpoint choices for the mesh counted, is
\[
          \ll N \delta^{-2} L^{C_2}
               [\Delta^J+N^{-c_1}]+N^{1-c_2}
             =o(\delta N).                                            \tag{7}
\]
Here \(C_2\) is fixed from the harmonic divisor induction and the mesh, and \(c_2>0\) can be chosen before shrinking \(\kappa\). Indeed dividing by \(\delta N\) makes the first term \(L^{C_2+3}\Delta^{J-3}\), negligible if \(A(J-3)>C_2+4\), and the second power term is negligible by \(\kappa\ll c_1\). The exact principal and exceptional coefficients from (6) give the same retained density \(1+t^{-\delta}\) in (4) of the base note. Therefore the prime sieve main and the integer comparison there are valid to relative precision in the larger window. In particular the Euler ratio \(\mathfrak S(N)(1+O(1/z))\) and \(A_{\rm rough}\gg\delta N\mathfrak S(N)\) are unchanged. The minority prime lower bound in the integer comparison follows directly from (2) for just the principal and \(\chi\) characters, so it uses no sum over \(q_0\) classes.

## 4. Short switched scales

The harmonic minority estimate (11) in the base note follows directly from [Matomäki–Merikoski v2, Lemma 4.1](https://arxiv.org/html/2112.11412v2#S4): its lower prime cutoff \(q_0^{1/2+\xi}\) is smaller than \(z=N^\epsilon\) for a fixed \(\xi>0\) when \(\kappa\ll\epsilon\), and its right hand side is \(O(\delta\log N)\). Thus the cofactor harmonic sum stays \(O_\epsilon(\Delta)\).

For a fixed \(r\) in the switched composite estimate, \(X=N/r\gg z\). Use an upper sieve of level \(X^{\upsilon/100}\) and threshold \(X^{\upsilon/2000}\) on the linear form \(p=N-rs\), retaining the actual varying prime \(s\) with \(\chi(s)=+1\). Both exponents are now fixed positive constants and their ratio is large enough for the dimension-one upper sieve. Keep the same local exclusion of primes dividing \(rNq_0\), the same Goldbach factor and reduced class \(b=N\bar r\bmod d\) as in §5 of the base note. For each modulus \(d\), instead of expanding over all minority residues modulo \(q_0\), use the **exact** character filter \((\chi_0+\chi)/2\) on \(s\) after orthogonality modulo \(d\). Since \((d,q_0)=1\), the primitive outside conductor \(s_*\mid d\) is unchanged. Summing upper-sieve coefficients with the inducing weights costs \(L^{O(1)}\tau(s_*)^{O(1)}/\varphi(s_*)\ll L^{O(1)}\), and the two possible fixed \(q_0\) components are the principal character or \(\chi\). The whole family (both components) is thus handled by (2) at scale \(X=N/r\), since \(q_0\le X^{2\kappa/\epsilon}\) for large \(N\), and \(2\kappa/\epsilon+\upsilon/100<\upsilon/10\). Prime powers and imprimitive corrections are again power-small, since the modulus family is of tiny fixed polynomial size.

For each \(r\), the additive error is
\[
    \ll X L^{C_3}\big[(\delta\log X)^J+X^{-c_1}\big]
        =o(\delta X)
\]
uniformly: \(\log X\asymp_\epsilon L\), \(A(J-1)>C_3+2\), and \(\kappa/2<\epsilon c_1/2\) with slack in (5). This is stronger than necessary; there is no \(\delta^{-2}\) mesh at this step because the endpoints of the \(s\)-interval are fixed once \(r\) is fixed. The total error again carries \(X=N/r\) and sums harmonically over cofactors. Accordingly the bound \(O_\epsilon(\Delta\,\delta N\mathfrak S(N))\) for every squarefree composite remains valid, and rough squareful terms are power-small because \(\kappa\ll\epsilon\). Since \(\Delta\to0\), the positive prime remainder survives as before.

For the soft local strata, write \(V=\log N/\log q_0\), \(\eta_{\mathrm{MM}}=V/\Delta\). Theorem 1.4 of [Matomäki–Merikoski v2](https://arxiv.org/html/2112.11412v2) applies with \(V\ge 1/\kappa>10\). Its error relative to \(N\mathfrak S(N)\) is \(O(e^{-C\sqrt{V\log \eta_{\mathrm{MM}}}}+e^{-CL^{3/5-\epsilon'}}+\Delta(\log\eta_{\mathrm{MM}})^6)\). The last quantity tends to zero: for fixed \(V\ge10\), \(u[\log(V/u)]^6\) is increasing for sufficiently small \(u\), and at \(u=L^{-A}\) it is \(O_A(L^{-A}(\log L)^6)\) since \(V\le L/\log 3\). The first two errors also tend to zero. By their exact local product, \(1+C_\chi(N)\ge2/3\) unless it is zero; hence their theorem supplies existence for the targets outside our hard stratum. We use no assertion about the existence of real zeros, nor about the binary problem outside (1).
