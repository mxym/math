# Two super-half Type II slices with signed cancellation in the true same-cofactor cell

We work on the literal Vaughan remainder in [SameCofactorVaughanCenter](SameCofactorVaughanCenter.md), equation (3), not on a new detector or on an averaged target. Two disjoint slices of that remainder vanish to arbitrary logarithmic precision, despite termwise absolute mass of order \(M_N (\log x)^{3/2}\) in each slice. Both use genuine \(s\) and the original prime-versus-balanced-semiprime quotient, and both require moduli greater than \(x^{1/2}\). The uncontrolled complement is still part of the same signed cell; this does not bound that cell's signed upper, much less the whole-low allowance.

## 1. Definitions and exact slices

Write \(N=2x\) even, \(I=(x/2,x]\), \(L=\log x\), \(Z=\exp(L^{1/4})\), \(R_Z(v)=1_{P^-v\ge Z}\) with the usual empty factor convention, \(V_0=\prod_{p<Z}(1-1/p)\), and \(M_N=\mathfrak S(N)x/(2L)\). In all formulas \(s\) is a true prime, \(\sigma=\log s/L\in[.10,.14]\), \(0<\delta\le .001\) is fixed, and
\[
 C_s(u)=1_{\{su\in I,\;P^-u>x^{.5-\sigma+2\delta},\;\mu^2(u)=1\}}
       \big[-\mu(u)-f(\log s/\log(su))\big],\qquad f(v)=(1-2v)^3 .
\]
Thus on support \(u\) is either prime or a product of two genuine distinct primes in the exact balanced band, and no \(n=su\) has two eligible marks \(s\). The old remainder is
\[
 \mathcal T_N=\sum_{\substack{s,u,d,\ell,k\\ d\ell k=N-su,\ d>x^{.2},\ \ell>x^{.2}}}
 C_s(u)1_{(su,N)=1}\,\mu(d)R_Z(d)\Lambda(\ell)R_Z(\ell k).
\]
This is simply the original \(r=\ell k\) grouped sum opened at its exact \(\Lambda\) label.

For the two rows of the table, let \(a\in(x^{A_-},x^{A_+}], B\in(x^{B_-},x^{B_+}]\) and \(\ell\in(x^{E_-},x^{E_+}]\). Require \(P^-B>x^{.090}\), \(\ell\) prime, and \(d=aB\). These restrictions define \(\mathcal T_{N,j}\) by selecting the corresponding summands of \(\mathcal T_N\), with no other deletion.

| \(j\) | \((A_-,A_+)\) | \((B_-,B_+)\) | \((E_-,E_+)\) | \((Q_1,Q_2,Q_3)\) slots | \(\log_x(d\ell)\) |
|---|---|---|---|---|---|
| 1 | \((.073,.089)\) | \((.187,.205)\) | \((.242,.252)\) | \((a e,B,\ell)\) | \((.502,.546]\) |
| 2 | \((.070,.089)\) | \((.232,.247)\) | \((.201,.205)\) | \((a e,\ell,B)\) | \((.503,.541]\) |

Here \(e\) will be a subpower roughness label, not a constraint on the original summands. Both slices have \(d,\ell>x^{.2}\). The grouping of \(d\) is unique: \(a\le x^{.089}\) is its full part supported on primes \(\le x^{.090}\), and \(B\) consists of all remaining prime powers. No exact prime powers need to be deleted in these products: \(\mu(d)=\mu(a)\mu(B)\) is valid with the two factors coprime. On the nonzero support \(B\) can be either prime or a distinct semiprime, because \(3(.090)>.247\). Also \((B,\ell)=1\): row 1 has \(B<\ell\); in row 2 equality is outside the ranges and \(B/\ell\le x^{.046}\) if \(\ell\mid B\), contradicting the cutoff on \(P^-B\) unless \(B=\ell\). The \(\ell\) bands are disjoint, so the slices are disjoint **as summands of the open identity**. Other \(\Lambda\) labels of the same physical integer may belong to the complement. The restriction that \(\ell\) is prime is literal, not an assertion about the other terms.

**Theorem.** For every \(D>0\), uniformly as \(N\) runs through large even integers,
\[
 \mathcal T_{N,1},\ \mathcal T_{N,2}=O_{D,\delta}(x L^{-D}).                     \tag{1}
\]
Let \(\mathcal A_{N,j}\) replace each summand in the corresponding expanded slice by its absolute value, *before* grouping back by \(n,m\) or \(r\). Then
\[
 \mathcal A_{N,j}=(c_{j,\delta}+o(1)) M_N L^{3/2},\qquad
 c_{j,\delta}=e^{-2\gamma}(A_+-A_-)(E_+-E_-)H_j J_{\delta}^{\rm abs}>0,          \tag{2}
\]
where \(\gamma\) is Euler's constant and
\[
 \begin{split}
 H_j &= \log(B_+/B_-)
     +\frac12\int_{\substack{v,w>.090,\ B_-<v+w<B_+}}\frac{dv\,dw}{vw},\\
 J_{\delta}^{\rm abs}
 &=\int_{.10}^{.14}\frac{(1-f(t))+
       (1+f(t))\log[(.5-2\delta)/(.5-t+2\delta)]}{t(1-t)}\,dt.
 \end{split}
\]
In particular (1) allows dropping both slices from \(\mathcal T_N\) with no cost at the calibrated \(M_N\) scale, not merely paying their absolute mass. It contracts the sum of absolute weights of the open remainder by precisely these masses, but does not assert reduction of an operator norm after grouping by physical integers. Neither slice includes a near-balanced configuration such as \(\log_x d=.49,\log_x\ell=.46\); the new distribution is not for arbitrary moduli or coefficients at these sizes.

## 2. Actual moving residue and three independent modulus slots

On the selected support \(aB\ell\) is \(Z\)-rough. For \(d\ell\mid m=N-su\), \(k=m/(aB\ell)\); its \(Z\)-roughness is exactly enforced by removing every prime \(<Z\) dividing \(m\), equivalently \(k\). Open this via odd/even Bonferroni depths near \(L^{1/4}\), with squarefree \(e\) supported below \(Z\) and \(e\le\exp(O(L^{1/2}))\). Every revealed condition is the actual
\[
                  su\equiv N\pmod{aB\ell e}.
\]
Any component sharing a prime with \(N\) has no physical row since \((su,N)=1\); enforce the coprimality on each modulus slot. Any \(p<Z\) cannot divide \(su\). As \(a\) is rough and \(e\) is fully supported below \(Z\), the coefficient of \(ae\) is exactly the product of the separate two coefficients under a unique factorization. It is 1-bounded for either choice of sieve depths; the other slots are 1-bounded after dividing the \(\Lambda(\ell)\) coefficient by \(L\). The same is true with the absolute-weight coefficients.

We apply [Lichtman, arXiv:2309.08522v1, Proposition 5.2](https://arxiv.org/html/2309.08522v1), not a fixed-residue theorem. In its notation our short factor is \(s\), so the log-length exponent of its \(N\)-slot is \(\sigma\). Our residue \(a_{\rm res}=N=2x\) is legal since \(|a_{\rm res}|<x^{1+\epsilon}\) for fixed \(\epsilon>0\) eventually. Denote the exponent bounds on its three modulus slots by \(q_1,q_2,q_3\) and put \(\theta=7/32\). The four strict rails before the tiny \(\epsilon\)-reserves are
\[
 q_1<\sigma,\quad 2\sigma+q_2+2q_3<1,\quad
 \theta+\sigma+q_1+5q_2+2q_3<2,\quad
 2\theta(\sigma+q_3-q_2)+\sigma+q_1+5q_2+2q_3<2.
\]
Here the tiny \(2\)-factor of the residue is swallowed by the reserves. Using separate worst endpoints (and ignoring \(o(1)\) from \(e\) and dyads), these are \(q_1\le.089<.10\) in both cases, and upper bounds respectively
\[
 (.989,1.97675,1.8476875),\qquad
 (.979,1.96675,1.829375)
\]
for the other three expressions. Thus e.g. \(\epsilon=10^{-4}\) leaves strict room for the printed \(8\epsilon,15\epsilon\) and all dyadic endpoint constants.

Here are details of separability on the genuine support. Use dyads in the factors and quotient \(u\), and subdivide each \(s\)-dyad into relative length \(L^{-K}\) bins. On a bin with frozen comparison endpoint \(s_0\), use \(s_0u\in I\), \(P^-u>x^{.5+2\delta}/s_0\), and replace \(f(\log s/\log(su))\) by \(f(\log s_0/\log(s_0u))\). Keep the *true* \(s\) in the residue, in the prime test, and in \((s,N)=1\). This leaves two independent source coefficients: prime \(s\) in a subinterval, and a bounded coefficient on \(u\), which needs no SW assumption. It is exactly the frozen prime/balanced-semiprime source with \((u,N)=1\) and its unchanged signs. The prime coefficient, including the restriction \(s\nmid N\), satisfies Lichtman's Definition 2.1 with an auxiliary coprime \(d_0\): classical prime prefix SW handles \(q\le L^C\); removing the primes dividing \(Nd_0\) costs \(O(L+\omega(d_0))\), admissible in (2.2); larger \(q\) use the trivial \(S/q+1\) bound and \(\phi(q)\gg\sqrt q\), with \(C\) depending on the requested log power. Also \(s\ge x^{.10}>x^{1/(\log\log x)^3}\) eventually. All coefficient amplitudes are bounded by an absolute constant (divide by it before using Proposition 5.2). Source dyads satisfy \(S U\asymp x\), since \(su\asymp x\) on both the original and frozen supports.

The endpoint error on \(su\in I\) has \(O(xL^{1-K}+x^{.14})\) unweighted rows by counting at fixed \(s\). The only other changed incidence requires a true prime factor \(p\) of \(u\) in a relative \(O(L^{-K})\) strip around \(x^{.5+2\delta}/s\). Here only the balanced semiprime qualifies, so write \(u=pv\) and count first \(p\) as an integer in that strip and then \(v\le x/(sp)\) as an integer. The count summed over \(s\) is \(O(xL^{1-K}+x^{.64})\); the \(+1\) from each strip gives at most \(O(x^{.5-2\delta})\) per \(s\). There is only one physical small mark even in the frozen support, since all the quotient factors are \(\gg x^{.36}\), and the quotient factorization is unordered and unique when it is semiprime. The weights of the opened divisor rows above a given \(m\) are bounded by \(L\tau(m)^{O(1)}\), including the Bonferroni truncations. Cauchy with global fixed divisor moments gives arbitrary-log small errors on both removed strips by choosing \(K\) sufficiently large. The error of freezing the smooth \(f\) is \(O(L^{-K-1})\) times the same global moment. For the proposed principal, absolute harmonic sums over the opened modulus factors cost only log powers, so the same endpoint repairs apply there without even Cauchy. Fine bins and dyads multiply the count of applications of Proposition 5.2 by only a fixed log power, absorbed by its arbitrary log savings.

We conclude that the physical terms with \(R_Z(k)\), for either the signed or absolute weights, can be replaced by the pointwise coprime principal
\[
 1_{(su,N)=1}\frac{1_{(aB\ell,Nsu)=1}}{\phi(a)\phi(B)\phi(\ell)}V_N(Z),\qquad
 V_N(Z)=\prod_{\substack{p<Z\\p\nmid N}}(1-1/(p-1)).                         \tag{3}
\]
Indeed \(a,B,\ell,e\) are pairwise coprime, and \(e\) is coprime to \(su\) automatically. The exact odd and even Bonferroni gap is bounded first with **nonnegative** coefficients (the absolute/source envelope and absolute modulus coefficients use all the same independent slots). Its main gap is bounded by \((O(\log L))^h/h!\) at the chosen depth \(h\asymp L^{1/4}\), times at most a log power from the modulus harmonics, and its progression errors again are arbitrary-log-small. The omitted higher orders from the finite Euler product have the same bound. This proves (3) to total \(O_{D,\delta}(x L^{-D})\), without a signed fundamental-lemma assumption.

## 3. Signed and absolute principal evaluations

For fixed physical \((s,u)\) put \(F=Nsu\). In (3) the \(a\)-sum for the signed slice is exactly
\[
             \sum_{\substack{x^{A_-}<a\le x^{A_+}\\(a,F)=1}}
                     \frac{\mu(a)R_Z(a)}{\phi(a)} .
\]
By the uniform rough harmonic estimate (5) of [SameCofactorVaughanCenter](SameCofactorVaughanCenter.md), applied at both polynomial endpoints, it is \(O_D(L^{-D})\); that estimate comes from Huang--Li Lemma 1 and an inverse small-prime Euler convolution, not by pretending that the small primorial is a polynomial-size masked conductor. All other harmonic sums have size at most a log power, and the factorization in (3) does not depend on the parity of \(a\). This proves (1).

For absolute weights the required uniform \(a\)-sum instead equals
\[
 \sum_{\substack{x^{A_-}<a\le x^{A_+}\\(a,F)=1}}
       \frac{\mu^2(a)R_Z(a)}{\phi(a)}
     =(A_+-A_-)L\,V_0(1+O(L/Z))+O_D(L^{-D}).                         \tag{4}
\]
To check it, convolve \(f_0(n)=\mu^2(n)nR_Z(n)1_{(n,F)=1}/\phi(n)\) with \(\mu\), writing \(g=f_0*\mu\). At an admissible prime \(p\), the nonzero local values beyond \(g(1)=1\) are \(g(p)=1/(p-1)\), \(g(p^2)=-p/(p-1)\); at excluded primes just \(g(p)=-1\). At Rankin exponent \(\eta=1/\log Z\) the Euler sum \(\sum |g(b)|b^{-1+\eta}\ll L^{1/4}\): the admissible primes have absolute convergent factors uniformly, the \(p<Z\) factors have extra log sum \(O(\sum_{p<Z}(p^\eta-1)/p)=O(1)\), and there are \(O(L)\) large excluded primes, each costing \(O(1/Z)\). For \(b>\exp(L^{1/2})\) this gives an exponential tail. For the rest, opening \(f_0=g*1\) gives the ordinary harmonic interval \((x^{A_-}/b,x^{A_+}/b]\) of main \((A_+-A_-)L\) with error \(O(b/x^{A_-})\). The exact Euler product \(\sum g(b)/b\) is \(\prod_{p\ \mathrm{excluded}}(1-1/p)\), since the admissible local factors are exactly 1. This proves (4) without fixing the rank of \(a\) or suppressing repeated powers in \(k\).

Prime Mertens and PNT on the fixed bands give \(\sum_B\mu^2(B)1_{P^- B>x^{.090}}/\phi(B)=H_j+o(1)\) and \(\sum_\ell\log\ell/\phi(\ell)=((E_+-E_-)+o(1))L\) on the stipulated ranges. For \(B\) this is the disjoint prime and unordered distinct semiprime decomposition: the prime harmonic density is \(dt/t\) on log exponents, the two distinct prime harmonic measures converge on the simplex strip, and its boundary has zero measure. The unit masks \((B\ell,F)=1\) remove only a uniformly power-small weighted contribution: for primes \(p\mid F\) in those bands open their multiples in \(B\) (at most one other factor, with bounded prime harmonic sum) or the prime term \(\ell=p\), costing \(O(L^{O(1)}x^{-.090})\). On the source side the same quotient PNT calculation that gives equation (1) of SameCofactorVaughanCenter with its local reference removed yields
\[
               \sum_{s,u}|C_s(u)|1_{(su,N)=1}
                    =(J_{\delta}^{\rm abs}+o(1))\frac{x}{2L}.
\]
The prime score is positive, the balanced-semiprime score negative; thus the plus sign in \(J_{\delta}^{\rm abs}\) is necessary. The \(N\)-unit deletion is power-small because every source prime is \(\ge x^{.10}\). Finally \(V_N(Z)/\mathfrak S(N)=V_0(1+O(L/Z))\) uniformly, by the tail of the Goldbach Euler factors, and Mertens gives \(V_0\sim e^{-\gamma}L^{-1/4}\). Multiplying these genuine unsigned principal factors proves (2).

The earlier full Type I identity applied product BV at fixed \(s\) below the square root of the shorter \(u\) scale. The present application uses the full scale \(su\asymp x\), real \(s\) as the SW variable and explicit three-way factorization of these portions of its true Type II modulus \(d\ell\). There is no assumption that unrestricted Type II admits this grouping: in particular the other portions may have large irreducible \(d\) and \(\ell\), or no independent arbitrary-rank rough core \(a\). Arneth Gold-42 and Pham Oct 30 are compared in the preceding SameCofactorVaughanCenter note; no Type II theorem has been imported from either.

[check_same_cofactor_typeii_rough_core.py](check_same_cofactor_typeii_rough_core.py) checks all rail vertices and the local harmonic factors by exact rational arithmetic.
