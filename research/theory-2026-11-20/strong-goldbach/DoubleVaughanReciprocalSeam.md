# Fixed-target double Vaughan III cancellation through the balanced product seam

Use the actual double residual (3) of [ReverseVaughanDoubleResidual.md](ReverseVaughanDoubleResidual.md), including its \(D<d\le2D\) dyads and all upper/lower cuts. Put
\[
 a=d\ell,\qquad A=s e,\qquad e=r\lambda,\qquad
      ah+A j=N,\quad ah\in N-I,\quad I=(x/2,x],\quad N=2x .
\]
Denote the dyadic scales of \(a,A\) by \(M,P\), their exponents by
\(b=\log_x M,\ c=\log_x P\), their sum by \(g=b+c\), and \(m_0=\max(b,c)\).
This note proves, with all actual coefficients and original \(1/\log(ej)\), arbitrary-log saving \(O_B(x(\log x)^{-B})\) for its balanced seam: for \(g\ge1\), any fixed closed subregion on which
\[
       .7g+.25m_0 < .85,\qquad .875g+.125m_0<1
\tag{1}
\]
with fixed positive reserves is admissible. A matching narrow region below \(g=1\) is also covered; (11) below gives the exact exponents there. For example the whole box \(b,c\in[.49,.51]\) works, including all of its supercritical part. In particular this is not the floor-error \(aA<x^{1-\epsilon}\) result: in the middle of the box \(aA\asymp x^{1.02}\), and most individual \(a,A\) pairs then have no free-variable point at all.

This applies on the ordinary high support of both opened prime sides. For instance \(\alpha=.14,\ \log_x d=.48,\ \log_x\ell=.03,\ \log_xr=.31,\ \log_x\lambda=.06\) gives \(b=c=.51\), \(e=x^{.37+o(1)}\) beyond reverse BV, and \(a=x^{.51+o(1)}\) beyond all prior forward estimates over this actual semiprime cell. Taking nearby exponents slightly below .51 gives a fixed positive-width interior supercritical box. The proof retains the true double signs, but does not bound the same residual on strongly imbalanced or much larger-product boxes.

## 1. Factor separation and units on the physical equality

For fixed \(D\) the cutoff \(e>E_D\) is constant in \(d\). Apart from a possible coupled outer cutoff on \(aA\), all arithmetic constraints are on either \(a\) or \(A\) after summing their literal factorizations. The \(a\)-weights are the actual
\[
 c_m(a)=\sum_{\substack{d\ell=a,\ d\sim D\\d>U,\ \ell>V,\ a>Q}}
                      \mu(d)\Lambda(\ell).
\tag{2}
\]
For each exact polynomial term of \(K_{P_3}(sq)\), retain the label powers of \(\log s/\log x\) in the \(A\)-weights. To separate the remaining \(1/\log q\), write
\[
 \frac{1}{\log(ej)}
   =\frac{1}{\log(x/s)+\log((N-ah)/x)} .
\]
On the supported \(N-ah\in I\) the second term in the denominator is bounded, and the first is \(\asymp\log x\). Expand in a finite geometric series to any fixed log precision. Each resulting term is exactly a factor in \(s\) times a smooth function of \(ah/x\) on the original central support. Error after summing is \(O_B(xL^{-B})\), \(L=\log x\), since at the physical equality \(m+n=N\),
\[
 \sum_{\substack{s\mid n\\s\sim S,\ s\ {\rm prime}}}|\kappa_s|\!
      \sum_{d\ell\mid m}|\mu(d)\Lambda(\ell)|
      \sum_{r\lambda\mid n/s}|\mu(r)\Lambda(\lambda)|
          \ll L^C\tau_2(m)\tau_2(n).
\]
The number of admissible prime \(s\)'s dividing \(n\) is \(O(1)\), and divisor moments bound the sum of the majorant by \(xL^C\). The same argument applies to the other finite smooth test families of the preceding notes. The sharp central product endpoints can then be smoothed at relative width \(L^{-F}\) for any fixed \(F\), with normalized derivatives bounded by fixed log powers: the edge has \(O(xL^{-F}+1)\) integers \(m\); Cauchy and the fourth divisor moment of both \(m,N-m\) give absolute error \(O(xL^{-F/2+C})\).

For each separated test write it as \(c_m(a)c_n(A)\Psi(ah/x)\). Here \(c_n(A)\) is the literal sum over \(A=s e\), \(s\) in the genuine prime band, with label weights and the actual coefficient
\(\sum_{r\lambda=e,\ r>U_q,\ \lambda>V_q}\mu(r)\Lambda(\lambda)\), \(e>E_D\). It has \(O(L^C)\) magnitude because the number of eligible \(s\)'s is \(O(1)\); the same is true of (2). If an additional free \(h\) cutoff is needed, work first on a dyad of \(h\), smooth its endpoints with arbitrary log reserve, and smoothly separate the resulting normalized ratio \(ah/(x)\) versus \(a\) dependence by Mellin. The displayed target requires no such cutoff. Restrictions \((a,N)=(A,N)=1\) are independent masks on their own slots, and \((a,A)=1\) holds on physical unit support: any common divisor would divide \(N\). Conversely, on these masks the remaining test \((ah,N)=1\) is exactly \((h,N)=1\).

Expand this unit indicator by \(\sum_{f\mid(h,N)}\mu(f)\). Since \(f\mid N\) and \(a,A\) are units, \(f\mid h\) on a physical term also implies \(f\mid n,m\) and \(f\mid j\). Truncate \(f\le\exp(L^{3/4})\) with arbitrary log accuracy at the physical equality. Indeed for fixed \(f\mid N\), using \(m=f u,\ n=f v\), Cauchy with the second divisor moment at scale \(x/f\) gives
\[
 \sum_{m+n=N,\ f\mid m,n} \tau_2(m)\tau_2(n)
                         \ll (x/f)\tau_2(f)^2L^C
\]
on the central ranges. This holds even if \(f\) is large, by the positive integer counts up to a constant multiple of \(x/f\); if that bound is below 1 there are no terms. Harmonic Rankin on \(f\mid N\) with exponent \(1/4\) gives the claimed tail (its Euler product is \(\exp(O(L^{1/2}))\) by splitting primes at \(L^2\)).

## 2. Actual Poisson and the exact zero term

For fixed \(f\mid N\) in this truncation, the progression for \(w=h/f\) is
\(w\equiv (N/f)\bar a\bmod A\). The positivity of \(h,j\) follows from the original smooth support. Thus its exact Poisson terms are
\[
 \frac{x}{f a A}\,\widehat\Psi\!\left(\frac{\nu x}{f a A}\right)
             e_A(\nu (N/f)\bar a),\qquad \nu\in\mathbb Z .
\tag{3}
\]
At \(\nu=0\), fix \(A,\ell\) and apply uniform coprime Mertens to the genuine \(\mu(d)/d\) in (2), with fixed \((d,A N)=1\) and sharp cutoffs. The original relation \(a\sim M\) and any extra product inequality \((aA)\gtrless x^\gamma\) (or a finite collection of such cuts) are ordinary intervals in \(d\) at fixed \(A,\ell\). Every nonempty interval lies within the \(D\)-dyad \(D\ge x^{.40}/2\). Partial summation of the coprime maximal estimate therefore gives arbitrary log saving in the harmonic \(d\)-sum, uniform in \(A,\ell\). The other sums have harmonic costs
\(\sum_A |c_n(A)|/A\ll L^C,\ \sum_\ell\Lambda(\ell)/\ell\ll L,\ \sum_{f\mid N}1/f\ll L^C\).
Thus the true zero contribution is \(O_B(xL^{-B})\), with no smallness condition on \(aA\).

## 3. Nonzero frequencies via the natural Bettin–Chandee scale

Take
\[
       T_D'=\max(1,\lceil x^\eta M P/x\rceil)
\]
for arbitrarily small fixed \(\eta>0\). A threshold at least \(x^\eta MP/x\), with the \(f\le e^{L^{3/4}}\) truncation above, dominates the natural length \(f a A/x\) by a fixed power \(x^{\eta-o(1)}\) even when \(MP<x\) (then a threshold of 1 only improves the ratio if \(x^\eta MP/x<1\)). By rapid decay every \(|\nu|>T_D'\) has arbitrarily high fixed power savings after summation. On each signed dyad \(|\nu|\asymp T\le T_D'\), the weight \(\widehat\Psi(\nu x/(f a A))\) in the dimensionless normalized variables separates via Mellin: as a function of \(u=(|\nu|/T)(M/a)(P/A)\) on a fixed compact interval it is smooth, with fixed derivatives \(O(L^C)\) uniformly even at large argument, by rapid decay of Fourier derivatives. Mellin \(L^1\) cost is a fixed log power. Powers from the inverse transform, and the separate \(1/a,1/A\) factors, preserve the coefficient norms after taking out \(x/(fMP)\). When a sharp \(aA\) cutoff is needed, the product indicator can be Mellin separated independently by truncated Perron at a half-integer threshold; since \(aA\) is an integer of polynomial size, a polynomial height as large as needed gives arbitrary power-small error and \(O(L)\) integral norm. The factors on \(a,A\) have bounded modulus after the real shift \(1/L\). This step does not affect the actual divisor restrictions in either grouped arithmetic coefficient.

For each such separated entry apply [Bettin–Chandee, Theorem 1, equation (1.2)](https://arxiv.org/pdf/1502.00769) directly:
\[
 \sum_{\substack{\nu\asymp T,\,a\sim M,\,A\sim P\\(a,A)=1}}
      u_\nu v_a w_A\,e_A((N/f)\nu\bar a)
 \ll_\epsilon
    \|u\|_2\|v\|_2\|w\|_2
    \left(1+\frac{|N/f|T}{MP}\right)^{1/2}
    \left((TMP)^{7/20}(M+P)^{1/4}
         +(TMP)^{3/8}(TM+TP)^{1/8}\right)x^\epsilon .
\tag{4}
\]
Negative signs of \(\nu\) may be treated separately. This is precisely the arbitrary-coefficient, \((a,A)=1\) bound of the cited theorem; no restriction to squarefree \(A\), smooth modulus, prime-variable character result, or averaged target is used. The three norms contribute \((TMP)^{1/2}L^C\). Crucially \(\vartheta=N/f\) is large but the **natural** frequency scale is proportional to \(f MP/x\), so the ratio in (4) is small on the relevant frequencies. Use \(T\ll x^{\eta+\max(0,g-1)}\). Compared with the target \(MP\) before the Poisson prefactor, the two exponents when \(g\ge1\) are at most
\[
        .7g+.25m_0-.85+O(\eta+\epsilon),\qquad
        .875g+.125m_0-1+O(\eta+\epsilon).
\tag{10}
\]
For \(g<1\), use \(T\ll x^\eta\) and
\((1+|N/f|T/(MP))^{1/2}\ll x^{(1-g+\eta)/2+o(1)}\).
The respective two exponents are then at most
\[
        .5-.65g+.25m_0+O(\eta+\epsilon),\qquad
        .5-.625g+.125m_0+O(\eta+\epsilon).
\tag{11}
\]
Thus every fixed closed subregion where the relevant exponents are negative works by taking \(\eta,\epsilon\) small. On \(b,c\in[.49,.51]\), (10) has worst first exponent \(-.0085\) and second at most \(-.04375\); for (11) the crude bounds \(g\ge.98,\ m_0\le .51\) already give strictly negative margins. The multiply-back prefactor is \(x/(fMP)\); the \(f\)-sum, all dyads, smoothing and transform integrals have only fixed log costs and preserve a power saving. This proves fixed-target arbitrary-log cancellation on the announced seam.

The source theorem already treats determinant equations in its Corollary 1. The contribution here is the application to the actual double prime-detection residual with its two sign coefficients, compatible cutoffs and exact zero-mode disposal, not an improvement of the arbitrary Kloosterman theorem. For comparison [Wright's partially fixed factor estimate, Theorem 2.1](https://arxiv.org/pdf/2604.25177) cannot simply improve this by freezing the actual \(s=x^{\alpha+o(1)}\): its inverse-length parameters then have product \(M(P/s)\), and its phase factor contains \(1+|N/f|T/[M(P/s)]\), not \(1+|N/f|T/(MP)\); moreover one must sum over all labels \(s\). The present proof does not need this or subdyadic interval claims.

The reciprocal inequalities reuse the same inverse-fraction input as [the Pan shoulder](PanSupercriticalShoulder.md) and [its centered extension](PanPolynomiallyRoughSurvivors.md). The new scope is the actual quotient/reflected double-Vaughan residual with its separate dictionaries, not another estimate for Pan's own divisor sum. [Arneth's October 2026 v1 abstract](https://zenodo.org/records/23504447) describes a related balanced Type II reduction with the fixed-even parity separation still open; the hosted PDF was not available in this comparison. No priority inference is made.

Beyond the seam, the untreated portion of (3) is the actual coupled double signed expression on the much larger or imbalanced boxes. Swapping h,j there leaves two Möbius weights, not two free factors. No bound for that portion, whole prime-mask asymptotic, or binary Goldbach positivity follows here.
