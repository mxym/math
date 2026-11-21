# All-rank control of the steep taper and the remaining coupled debt

Use the fixed-target \(N=2x\) physical rows and the two actual \(\mathcal Q_i\) quotient profiles of [AdjustedTriprimePositiveBudget.md](AdjustedTriprimePositiveBudget.md), with their exact positive multiplier \(D_B(q)/\log q=i\). Use the original reflected \(C\) and the smoothed short divisor \(G\) of [AdjustedPolynomialRankAbsorption.md](AdjustedPolynomialRankAbsorption.md). For this proposition the power and flattening parameters of \(G\) are merely fixed; they need not increase with the rank. Write
\[
 A_j(m)=\sum_{d\mid m}\mu(d)(1-2\log d/\log m)_+^j
 \quad(j\ \text{odd},\ j\ge9).
\]
Write \(\sum_{\mathcal Q_i}\) for the actual physical sum including the \(s\)-prime, equation, units, and central bounds \(n=sq\in(x/2,x]\), \(m=N-n\). There is an absolute constant (depending only on the original fixed profile bounds) for which
\[
 \boxed{\quad
   \limsup_{x\to\infty,\ x\in\mathbb Z}
   \frac1{M_{2x}}\sum_{\mathcal Q_i}
          W_s(q)\frac{D_B(q)}{\log q}\frac{\log m}{2j}
                          (A_j(m))_-
       \ll j^{4/\pi-2},\qquad i=1,2 .
       \quad}
\tag{1}
\]
All reflected ranks and repeats are included. The limit order is fixed \(j\), then \(x\to\infty\). In the original whole signed \(\mathcal Q_i\)-profile, after the shift of the polynomial-rank note, one may use the exact arithmetic form
\[
       \Lambda(m)-\log m\left\{\frac{A_j(m)}{2j}
                         +\left(1-\frac1{2j}\right)G(m)\right\}
\tag{2}
\]
at total \(o(M_N)\) error, provided \(j(1-\sigma)>3\), where \(H=\exp((\log x)^\sigma)\), \(0<\sigma<1\). This pays the **negative part of the first taper** in (2) arbitrarily cheaply by taking \(j\) large. The second flat taper cannot be paid independently in this fashion, as §3 shows.

## 1. Exact one-variable arithmetic and the whole short differences

As usual let \(C'_U(m)=\sum_{d\mid m,d>U}\mu(d)\log(m/d)\). Here one can replace \(C\) by \(C'_U\) on the **whole** actual \(\mathcal Q_i\) profile, rather than taking their pointwise difference in any rank. Their difference is the short term \((\mu_{\le U}*\Lambda_{\le V}*\mathbf 1)(m)\) minus the sum over \(d>U,\ell>V,\ d\ell\le Q_0\) of \(\mu(d)\Lambda(\ell)\); an isolated \(\Lambda_{\le V}(m)\) vanishes in the central window. The exact true moduli are at most \(UV\) or \(Q_0\), both below \(\sqrt x\) by arbitrarily many log powers. Apply the actual \(s\times q\) generalized BV in §1 of the polynomial-rank note, using SW on the genuine prime \(s\), with the actual whole \(\mathcal Q_i\) mask. For the reduced main fix \(\ell=p^k\) and the actual source \(n=sq\), and retain the mask \((d\ell,Nn)=1\). The overlap is the exact factor \(1-p^{-1}1_{p\mid d}\) in \(\phi(d)\phi(\ell)/\phi(d\ell)\). Thus the finite coprime \(\mu/\phi\) constant moments at \(U\) or between \(U\) and \(Q_0/\ell\) give arbitrary inverse-log reserve; split the \(p\mid d\) piece with its usual additional coprime mask and power-tail argument as in [FullScaleConvolutionBV.md](FullScaleConvolutionBV.md), §3. In fact for \(\ell\le V\) the overlap prime is subpower, so all surviving harmonic endpoints after division by \(p\) are polynomial. In the second term \(d>U,\ d\ell\le Q_0\) implies \(\ell<Q_0/U=H^2\), so the same assertion holds there. The outer harmonic \(\ell\)-sums cost log powers only. Hence the whole replacement error is \(O_A(xL^{-A})\) for every fixed \(A\), without a rank restriction or pointwise short-difference assertion.

Use exactly \(C'_U(m)=\Lambda(m)-\sum_{d\mid m,d\le U}\mu(d)\log(m/d)\). The shift (2) of the polynomial-rank note then reduces by simple substitution to (2) of the present note with the \(A_j\)-sum still cut at \(d\le U\), since
\[
                \tfrac12-t+P_j(t)=\frac{(1-2t)^j}{2j},
           \qquad P_j(0)-\tfrac12=-(1-\tfrac1{2j}).
\]
This algebra works on every integer \(m\), not just squarefree, since \(\mu\) already ignores repeated divisor powers. Each extra \(U<d<\sqrt m\) has \(0<1-2\log d/\log m\ll(\log H+1)/L\). The sum of absolute added weights costs
\(O_j(xL^{2-j(1-\sigma)})\) by \(\sum_{m\le 1.5x}\tau(m)\ll xL\), the logarithm in front, and a bounded number of admissible \(s\) at each \(m\) because \(s\mid N-m\) and \(s>x^{.10}\). Thus the extension fits \(o(M_N)\) at the stated \(j\). No radical error remains. At true prime \(m\), both tapers equal \(1\), so (2) is zero exactly. Proper prime-power rows cost \(x^{1/2+o(1)}\) in absolute weight and can be omitted; all seriously remaining cases have \(\Lambda(m)=0\).

## 2. Uniform all-rank Fourier control of the first taper

Use \(e(t)=e^{2\pi it}\) and \(F_\theta(m)=\prod_{p\mid m}|1-e(\theta\log p/L)|\), a strongly multiplicative nonnegative factor on all \(m\). Uniformly in \(N,\theta\), the actual quotient profiles give
\[
 \sum_{\mathcal Q_i}F_\theta(m)\ \ll\
      \frac{\mathfrak S(N)x}{L^2}\,{\cal E}_x(\theta),\qquad
 {\cal E}_x(\theta)=\exp\left\{\sum_{p\le2x}
                                  \frac{|1-e(\theta\log p/L)|}{p}\right\}.
\tag{3}
\]
This is the same uniform two-form multiplicative upper bound as in [ForcedHighRankNegativeQuotient.md](ForcedHighRankNegativeQuotient.md), §2, on a different literal affine form. For \(\mathcal Q_1\) fix \(s,a_q,P\) and put \(B_0=s a_qP\). The remaining true prime \(v=Q\) has \(v\asymp Y=x/B_0\ge x^{.289}\), and \(m=N-B_0 v\). For \(\mathcal Q_2\) fix \(s\) and the two smaller \(q\)-primes, and let the largest \(v\) be free; \(B_0\le x^{.856}\), so \(Y\ge x^{.144}\). A central interval at this scale suffices, dropping extra profile cuts in an upper bound. The two primitive linear forms are \(v,N-B_0v\), determinant \(N\), and \((B_0,N)=1\) holds on unit support. The product has height \(O(x^2)\), and the interval \(\asymp Y\) at polynomial length meets the fixed height and interval parameters in the cited Henriot upper bound with its [published erratum](https://doi.org/10.1017/S0305004114000280). For \(v\) we may upper-bound the prime by roughness at \(x^{.001}\), and for \(m\) take the exact nonnegative multiplicative envelope \(F_\theta\). These functions have prime values bounded by \(2\) uniformly, giving the same growth and all constants independent of \(\theta\). At primes of \(N\) exclude positive valuations by the actual unit condition on both forms. At primes of \(B_0\) the \(m\)-form is a nonzero constant and the \(v\)-form has one root. There are only finitely many such added prime factors, so their exceptional local factors cost \(O(1)\), and the determinant factor is \(\mathfrak S(N)\). The common two-form sieve base and the roughness of \(v\) give \(O(\mathfrak S(N)Y/L^2)\) times the factor \({\cal E}_x(\theta)\) for the \(m\)-weight. This is exactly the positive-Euler-product bound (7) of the cited note. Sum over the fixed primes with \(Y=x/B_0\) and \(\sum1/B_0\ll1\) on their polynomial bands; all fixed prime labels have a fixed positive lower exponent. This proves (3). The pointwise \(W_s(q) D_B(q)/\log q\) is a bounded nonnegative weight and can be inserted at constant cost in (3).

For fixed \(\theta\), the harmonic prime limit gives
\[
 \log{\cal E}_x(\theta)\ \longrightarrow\
      \int_0^1 \frac{|1-e(\theta t)|}{t}\,dt
         \le \frac4\pi\log(1+|\theta|)+O(1).
\]
The periodic numerator has mean \(4/\pi\) and its mean-zero part has a bounded primitive. Near zero use the Lipschitz upper; the same Chebyshev/Mertens split as in the cited note gives the global \({\cal E}_x(\theta)\ll(1+|\theta|)^2\) regardless of \(x,\theta\).

Let \(h_j(u)=(1-u/j)_+^j-e^{-u}\) on \(u\ge0\), and extend it evenly to the negative real line. Its \(L^1\) norm and the total variation of its **fourth distributional derivative** are \(O(1/j)\), uniformly in \(j\ge9\). Indeed for each \(0\le k\le4\) the derivative on the positive half-line is the difference between \((-1)^k(j)_k j^{-k}(1-u/j)_+^{j-k}\) and \((-1)^ke^{-u}\). On \(u\le j/2\) Taylor's bound for \(\log(1-u/j)\) and the mean-value inequality for exponentials bound the absolute difference by
\(O_k(j^{-1}(1+u)^2e^{-c u})\), using \((j)_k/j^k=1+O_k(1/j)\). To see the reserve near \(u=j/2\), the difference of the two exponents is \(O_k((u+u^2)/j)\), and both exponents are at most \(-u/2\) for \(j\ge9,k\le4\). The remaining tails have exponentially small integrals by the same \(e^{-u/2}\) upper and the cutoff. At the origin \(h_j'(0)=0\) exactly, \(h_j''\) matches under even reflection, and the jump of \(h_j'''\) is \(O(1/j)\); the possible atom in the fourth derivative has the same price. The cutoff at \(u=j\) causes no atom to this order. Hence
\[
                  |\widehat h_j(y)|\ll j^{-1}\min(1,|y|^{-4}).
\]

The full exponential comparator is exactly nonnegative on every \(m\):
\[
 \sum_{d\mid m}\mu(d)e^{-2j\log d/\log m}
                    =\prod_{p\mid m}(1-p^{-2j/\log m})\ge0.
\]
Consequently \((A_j(m))_-\) is bounded by the absolute Möbius sum of \(f_j(t)=h_j(2jt)\) at \(t=\log d/\log m\). Fourier inversion produces the multiplier \(F_\theta(m)\) in (3), **without freezing \(\log m\)**: with \(\lambda=\log m/L\in[1,2]\), the Fourier weight is \(\lambda|\widehat f_j(\lambda\theta)|\ll j^{-2}\min(1,(j/|\theta|)^4)\). Tonelli, (3), and the global quadratic \( {\cal E}_x\)-bound permit dominated convergence at fixed \(j\). Its limiting integral is at most
\[
       O\left(j^{-2}\int_{\mathbb R}
                 (1+|\theta|)^{4/\pi}\min(1,(j/|\theta|)^4)\,d\theta\right)
                   =O(j^{4/\pi-1}).
\]
Multiplying by \(\log m/(2j)\) in (1) and dividing by \(M_N=\mathfrak S(N)x/(2L)\) proves (1). There is no \(\Omega(m)\)-dependent cutoff error, and the sign of the exponential product is exact at primes and repeated factors alike.

## 3. Genuine remaining coupling, not an independent flat-taper bound

The positive capacity of the first taper is of the reference scale. On actual \(\mathcal Q_i\), the signed main of its \(\log m/(2j)\) sum is \((I_i+o(1))M_N\), with \(I_i\) the true product density in (6) of the positive-budget note. In the short range \(d\le U\) this follows by the finite polynomial moment argument of the polynomial-rank note: here the derivative of \((1-2t)^j\) at zero is \(-2j\), and \(\sum\mu(d)\log d/\phi(d)=-\mathfrak S(Nn)+o(1)\) by the exact uniform Huang–Li finite moment and the constant moment. All higher Taylor coefficients contribute \(o(M_N)\), and the \(\sqrt m\) extension has already been paid. On the actual profile \(\mathfrak S(Nn)/\mathfrak S(N)=1+O(x^{-.010})\), and removing target primes among the source factors costs power-small relative to its ordinary PNT count. Thus (1) also bounds any first-taper positive capacity above that reference by \(O(j^{4/\pi-2})M_N+o(M_N)\).

By contrast the whole weighted sum of \(\log m\,G(m)\) is null to arbitrary log precision on this same genuine \(\mathcal Q_i\) mask, while **\(G(m)=1\) at each true prime \(m\)**. Thus the composite negative part of \(G\) costs at least the true prime mass, up to the negligible null error. This has a rigorously positive size in dyadic average: the actual \(n=sq\) density with \(W_s(q)D_B(q)/\log q\) is \(I_i\) on the scale \(X/\log X\), as in the positive-budget note, and the independent weighted prime \(m\) density on scale \(X\) is \(1\) by ordinary PNT. Their actual additive constraint over \(X\le x\le2X\) uses the same area \(3/2\), with both arguments odd, and unit condition automatic for a reflected prime \(m\) (it is bigger than all source factors). Consequently
\[
 \liminf_{X\to\infty}
 \frac{\sum_{X\le x\le2X}\sum_{\mathcal Q_i,\ m\ {\rm composite}}
              W_s(q)\frac{D_B(q)}{\log q}\log m\,G_-(m)}
      {\sum_{X\le x\le2X}M_{2x}}
              \ \ge\ I_i>0 .
\]
This excludes making the whole composite negative flat-taper mass an arbitrarily small \(o(1)M_N\) by any separate positive-part argument for it, with the same null and prime normalization. The required next estimate must correlate the negative flat taper with the positive first taper on the **same** physical row (or use a different signed ledger). Neither (1) nor this necessary coupling gives the full fixed-target signed upper, and neither proves Goldbach.

## Related work

See [Granville–Koukoulopoulos–Maynard](https://dms.umontreal.ca/~koukoulo/documents/publications/sieveweights.pdf) for earlier smooth Möbius divisor weights and [Pham’s October preprint](https://www.preprints.org/manuscript/202610.3061) for nearby fixed-target reflected comparisons. The estimate above concerns the first taper on the actual two adjusted quotient supports. The independently unpriceable flat-taper sign is not a uniform obstruction to a signed comparison. No priority claim is made.
