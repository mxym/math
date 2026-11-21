# A fixed-target upper on the whole higher even cubic tail

This treats the actual final term of [CubicRankFourAndMarkedOccupancy](CubicRankFourAndMarkedOccupancy.md) **in its cubic representation**, after the full rank-2, 3, 4 and 6 transfers. The remaining smooth even ranks \(\ge8\) have a uniform one-sided upper below \(.0073 M_N\) for all sufficiently large targets. This does not price rank six or pay the changed cubic calibration gap of almost \(5J M_N\).

## 1. Whole transfer, including unbounded even rank

Keep the exact prime \(s\), integers \(q,m\), central window, units, weight \(W_s(q)\), scores \(T_q,R\), and \(L,T,M_N,J,B_m,z_q,z_m\) of the cubic notes. For any integer cutoff \(K\ge2\), even varying with the target, let \(\mathcal V_K\) be the actual squarefree reflected composites of even rank \(\ge K\), with \(P^-(m)>z_m\) and \(P^+(m)\le B_m\). Then
\[
 \sum_{\substack{s,q\ {\rm composite}\rho_q(q)=1,\ m\in\mathcal V_K}}
      W_s(q)(\log m) T_q(q)R(m)
   = -\sum_{\substack{s,q\ {\rm prime}\m\in\mathcal V_K}} W_s(q)(\log m)R(m)
       +O_A(xL^{-A})                                                \tag{1}
\]
uniformly in \(K\). Here \(s\) is always prime; in the first sum the word composite applies only to \(q\), and it can be taken squarefree by the earlier rough-square bound. All unit and central masks are retained. Odd ranks are not asserted in (1).

We give the needed explicit subpower two-product conductor argument, rather than applying a fixed-power hypothesis at a moving exponent. On a dyadic rectangle \(r\asymp R_0,v\asymp V_0\), \(R_0V_0\asymp x\), \(R_0,V_0\ge z_m/2\), use actual prime \(r\) with prime interval restrictions and the unit mask modulo \(N\), and an arbitrary divisor-bounded coefficient on \(v\). Allow fixed log powers in both coefficients. For the sum of absolute progression discrepancies over moduli \(A\le Q=x^{.4995}\) and maximal reduced residues, start from character orthogonality with the exact coprime principal. As in Bombieri--Friedlander--Iwaniec, [Acta Mathematica 156 (1986), Theorem 0 proof, (2.4), (2.7)](https://doi.org/10.1007/BF02399204), write a nonprincipal character modulo \(A=ef\) as induced by a primitive one modulo \(f>1\). Its axis coefficients retain \((r,e)=(v,e)=1\) inside the character sums, and \(1/\phi(ef)\le1/(\phi(e)\phi(f))\). For conductors \(f\sim U>F=L^B\), Cauchy and the primitive multiplicative large sieve, at fixed \(e\), bound that dyad by
\[
 \ll L^C\sqrt{x}\,(U^2+R_0)^{1/2}(U^2+V_0)^{1/2}/U
 \ll L^C\big(Q\sqrt{x}+x/\sqrt{R_0}+x/\sqrt{V_0}+x/F\big).
]
Both axis norms use the usual fixed divisor-square moments. Summing \(e\) with \(1/\phi(e)\) and conductor dyads costs only log powers. For \(1<f\le F\), genuine prime Siegel--Walfisz at its actual scale \(R_0\) gives \(O_D(R_0 L^{-D})\) for every fixed \(D\), uniformly in prefix intervals and primitive nonprincipal characters. Indeed \(\log R_0\ge (1+o(1))L/T^{23}\), and \(L^B\le(\log R_0)^{B+1}\) eventually. Deleting prime divisors of the additional imprimitive mask \(eN\) costs only \(O(L)\) actual primes. The trivial other-slot \(O(V_0L^C)\) bound and the \(O(FL^{O(1)})\) harmonic multiplicity complete the low-conductor estimate. Thus the progression discrepancy is \(O_A(xL^{-A})\) for every fixed \(A\); this proof explicitly covers both lengths as short as \(z_m/2\), not a near-unit length 1.

On an actual \(m\in\mathcal V_K\), label *each* prime \(r\mid m\) with weight \((1+\omega(v))^{-1}\), \(v=m/r\); the total orientation weight is exactly 1. Both slots are \(>z_m\), since \(m\) is composite and rough. All the reflected rough, even rank, \(K\), and largest factor masks separate between the true prime axis and the divisor-bounded cofactor axis. A temporarily recombined repeated \(r\mid v\) is removed by the old rough-square support estimate, both in the actual row and the coprime principal using divisor moments; all involved prime squares exceed \(z_m^2\), saving more than every log power. For squarefree even rank use the exact even half-score
\[
 R(rv)=\tfrac12\sum_{d\mid v}\mu(d)
  \left[
    \left|1-\frac{2\log d}{\log(rv)}\right|^3-
    \left|1-\frac{2\log(rd)}{\log(rv)}\right|^3
  \right].
\]
Freeze only \(\log r/L\) in this formula on a mesh of width \(L^{-F_1}\), keeping the literal prime \(r\) with its interval on the SW axis. The rounded coefficient depends only on \(v\), and each score changes by at most \(O(L^{-F_1}\tau(v))\), uniformly in rank, because \(|t|^3\) is Lipschitz on the fixed compact interval in use. The masks are not rounded. The error on actual rows has arbitrary log reserve by fixed divisor moments on \((q,N-sq)\) (Cauchy and Shiu); on coprime principal rows sum fixed divisor powers with \(1/\phi(A)\). Thus the unbounded rank does not increase any divisor-power exponent.

Before applying the conductor argument open the exact \(T_q\) divisor \(d_q\) and replace \(\rho_q\) by its previous degree-\(\lfloor T^2\rfloor\) Bonferroni polynomial with divisor \(e_q\). Its restoration error is still arbitrary-log small, because \(|R|\ll\tau(m)\). The actual modulus is \(A=s\operatorname{lcm}(d_q,e_q)\), not the product if the two labels overlap; it is \(<x^{.4995}\). At each modulus and original labels the cut \(d_q<q/B_q\) is the genuine prefix \(m<N-sB_q d_q\). The previous log-relative meshes keep this endpoint and the central window: first round all physical \(m\) endpoints to absolute grid width \(xL^{-F_2}\), then approximate each prefix on product dyads by rectangular meshes in \(r,v\) of relative width \(L^{-F_2}\). Both errors change only a constant number of physical strips of length \(O(xL^{-F_2})\) at each fixed original endpoint and modulus. Shiu on the actual reduced class and the analogous coprime principal bound each strip by \(O(xL^{-F_2+C}/\phi(A))\) for the fixed divisor power at hand. Total harmonic modulus count, smooth separations of \(W_s,\log m\), dyads and mesh pieces cost log powers, paid by arbitrary reserve. Weighted discrepancies over repeated moduli are absorbed by the usual fixed-divisor-power interpolation between the unweighted conductor estimate and the trivial Shiu bound. No restriction on the sign or growing rank of the \(v\) coefficient enters the conductor proof.

After distribution the exact principal is the usual masked \(q\)-side harmonic: fix physical \(m,s,e_q\), write \(d_q=a j\), \(a\mid e_q\), \((j,e_q)=1\), and use the actual cutoff \(j<q/(B_q a)\) and \(1/\phi(j)\). It is arbitrarily log-small uniformly since the endpoint is polynomially large. The coprimality with \(m,N,s,e_q\), and the \(s^{-1}1_{s\mid j}\) correction when needed, are exactly as in the earlier projections. Thus the all-integer \(q\) sum is arbitrarily log-small. The actual prime \(q\) terms have \(T_q=1\), giving (1), with no extra prime-\(q\) distribution asserted on an individual rank.

## 2. Uniform truncations on the actual prime-\(q\) right side

Use a compactly supported function \(F(t)\) equal on \([0,1]\) to \((1-2t)_+^3\), with a smooth left extension and cutoff. Its Fourier transform is \(O((1+|\xi|)^{-4})\), since the third derivative has only a finite jump and is piecewise smooth with compact support. Absolute inversion gives the factor-by-factor majorant for the full score by
\[
 \int |\widehat F(\xi)|\prod_{p\mid m} a_\xi(p)\,d\xi,
 \qquad a_\xi(p)=\min(2,|\xi|\log p/L),
\]
with a harmless fixed convention factor. Here \(m\ge x\) makes the inequality uniform while \(\log m\) in the true formula may vary.

Take \(\lambda=5/4\), and at each prime power use the nonnegative multiplicative values \(\lambda a_\xi(p)\) on the reflected form, and the \(x^{.4}\)-rough indicator on the actual prime-\(q\) form. At primes dividing \(N\) both weights give zero on positive powers, retaining the true unit masks. The class constants in corrected Henriot are independent of \(\xi\): these local values are bounded by \(5/2\) at all prime powers and the induced growth at any integer is at most \((5/2)^{\omega(m)}\ll_\epsilon m^\epsilon\) with a fixed constant for each fixed \(\epsilon\). The source forms are \(q,N-sq\), primitive with product discriminant \(N^2\), and length \(Y\asymp x/s\). At \(p\mid N\) the roots coincide and nontrivial discriminant contributions are zero because of the zero weights there; at \(p=s\) one form is a nonzero constant and the slope ratio is \((s-1)/(s-2)\); otherwise the two roots are distinct. At \(2\mid N\) there is one root, contributing the usual normalized factor 2 or an absolute constant if omitted in Corollary 2. Thus the normalized sieve product is \(O(\mathfrak S(N)\prod_{p\le Y}(1-1/p)^2)=O(\mathfrak S(N)L^{-2})\), as in UngatedReflectedRankProjection, with no extra \(N/\phi(N)\) from the discriminant. The rough \(q\) Euler envelope is bounded. The remaining Euler factor is
\[
 \exp\left(\lambda\sum_{p\le2x}\frac{a_\xi(p)}p\right)
       \ll (2+|\xi|)^{2\lambda};
]
split at \(p=\exp(L/|\xi|)\) when it lies in \([2,2x]\), using \(\sum_{p\le y}\log p/p\ll\log y\) below and Mertens above; the extreme ranges satisfy the same bound directly. Corrected Henriot's height and interval hypotheses hold with fixed exponents since \(s<x^{.14}\), and no constants grow with \(\xi\). Integration against \(\widehat F\) converges because \(2\lambda=2.5<3\). Summing the bounded \(s\)-harmonic and the actual \(\log m\) yields
\[
 \sum_{s,q\prime, m\ {\rm squarefree},\Omega(m)\ge K}
  W_s(q)(\log m)|R(m)| \ll \lambda^{-K}M_N,                         \tag{2}
]
with a single fixed constant, valid even when \(K\) varies. Dropping the remaining largest-factor or rough lower bounds is allowed on this positive upper.

Similarly, the contribution with at least one true reflected prime factor \(p\le x^\kappa\) is \(O(\sqrt\kappa M_N)\) for fixed \(0<\kappa<.05\), with a fixed constant. Open one such genuine \(p\) for an upper and write \(m=p v\). If \((p,sN)>1\) the physical row is empty (and \(p=s\) is also excluded by size). The free forms \(q=q_0+p j,\ v=(N-s q_0)/p-sj\), with \(q_0\equiv N\bar s\pmod p\), have determinant \(N\), are primitive, and have parameter length \(\asymp x/(s p)\gg x^{.81}\). The extra local ratio \((p-1)/(p-2)\) is bounded for the actual odd \(p\). Use \(\lambda=1\) and factor out \(a_\xi(p)\) once; the reflected row is squarefree. The sum over the opened prime has
\[
 \sum_{p\le x^\kappa}a_\xi(p)/p\ll\min(\kappa |\xi|,\log(2+|\xi|)).
]
The geometric mean bound gives \(O(\sqrt\kappa)\) after integration against \(|\widehat F(\xi)|(2+|\xi|)^2\), uniformly in \(N\). This is a true same-target estimate, not a tightness claim from an angular model.

## 3. Fixed-rank actual angular upper

For fixed \(k\ge2\), fixed \(\kappa>0\), and nonnegative Lipschitz function \(C(a)\) on the symmetric prime log simplex, restrict the true squarefree reflected source to primes \(>x^\kappa\), and put \(a_i=\log p_i/\log m\). In particular \(C=[-R]_+\) at even \(k\) is Lipschitz for each fixed rank, with no claim of uniform constant in \(k\). Count actual \(s,q\prime\) with \(m=N-sq\) in this source, using weight \(W_s(q)\log m\,C(a)\). It has the uniform upper
\[
 \limsup_{N\to\infty,\,2\mid N}\frac{\text{that weighted count}}{M_N}
   \le
 \left(\int_{.10}^{.14}\frac{2(1-\sigma)(1-2\sigma)^2}{(.499-\sigma)\sigma}\,d\sigma\right)
 \int_{\substack{a_i\ge\kappa\\\sum a_i=1}}C(a)\frac{da}{k!\prod a_i}
   \le 4.8 J\int_{\substack{a_i\ge\kappa\\\sum a_i=1}}C(a)\frac{da}{k!\prod a_i}.       \tag{3}
\]

Here is the actual upper sieve proof, in particular its factor relative to the physical \(s\)-weight. Fix \(s\), let \(D_s=x^{.499}/s\), and use the dimension-one upper sieve on \(q=(N-m)/s\) at \(z=D_s^{1/2}\); genuine \(q\prime\gg x^{.86}\) is included. Its squarefree divisibility modulus is precisely \(s d\), including \(s^2\) if \(s\mid d\). Use product BV on the true weighted reflected prime-product source to level \(x^{.499}\), labeling one of its genuine primes as in Section 1 (now both slots have fixed polynomial length). The independent coefficient for each mesh of the prime axis, fixed score \(C\), and the central product range are treated by the same Lipschitz and endpoint argument as in Section 1. The possible many labels \((s,d)\) for a modulus cost a fixed divisor power, so aggregate sieve errors are arbitrary-log-small without an individual distribution claim for a fixed \(s\).

The exact density is \(g_s(p)=0\) if \(p\mid N\), \(g_s(s)=1/s\) and \(g_s(p)=1/(p-1)\) otherwise, just as in the marked occupancy proof. Here the coprime principal initially also excludes primes of \(m\) dividing \(s d\). The \(s\mid m\) exclusion is power-small in the total harmonic principal because \(s>x^{.10}\), using the bound \(O(x/s)\) on arbitrary integer multiples with bounded fixed-rank weight; the same is true if a reflected prime divides any \(d\), by first fixing \(m\) and summing divisors \(d\) with a given \(p\mid m\). There are at most \(k\) such primes and each is \(>x^\kappa\), giving a power-saving in the harmonic modulus sum. Exclusions of reflected primes dividing \(N\) also cost a power-saving in the unprogressioned main by opening those prime multiples. The source remains physically unit throughout. Consequently the usual uniform dimension-one main is \((1+o(1))X_s\mathfrak S(N)e^{-\gamma}/\log z\) times \(F(2)=e^\gamma\), which gives the factor \(2/((.499-\sigma)L)\) with \(\sigma=\log s/L\). Here \(X_s\) is the unprogressioned true reflected source mass divided by \(\phi(s)\). The upper comparison uses only the upper linear sieve (Matomäki--Zuniga-Alterman Lemma 2.5), not the stronger conjectural prime-product upper.

The unprogressioned true weighted reflected mass is asymptotic to \((x/(2L))\int C(a)\,da/(k!\prod a_i)\) with the stated prime cut, by ordinary prime PNT: for each fixed compact angular box count the last actual prime over the physical \(m\in[x,1.5x)\) interval after fixing the other genuine primes, and then sum their reciprocal prime measures. Refine finite boxes and discard angular walls of vanishing measure; \(a_i\ge\kappa\) keeps all prime lengths polynomial and the density locally bounded. The unordered convention divides by \(k!\). Since \(W_s(q)=(1-\sigma)(1-2\sigma)^2+O(1/L)\) and \(\log m=L+O(1)\), inserting the prime \(s\)-harmonic gives the first coefficient of (3). The ratio against the original \(J\) integrand is \(2(1-\sigma)/(.499-\sigma)\), maximized at \(.14\) and less than \(4.8\). This proves (3) with the target singular series and no assumption of joint prime independence.

## 4. Certified angular arithmetic and final inequality

For even \(k\ge4\), let \(A_k\) be the signed simplex integral of \(R\) and \(B_k\) that of \(|R|\), both with the unordered measure in (3) and no cutoff on the logs. Fourier representation of \(|t|^3\), after the degree-zero and degree-two moments vanish, gives
\[
 A_k=\frac{3}{\pi}\frac{(-1)^{k/2}2^k}{k!}
                  \int_0^\infty\frac{(\arctan u)^k}{u^4}\,du,
 \qquad
 B_k\le\frac{3}{\pi k!}\int_0^\infty\frac{H(u)^k}{u^4}\,du,
 \quad H(u)=\int_0^\infty\frac{2e^{-a}|\sin(u a)|}{a}\,da.       \tag{4}
\]
For details, \(|t|^3=(12/\pi)\int_0^\infty(\cos(ut)-1+(ut)^2/2)u^{-4}du\), by two integrations by parts and the elementary \(\int_0^\infty(1-\cos u)/u^2=\pi/2\). On a simplex of total scale \(v\), the complete centered argument is \(v-2\sum_{i\in I}a_i\). Taking its half finite difference gives the Fourier product \(\prod_i2i\sin(u a_i)\) with prefactor \(6/\pi\). The corresponding simplex integral of the cubic homogeneous score is \(v^2\) times its value at \(v=1\), because the log harmonic measure has degree \(-1\). Laplace integrating in \(v\) at parameter 1 gives the factor \(\int_0^\infty v^2 e^{-v}dv=2\) on the left and independent \(a_i\) on the right. Absolute products give the upper in (4) by Tonelli; for the signed formula the same absolute majorant ensures Fubini, and the signed one-axis integral is \(2i\arctan u\). This also establishes integrability of the required angle weights even near tiny factors. The alternating signs and decreasing absolute ratios \(|A_{k+2}|/|A_k|\le\pi^2/((k+1)(k+2))\) show that \(\sum_{k\ge8\ {\rm even}}A_k\ge0\). Hence
\[
 \sum_{k\ge8\ {\rm even}}\int[-R]_+\,\frac{da}{k!\prod a_i}
     =\frac12\sum_{k\ge8\ {\rm even}}(B_k-A_k)
     \le\frac{3}{2\pi}\int_0^\infty
          \frac{\sum_{j\ge8\ {\rm even}}H(u)^j/j!}{u^4}\,du.       \tag{5}
\]

There is no pointwise sign replacement for (5). An exact useful check from the largest-factor bit is this: at even rank `k` at least 6, let `a` be the largest logarithmic coordinate, `b_i` the remaining ones, and `e=1/2-a`. Then
\[
 R=-16\sum_I(-1)^{|I|}\left(e-\sum_{i\in I}b_i\right)_+^3.
\]
In the even complete half-score, split the largest bit, expand `|t|^3=t^3+2(-t)_+^3` in each part, and discard the two full cubic polynomial moments on the at-least-five remaining variables. Complement the first truncated sum in the remaining odd-rank set; in the second, the positive and negative cubic parts have equal full signed sum, since their difference is a polynomial. This proves the display. In particular the score is nonpositive if at most four of the remaining coordinates are less than `e`: larger bits never enter, and the first four distributional derivatives of the positive cubic power are nonnegative. At rank eight, equal coordinates give `R=1/4`, whereas `(.3,.1,.1,.1,.1,.1,.1,.1)` gives `R=-.016`. Thus both signs occur on real open angular families by continuity, including nearby distinct-coordinate profiles.

For the explicit upper, the positive cosine expansion of \(|\sin|\) gives
\[
 H(u)=\frac4\pi\sum_{b\ge1}\frac{\log(1+4b^2u^2)}{4b^2-1}.
\]
Indeed \(|\sin t|=(4/\pi)\sum_{b\ge1}(1-\cos(2bt))/(4b^2-1)\) with nonnegative summands, and the integral of \(e^{-a}(1-\cos(c a))/a\) is \(\tfrac12\log(1+c^2)\). Thus \(H\) increases, \(H(u)\le2u\), and for \(u\ge U\), \(H(u)\le H(U)+(4/\pi)\log(u/U)\) using \(\sum_b(4b^2-1)^{-1}=1/2\). For a truncated b-sum at \(b=12\), the omitted tail (before the \(4/\pi\) multiplier) is at most
\[
 \frac{\log(1+4u^2)+2(\log12+1)}
             {12(4-13^{-2})};
]
use \(\log(1+4b^2u^2)\le\log(1+4u^2)+2\log b\) and the two integral series bounds. For the middle range \(u\in[1/4,128]\) integrate with 32 equal subdivisions of each dyadic interval, taking the monotone upper at the right endpoint against the exact integral of \(u^{-4}\). Below \(1/4\) use \(H\le2u\) and \(\sum_{j\ge8,\mathrm{even}}H^j/j!\le H^8\cosh(H)/8!\); above \(128\) use this tail \(\le e^H/2\) and the preceding log bound. The rational script [check_cubic_even_tail.py](check_cubic_even_tail.py) certifies that \((3/\pi)\) times the full integral in (5), before its factor \(1/2\), is less than \(.0155\), and that the result after multiplication by \(4.8J/2\) is **strictly less than .0073**. Logarithm, exponential and even factorial tails in the certificate are rounded outward.

Finally, for any tolerance, first fix \(K_0\) large using (2), then a fixed small \(\kappa\) using the tiny-factor estimate, and then take the target limit using (3) on the finitely many remaining ranks. Let the two tolerances decrease; there is no application of a fixed-rank theorem with growing ranks. Reversing the sign in (1), drop its favorable true \(R>0\) part and bound the remainder by (3)--(5). The strict certified margin yields the announced upper below \(.0073M_N\) for all sufficiently large even \(N\). In particular the cubic identity now gives
\[
              Z_N\le6J M_N-H_N^*+D_{6,N}+.0073 M_N+o(M_N).
\]
It would still need, for example, a uniform fixed-margin lower on \((H_N^*-D_{6,N})/M_N\) above \(5J-.0027\), about \(.97566\), to reach the [assigned upper budget for this semiprime cell](JointShortDivisorProjection.md#1-statement-and-literal-endpoints). The proved favorable lower \(.0033\) alone is far below this requirement. No all-target Goldbach positivity follows.
