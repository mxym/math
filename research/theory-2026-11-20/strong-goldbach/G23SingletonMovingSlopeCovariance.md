# Actual prime-averaged singleton Type II: a precise coprime moving-slope target

Written research note, 2026-11-24. Continuation of the [genuine long-singleton Vaughan reduction](G23LongSingletonVaughanTypeII.md), not a bound for its remaining Type II. For \(P=2^j\), \(L=\log P\), and fixed interior \(J\), let \(\lambda_y(m)=R_y(m)\lambda(m)\), \(y=e^{L^\delta}\), \(z=e^{L^{.24}}\). The signed singleton Type II has actual \(p\) prime, \(P^\sigma<p\le P^{1/2-\varepsilon}\), actual z-rough w-smooth \(d\le P^\eta\), \(b,\ell>P^\gamma\), and genuine weights \(\lambda(d)\), \(\mu(b)\), \(\beta(\ell)=\sum_{a\mid\ell,\ a>P^\gamma}\Lambda(a)\). Keep the real \(n b=p d\ell b\in PJ\), \(k=d\ell b\in\mathcal K\) and \(t=\ell b\le X_t\). The aim is \(o(PV_y(P)/L)\) for the Lambda-weighted Type II uniformly in \(X_t\), sufficient after dividing by \(\log t\asymp L\) and including the original outer \(L\).

## 1. Average over actual p and ell before Cauchy

First process the k-interval and t-endpoint cuts with two separated Mellin step factors if present: choose each integer-test endpoint at a half-integer, and apply the ordinary truncated Perron identity using \({\rm Re}\,s=1/L\) and height \(P^{10}\). Its pointwise error is \(O(P^{-9})\) on relevant integer arguments of size \(O(P)\); the gap from the half-integer gives \(|\log(x/u)|\gg 1/P\) when \(x,u\) are comparable. Outside their comparable range the error is smaller, and endpoint cuts entirely outside the box can be omitted. Each integral of the absolute scalar kernel costs \(O(L)\); interval cuts use a difference of two step factors. The resulting twists factor into \(b^{i\omega}\), \(\ell^{i\theta}\), and \(d^{i\phi}\) (real powers of magnitude \(O(1)\) as all variables are \(\le CP\)). One may leave \(\mathbf1_{nb\in PJ}\) exact inside the later b-sum. The normalized factor \(\log(nb)/L\) is the sum of the separated bounded weights \(\log n/L\) and \(\log b/L\).

Now group the actual triples by \(n=p d\ell\) **before** any dyadic boxes in p, d, or ell. The literal \(nb\in PJ\) makes every relevant integer argument of the endpoint cuts \(O(P)\), so the uniform Perron error is harmless also before these boxes. Then divide just n and b into dyadic boxes of scales N and B. There are \(O(L^2)\) candidate boxes but only \(O_J(L)\) nonempty ones, since each B allows \(O_J(1)\) multiplicative N boxes with \(NB\asymp_J P\). Both B and N are polynomial, \(B\gg P^\gamma\), \(N\gg P^{\sigma+\gamma}\). For the two Mellin variables s,t, retain the factor \(d^s\ell^{s+t}\) (or its inverse, depending on the step convention) in \(a_n(s,t)\) and \(b^{s+t}\) separately in \(c_b(s,t)\). Since \(R_z(b\ell)=R_z(b)R_z(\ell)\), one obtains sums of the form
\[
 \sum_{\substack{n\asymp N\\n\ {\rm odd}}}
 a_n\sum_{b\asymp B} c_b\,1_{\{nb\in PJ\}}\lambda_y(P-nb),
 \quad
 a_n=\!\!\sum_{\substack{p d\ell=n\\p\ {\rm true\ prime}\\
       \text{literal box, d and ell restrictions}}}
 (-\lambda(d))\,\beta(\ell)R_z(\ell)\,(\text{separated twists}),
\]
where \(|c_b|\ll1\) and \(c_b\) includes the true \(\mu(b)R_z(b)\), divided log/phase if relevant. No prime is replaced in the original weights. Indeed \(p\) is genuine in the grouped coefficient and each n has at most \(1/\sigma\) possible genuine slope divisors p, after which each d is a divisor and determines ell. Since \(\beta(\ell)\le L\), \(|a_n|\ll_\sigma L\tau(n)\), so \(\sum |a_n|^2\ll NL^5\) by \(\tau(n)^2\le \tau_4(n)\). The Cauchy bound can now enlarge the nonnegative inner-square sum on n to all odd n in the actual product-scale box (fixed relative length), removing prime weights **only at this modulus-variable stage**.

## 2. Pay diagonals and true shared factors; remaining sufficient estimate

The b-diagonal of the inner square is \(O(NB)\). For distinct b,b', put \(m=P-nb\), \(m'=P-nb'\). If a prime \(r>y\) divides both, then \(r\mid b-b'\) since \((n,P)=1\); and \(r\nmid b\) or b', so \(n\equiv P b^{-1}\pmod r\) on the actual lattice. For a given r the number of genuine b,b' candidates is at most the integer bound \(O(B^2/r)\) because \(r\ll B\), and then there are \(O(N/r+1)\) n. Summing all \(r>y\) shows the complete absolute shared-factor bill is
\[
 O(NB^2/y+B^2\log L),
\]
which is smaller than \(NB^2L^{-A}\) for every fixed A, uniformly in the relevant exponent chambers, including the case \(B>N\). This treats floors at r>N separately. Weight \(\lambda_y(m)\lambda_y(m')\) ensures any common prime really is \(>y\).

One explicit sufficient remaining joint estimate is therefore
\[
 \sum_{\substack{b,b'\asymp B,\ b\ne b'\\R_z(b)R_z(b')=1}}
 \left|\sum_{\substack{n\asymp N,\ n\ {\rm odd}\\nb,nb'\in PJ\\
                  \gcd(P-nb,P-nb')=1}}
       \lambda_y(P-nb)\lambda_y(P-nb')\right|
 \ll NB^2 L^{-14}.
\]
The actual n interval lies in a fixed multiplicative width box, and endpoints from both nb and nb' are literal, not frozen. A one-sided bound for the signed sum of these covariances with the actual \(c_b\overline{c_{b'}}\) and real twist would be enough; the displayed absolute sufficient condition is stronger than necessary. By the \(NL^{5}\) coefficient norm, it gives \(O(P L^{(5-14)/2})\) per separated box, before the \(O_J(L)\) nonempty box multiplicity and \(O(L^2)\) Mellin cost. The result \(O(P L^{-3/2})\) more than pays \(o(PV_y/L)\) on powers of two. If one uses both coarser bounds (four pre-group boxes and \(NL^{17}\)), \(L^{-36}\) is still amply sufficient. The detailed arithmetic does not provide the displayed estimate.

## 3. Scope check against actual theorems

The [Matomäki–Radziwiłł–Tao averaged Chowla theorem](https://arxiv.org/abs/1503.05121), Theorems 1.1 and 1.6, averages additive shifts (the latter for bounded linear coefficients and shifts in actual intervals). Here the slope parameters \(b,b'\) both grow polynomially and the separation is \(n(b-b')\); changing to one reflected argument imposes a progression of step b and a coupled divisor condition on the shift, not independent shift averaging. The [ordinary two-point fixed-affine result](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) has constants depending on the fixed affine forms, not this family of polynomial slopes and intercept P with varying interval support. Its rough-shift averaging in the proof also occurs with a base variable independently averaged and fixed outer coefficients, unlike the coupled divisibility above. [Green–Tao linear equations](https://annals.math.princeton.edu/2010/171-3/p08) puts bounded linear systems on multidimensional domains; the jointly varying products nb, nb' are bilinear, and when slopes are fixed there is only the one n variable. Neither ordinary one-function BV nor these theorem statements supply the displayed joint estimate on any of the polynomial Type II chambers. No further cancellation is claimed here.
