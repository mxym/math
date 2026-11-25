# Residue-Parseval gain for the short signed factor

On Dirichlet GRH, in the [true reflected Type II sum](DirectGoldbachReflectedMobiusTypeI.md) for \(X=N\), boxes with \(d\asymp D\), \(e\asymp E\), \(a\asymp A\), \(DE\asymp X\), \(D\le\sqrt X\), \(U<a\), \(A\le X^{1/2-\delta}\), cost
\[
 O_{\epsilon,\sigma}\left(X^{1/2+2\sigma+\epsilon} A(1+V_0)
             \sqrt{1+D/A}+X^{1-\sigma+\epsilon}\right).
\]
Here \(\delta>0\) is fixed, and \(V_0\) is the second Vaughan cutoff, chosen to be a sufficiently small fixed power of \(X\) in terms of \(\delta\). The smoothing exponent \(\sigma>0\) can likewise be chosen small. This gives a power saving on every such box. It leaves the skew \(A>\sqrt X\) range open.

One may impose \((de,N)=1\) before Vaughan expansion: on central prime support this is automatic since \(p=N-de\asymp N\) cannot be a prime divisor of \(N\) for large even \(N\). The change on replacing primes by von Mangoldt weights due to proper powers is already negligible by the original argument. Keep this coprimality in the expanded identity. Open \(\beta(b)=\log b-\sum_{j\mid b,\ j\le V_0}\Lambda(j)\); the log term uses \(j=1\). The condition \(b>V_0\) is automatic since \(b=(N-de)/a\asymp X/A\). Fix \(a,j\) and put \(q=aj\). Then \(q\mid N-de\), so necessarily \((N,q)=(de,q)=1\).

Smooth sharp physical box edges in \(d,e,b\), and \(e>d\), at relative width \(X^{-\sigma}\) (an \(a\)-interval is a fixed outer restriction). This costs \(O(X^{1-\sigma+\epsilon})\) after summing all the weights, before opening \((d,e)=1\) and \(\beta\): there are \(O(X^{1-\sigma}+D+E)\) pairs \((d,e)\) at the edges in those variables, or \(O(X^{1-\sigma}+A+X/A)\) pairs \((a,b)\) at a sharp \(b\)-edge, and the opposite factorization and weights cost \(X^\epsilon\). Alternatively no \(b\)-box cutoff is needed: with \(a\) fixed its sharp cutoff is a single product window, and in this application one can bound the resulting box by Perron separation or assume \(A,X/A\le X^{1-\sigma}\). In the present Vaughan region take \(U\) to be a fixed positive power of \(X\), and \(\sigma\) below that power; if \(D\) or \(E\) is small, keep their independent rectangular endpoints sharp rather than smoothing them. The \(e>d\) boundary only occurs when \(D\asymp E\). The following argument only uses windowing in \(b\) when this smoothing error is valid.

Open \(1_{(d,e)=1}\) by summing \(r\mid(d,e)\) with weight \(\mu(r)\). Necessarily \((r,q)=1\). Write \(d=rd'\), \(e=re'\). For squarefree \(r\), \(\mu(e)=\mu(r)\mu(e')1_{(r,e')=1}\); also retain \((e',N)=1\) as an induced coprimality, and \((d',N)=1\) in the \(d'\) weights. The congruence for \(e'\) is
\[
 e'\equiv N\overline{r^2d'}\pmod q.
\]
In any prefix of the \(d'\) interval each reduced residue is selected at most \(1+O(D/(rq))\) times, since inversion and multiplication by \(N\bar r^2\) are bijections on units.

For an arbitrary \(e'\)-prefix, denote by \(S(v)\) the sum of \(\mu(e')1_{(e',rN)=1}\) in residue \(v\) in that interval. The [uniform GRH prefix estimate](DirectGoldbachReflectedMobiusTypeI.md) and character Parseval on \((\mathbb Z/q\mathbb Z)^*\) give
\[
 \sum_v |S(v)|^2
   =\frac1{\varphi(q)}\sum_{\chi\bmod q}
      \left|\sum_{e'}\mu(e')1_{(e',rN)=1}\chi(e')\right|^2
   \ll_\epsilon (E/r)X^\epsilon .
\]
The characters are induced to a modulus dividing \([q,\mathrm{rad}(rN)]\) for this estimate. Cauchy–Schwarz over the \(d'\)-prefix with any bounded \(d'\) weight, including \(\mu^2(rd')\), now gives
\[
 \ll_\epsilon X^\epsilon \frac{\sqrt{DE}}{r}
       \sqrt{1+D/(rq)}
\]
for every rectangular prefix. If the support is nonempty then \(r\ll\min(D,E)\), so interval lengths rounded to integers do not alter the displayed scale. Use two-dimensional Abel summation to restore \(W(1-de/X)\log(e/d)\), the cutoffs, and the log of \(b=(N-de)/a\) for \(j=1\). The normalized variation loss is \(O(X^{2\sigma+\epsilon})\); rectangular sharp endpoints can be kept as just those endpoints. The central test ensures the log of \(b\) and its derivatives are finite with these bounds.

Sum harmonically over \(r\), use \(q\gg A\), and sum the weights over \(a,j\) using \(\sum_{j\le V_0}\Lambda(j)\ll V_0\). This proves the bound. In particular
\[
 X^{1/2}A\sqrt{1+D/A}\ll X^{1-\delta/2}
\]
for \(D\le\sqrt X\), and fixed sufficiently small \(\sigma\) and \(V_0=X^\kappa\) retain a saving. This improvement over the [individual-progressions estimate](DirectGoldbachReflectedTypeIIShortFactor.md) comes from averaging over the different inverse residues before summing the \(d\)-variable. It does not estimate the needed signed total on primorials or arbitrary targets.
