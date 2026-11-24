# A natural-scale high-term fiber with genuine positive and negative cancellation

Companion to [the natural-scale note](SmallRadicalShiftedNaturalScaleReservoir.md) and its checked centered-prime analytic input. This proves a **net** signed estimate in one real subchamber, with both signs at the whole high-term scale there. It is not a bound on the net shifted high term over other chambers.

## 1. The actual fiber and theorem

Use the same even target \(P\), \(L=\log P\), small radical, interior \(I=PJ\), \(y=e^{L^\delta}\) for \(0<\delta<.1\), \(z=e^{L^{.24}}\), base tag family \(\mathcal T\) with even \(K\), singular factor \(S(P)\), and \(V_y(P)\asymp S(P)/L^\delta\). Fix \(\beta=.82,\ \gamma=.9\) and a sufficiently small fixed \(c>0\). Take two squarefree cofactor libraries, with all base packet bands excluded in each:
\[
\begin{aligned}
\mathcal A_1
 &=\{v_1\le e^{L^\gamma}:\ \text{each prime factor lies in }(y,e^{L^\beta}]\},\\
\mathcal A_2
 &=\{v_2\le P^{.09}:\ \text{each prime factor lies in }(e^{L^\beta},P^c]\}.
\end{aligned}
\]
There is **no parity restriction** in either. Both contain 1 and their prime supports are disjoint. In the same set of \(\asymp L\) disjoint genuine-prime rectangles from the natural-scale note, retain only rows
\[
n=pq\in I,\qquad P-pq=u v_1v_2r,\qquad
u\in\mathcal T,\quad v_i\in\mathcal A_i,\quad p,q,r\text{ prime}.
\tag{1}
\]
Here \(p\in[P^{.32},P^{.35}]\) is the smaller prime. By the bounds on \(v_i\) and \(u\), \(v_1v_2\le P^{.1}\) and the true \(r>P^{.8}\) is unique. The tag \(u\) and both cofactor labels are recovered uniquely from the prime factors of \(m=P-n\). The actual sign of the smooth shifted high summand is
\[
T(pq)\lambda(m)=\lambda(v_1v_2)\log(pq).
\tag{2}
\]

The positive and negative parts in (1) are each \(\asymp P V_y(P)\) in absolute weight. Their **net** actual signed sum is
\[
O\bigl(PV_y(P)L^{-2(\beta-\delta)}\bigr).
\tag{3}
\]
If the shifted high budget includes the actual first translated cover across \(M\ge2\) offsets as in the natural-scale note, restrict (1) to those genuinely covered rows. The same two-sided absolute-weight assertions hold and their net marked sum is
\[
O\bigl(PV_y(P)(L^{-2(\beta-\delta)}+L^{-M/200})\bigr).
\tag{4}
\]
In particular both losses are \(o(PV_y(P)/L)\) if \(M>200\). This is a proved relative power-log saving of the marked contribution *of this whole two-sided fiber*, not just a true-positive count or a subtraction of incomparable upper and lower bounds.

## 2. Reciprocal masses and exact signed product in the lower cofactor

Write \(D_i=\sum_{v_i\in\mathcal A_i}v_i^{-1}\). Mertens gives full product reciprocal masses \(\asymp L^{\beta-\delta}\) and \(\asymp L^{1-\beta}\) for the two respective prime ranges; removing the finitely many complete base bands has only a bounded-factor effect. Rankin pays the \(v_1\) size restriction (shown uniformly below). For \(v_2\) use the same independently included-prime reciprocal law as in the natural-scale note: its log size has expectation \(O(cL)\), so choose \(c\) small enough that at least half the weight lies below \(P^{.09}\). Thus \(D_1\asymp L^{\beta-\delta}\) and \(D_2\asymp L^{1-\beta}\).

For fixed \(C>0\) and \(0\le t\le C\log L/L\), the lower cofactor signed reciprocal transform satisfies the uniform bound
\[
\left|\sum_{v_1\in\mathcal A_1}\lambda(v_1)v_1^{t-1}\right|
\ll L^{-(\beta-\delta)}.
\tag{5}
\]
Indeed the full squarefree product is \(\prod_{\ell}(1-\ell^{t-1})\) over that lower cofactor prime set. All factors lie in \((0,1)\) for large \(P\) and \(1-\ell^{t-1}\le1-1/\ell\), whose product is \(O(L^{-(\beta-\delta)})\) by Mertens (deleting the base bands changes this by at most a constant). For the truncated tail use \(s=L^{-\beta}\); all \(\ell^{s+t}\le e^{1+o(1)}\), so
\[
\sum_{v_1>e^{L^\gamma}}v_1^{t-1}
\le e^{-L^{\gamma-\beta}}\prod_{\ell}(1+\ell^{s+t-1})
\le e^{-L^{\gamma-\beta}} L^{O(1)}.
\]
The same Rankin inequality with \(t=0\) justifies the stated unsigned mass. All signed generating products are on finite sets of genuine primes, with \(\lambda=\mu\) on these squarefree factors.

## 3. Prime-centered comparison for the actual source weight, not merely log-triple counts

Let \(w(x)=(\log x)1_{\mathrm{prime}}(x)\), \(R_z(x)=1_{\{P^-(x)>z\}}\), and \(\kappa_z=\prod_{\ell\le z}(1-1/\ell)\). On a source rectangle with coordinates \(x,q\), the desired summand is implemented by
\[
\left(\frac{w(x)}{\log x}w(q)+w(x)\frac{w(q)}{\log q}\right)
b\bigl((P-xq)/u\bigr),
\]
where \(b(h)=\lambda(v_1v_2)\) when \(h=v_1v_2r\) has genuine prime \(r>P^{.8}\) and both designated cofactors, and zero otherwise (and beyond \(h=P\)). The decomposition of \(h\) is unique, and this is one bounded function of \(h\) alone. For the unsigned version replace \(b\) by \(|b|\). The logarithmic amplitudes add exactly to \(\log(pq)\).

Both \(\alpha=w-\kappa_z^{-1}R_z\) and \(\alpha/\log x\) satisfy the uniform centered-character estimates from the checked proof, the latter by partial summation on the polynomial \(x\)-range. Apply the reflected comparison to replace \(w\) by \(\kappa_z^{-1}R_z\) in both coordinates, retaining the \(1/\log\) amplitudes and the true last prime. The signed and unsigned rectangle errors are \(O_A(PL^{-A})\), with \(K\) fixed sufficiently large for a fixed \(A\). This error is for the entire cofactor fiber at once.

For fixed \(a=uv_1v_2\), after replacements the same genuine last-prime BV calculation as in the natural-scale note applies, now with the weight \(1/\log x+1/\log q\) and counting the last prime without its log. In detail, fix a rough \(x\); a solution forces \((x,a)=1\) as no prime of \(a\) divides \(P\). The exclusion costs \(O(XL/z+L)\) against rough \(x\)-main of scale \(\kappa_z X\), by summing integer counts over primes above \(z\) of \(a\). For all retained \(x\), open \(q\)-roughness via squarefree \(d\) supported on primes \(\ell\le z,\ \ell\nmid aP\); the reduced progression for the last prime is \(r\equiv Pa^{-1}\bmod xd\). The true endpoint is \(P/a\ge P^{.9-o(1)}\), vastly above the square of the moduli \(xd\le P^{.35+o(1)}\). The rough and small parts of \(xd\) determine the pair \(x,d\) uniquely. Use maximal weighted prime BV and harmless partial summation for the multiplier
\[
\frac{1/\log x+1/\log((P-ar)/x)}{\log r}
\]
on the true last-prime interval. Both its size and its variation there are \(O(L^{-2})\), since all variables are polynomial in \(P\) and the interval endpoints have fixed ratio bounds. Its prime-log main term becomes \(x/a\) times the integral in \(q\) after changing variables from \(r\). The Bonferroni model and omitted-shell bounds are uniform per \(a\). A summed error of size \(O_A((P/a)L^{-A})\) is more than sufficient.

In the resulting model \(x/\varphi(x)=1+O(L/z)\) and pure-integer rough \(x\) has density \(\kappa_z\) with arbitrary-log uniform prefix error. Partial summation permits the amplitude
\[
\frac{1/\log x+1/\log q}{\log((P-xq)/a)}
\]
since both its supremum and its total \(x\)-variation are \(O(L^{-2})\) uniformly over the rectangle and \(a\), using \(P-xq\gg_J P\). The local factor after normalization is \(S(P)(1+O(L/y+1/z))\) uniformly as in the natural-scale note, and that relative error remains superlog-small when estimated against the full **unsigned** cofactor mass \(\sum1/a=O(L^{1-\delta})\). Thus the signed rectangle model is
\[
S(P)\sum_{u,v_1,v_2}
  \frac{\lambda(v_1v_2)}{uv_1v_2}
  \int_{I_1}\int_{I_2}
  \frac{1/\log x+1/\log q}{\log((P-xq)/(uv_1v_2))}
  \,dq\,dx+O_A(PL^{-A}).
\tag{6}
\]
The corresponding unsigned model is exactly (6) with \(\lambda(v_1v_2)\) replaced by 1, by the same proof. Its amplitude is \(\asymp L^{-2}\) uniformly. Consequently the unsigned total on \(\asymp L\) rectangles is \(\asymp P S(P)L^{-\delta}\). One **cannot** infer the signed model from a log-triple count by dividing by a single asymptotic \(L^2\) without a relative precision analysis; the exact weighting above avoids that issue.

## 4. Laplace separation of the last logarithm and the exact signed saving

Put \(F=P-xq\asymp_J P\), so \(R=F/(uv_1v_2)>P^{.8}\). Use the exact identity
\[
\frac1{\log R}=\int_0^\infty R^{-t}\,dt
=\int_0^\infty (F/(u v_2))^{-t}v_1^t\,dt.
\]
Cut at \(T=C\log L/L\) with sufficiently large fixed \(C\). The integral beyond \(T\) is \(R^{-T}/\log R=O(L^{-1-.8C})\) pointwise, so pay it against full unsigned mass. On \([0,T]\), sum over \(v_1\) using (5). The remaining \((F/(u v_2))^{-t}\) has integral \(\ll L^{-1}\) uniformly, by \(F/(u v_2)\ge P^{.9-o(1)}\). Taking absolute values in the \(v_2\) and \(u\) sums and using \(\mathcal V\asymp1\), the signed amplitude of (6), after \((1/\log x+1/\log q)\), is bounded by
\[
O\left(L^{-2}D_2 L^{-(\beta-\delta)}\right)
=O\left(L^{-1-2\beta+\delta}\right).
\]
Areas are \(\asymp P\) on \(\asymp L\) rectangles. This proves (3); the two individual sign masses are each \(\asymp PV_y(P)\) by the unsigned calculation and the now genuine cancellation.

## 5. The actual translated selector only removes a negligible unsigned cost from this fiber

The fixed-\(p,u,v\) two-affine upper sieve in the natural-scale note does not use the parity of \(v\). Apply it with \(v=v_1v_2\): these cofactors are squarefree, \(\le P^{.1}\), avoid the base bands, all primes \(>y\), their two-range labels are unique, and their reciprocal mass is \(D_1 D_2\asymp L^{1-\delta}\). Even when some primes of \(v\) belong to translated cover packets, their entire reciprocal cost in the deleted forbidden classes is \(O_M(L/y)\), as before. Thus true uncovered weight \(\sum_{\rm uncov}\log(pq)\) in the union of rectangles is \(O(PV_y(P)L^{-M/200})\). Deleting it changes the signed sum by at most that much regardless of sign. On surviving rows the actual first-cover selector sums to one. This gives (4) in the original marked budget, without applying any reflected Type II theorem to a shifted, tag-dependent residual.

The result pays only this prescribed **near-full prime with a two-range cofactor** fiber, with a base-tag occupancy requirement on \(P-n\). Its bounded logarithmic partition is essential: no estimate is asserted for a cofactor cutoff that couples \(v_1\) and \(v_2\), arbitrary components of either library, or the whole shifted high budget.
