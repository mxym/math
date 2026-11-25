# The positive-vector central test, with linear edge sensitivity

This is a deterministic refinement of the [reflection-even primitive test](CentralEvenPrimitiveGoldbachCriterion.md). It uses the genuine prime-only measure and the exact central discrepancy kernel, but proves no new lower bound for the number of pairs. The full Li–Liu operator norm is not required for this criterion.

Let \(a=1/3\), \(b=2/3\), \(S=\mathfrak S(N)\), \(\omega(t)=\sqrt{t(1-t)}\), and let \(\nu_N^{\rm pr}\) and \(\rho_N\) be the measures and weights of the earlier notes. Thus \(\nu_N^{\rm pr}\) is the actual coprime prime-pair measure with both primes central, symmetric about \(1/2\), and has mass \(O(S)\) by the [central upper sieve](CentralSpectrumQuantization.md). On real \(L^2[a,b]\) write \(g_f(t)=\int_t^b\rho_N(u)f(u)\,du\). Let \(A\) denote the pure main-term operator and \(P\) the prime-pair correction, with forms
\[
 A[f,f]=S\int_a^b g_f(t)g_f(1-t)\omega(t)\,dt,\qquad
 P[f,f]=\int_a^b g_f(t)g_f(1-t)\omega(t)\,d\nu_N^{\rm pr}(t).
\]
On the cone \(f\ge0\) these two integrands are nonnegative; \(P\) need not be positive semidefinite outside this cone. Put
\[
 \Lambda_N^+ = \sup_{\substack{\|f\|_2=1\\f\ge0}} (A-P)[f,f].
\]
If \(\lambda_0\) is the top eigenvalue of the model \(A\), then for absolute constants \(c,C>0\) and all sufficiently large \(N\),
\[
 c\int_a^b(b-t)(t-a)\,d\nu_N^{\rm pr}(t)
 \;\le\;\lambda_0-\Lambda_N^+
 \;\le\; C\int_a^b(b-t)(t-a)\,d\nu_N^{\rm pr}(t).
\]
Thus the amount by which a surviving pair influences the criterion is linear in the distance to a central endpoint, not quadratic as in the reflection-even primitive test.

## Positive main-term vector

The kernel of \(A/S\) is
\[
 \rho_N(u)\rho_N(v)\mathbf1_{u+v\ge1}\int_{1-v}^{u}\omega(t)\,dt.
\]
It is continuous, nonnegative, and positive for \(u+v>1\). The kernel of its square is strictly positive for \(u,v>a\), since one can choose its intermediate argument in a sufficiently short open interval immediately below \(b\). By the positivity-improving compact-operator argument the largest eigenvalue of the square is simple and has a positive eigenfunction: replacing a real maximizing vector by its absolute value preserves or increases the quadratic form, and strict positivity makes sign changes strictly disadvantageous; two independent eigenvectors would have an orthogonal pair and thus cannot both be of constant sign. The corresponding eigenvector \(f_0\) of \(A\), normalized and nonnegative, has a positive eigenvalue because the kernel of \(A\) is nonnegative and its quadratic form on \(f_0\) is positive. In particular the gap \(\Delta\) of the leading eigenvalue from the next largest Rayleigh value satisfies \(\Delta\asymp S\) uniformly for large \(N\). Indeed \(\rho_N\) converges uniformly to a fixed positive continuous function, the normalized kernels converge uniformly and in operator norm, and the limiting square has the same positivity improvement. Simplicity and the gap imply \(L^2\) convergence of the chosen unit top eigenvectors, and the eigen-equation with uniformly convergent kernels upgrades it to uniform convergence of their continuous representatives.

The limiting eigenfunction is positive at \(b\) since the kernel of the limit at \((b,v)\) is positive for every \(v>a\). Thus \(g_0=g_{f_0}\) satisfies \(c_0(b-t)\le g_0(t)\le C_0(b-t)\) uniformly on \([a,b]\). The upper follows from uniform boundedness; the lower follows from positivity uniformly near \(b\), for \(t\) outside that neighborhood also using \(b-t\le b-a\).

## Cone perturbation

Write \(m=P[f_0,f_0]\). From the estimate on \(g_0\), the symmetry \(b=1-a\), and \(\omega\asymp1\), \(m\) is comparable to the displayed endpoint-weighted moment and \(m\ll S\). The claimed upper gap bound follows by testing \(f_0\). For the lower, write a unit vector in the cone as \(f=u f_0+h\), \(h\perp f_0\), \(0\le u\le1\). The loss in the model is at least \(\Delta\|h\|_2^2\), and the prime correction \(P[f,f]\) is nonnegative on this cone. If \(\|h\|_2^2\ge \varepsilon m/S\) this proves the lower bound, with \(\varepsilon>0\) a small absolute constant.

Otherwise Cauchy–Schwarz on the primitive gives \(|g_h(t)|\ll\sqrt{b-t}\|h\|_2\). Hence
\[
 |P[h,h]|\ll S\|h\|_2^2,\qquad
 |P[f_0,h]|\ll\sqrt{Sm}\|h\|_2.
\]
For the second bound one uses \(g_0(t)|g_h(1-t)|\ll (b-t)\sqrt{t-a}\|h\|_2\), then the Cauchy bound by the square roots of \(\int(b-t)(t-a)d\nu_N^{\rm pr}\) and \(\int(b-t)d\nu_N^{\rm pr}\). Reflection handles the other cross term. Thus for sufficiently small \(\varepsilon\) the expansion \(u^2m+2uP[f_0,h]+P[h,h]\) is at least \(m/2\). This finishes the proof.

The gap is consequently strict if and only if a coprime prime pair lies in the open central interval. In particular this is not a way to infer a gap from a model density alone. The adapted separable count uses the weight \(\sqrt t\,g_0(t)\) on the central interval and zero outside. It has bounded variation, with a possible jump at \(a\), and its positive main-term comparison in ordinary major arcs does not control its fixed-target signed minor coefficient. The existing [global norm obstruction](https://hexagonmath.org/pdf/2611.00788v1) uses a polylogarithmic summand and \(N\pm m\), outside these central supports; it neither supplies a lower bound for the central cone gap nor refutes its positivity.
