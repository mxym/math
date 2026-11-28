# The sharp grid resolution for distributional equivalence of quantized dyadic observations

Suppose the public coefficients stay available, but each noisy angle is recorded only as the index of its equal-width bin. A label-independent randomization can then turn the discrete observation back into a continuous one, but constant-in-bin reconstruction wastes resolution. In the broad-noise ensemble the exact order of bin count needed for vanishing statistical deficiency is \(d^{1/4}\), not the \(d^{1/2}\) scale suggested by constant-in-bin reconstruction. At critical resolution we bound the deficiency between two explicit positive Gaussian quantities.

## 1. Model and theorem

Fix odd \(q\ge3\), dyadic \(d\to\infty\), \(R=(\mathbb Z/q)[X]/(X^d+1)\), and fixed positive rank \(r\). Write \(b=\beta/d\) for \(\beta>0\) fixed, and \(t_d=kb^2\to t\in(0,r\log q)\). Each of \(k\) independent rows has \(A_i\sim U_{R^r}\) and scalar-coordinate response vector \(Y_i=\langle A_i,s\rangle_R/q+E_i\) on the torus, for the label \(s\in R^r\). All \(kd\) scalar coordinates of the noise have independently wrapped density \(f_b(y)=\sum_h b^{h^2}e^{2\pi i h y}\). Let \(P_s\) be the full observation law. Let \(Q_s\) retain all public coefficients but replace each response coordinate by the bin index in a circular equally spaced partition with \(m=m_d\) bins, \(m\) a multiple of \(q\). The bin centers are \(c_z=(z+1/2)/m\bmod 1\), \(0\le z<m\).

Consider the directed deficiency
\[
        \delta_m=\inf_K\sup_{s\in R^r}\operatorname{TV}(Q_s K,P_s),
\]
where \(K\) is any label-independent Borel kernel; it is not required to preserve the recorded bin or even the public coefficient in the output. The reverse direction has zero deficiency by the quantization map. With \(\Phi\) the standard Gaussian distribution function:
* If \(m/d^{1/4}\to0\), then \(\delta_m\to1\).
* If \(m/d^{1/4}\to\infty\), then \(\delta_m\to0\). The sufficient direction needs no assumption \(t<r\log q\).
* If \(m/d^{1/4}\to\gamma\in(0,\infty)\), then
  \[
  2\Phi\!\left(\frac{\pi^2\sqrt t}{6\sqrt2\,\gamma^2}\right)-1
   \ \le\ \liminf\delta_m\ \le\ \limsup\delta_m
   \ \le\ 2\Phi\!\left(\frac{7\pi^2\sqrt t}{6\sqrt{10}\,\gamma^2}\right)-1 .
                                                                 \tag{1}
  \]

The critical upper limit is optimal within the narrower class of identical independent scalar reconstructions that keep the design, send uniform bin indices to Haar, and commute with shifts by \(1/q\). This is not a lower bound for arbitrary joint kernels.

In particular, in the stated subcritical regime of the full label space, the condition \(m/d^{1/4}\to\infty\) is necessary and sufficient for vanishing deficiency. The theorem identifies the sharp order of resolution, not the exact limiting constant at finite \(\gamma\). The bounds concern statistical experiments, with a deterministic quantizer; they do not address an attack, a response decoder of any complexity class, or a deployment.

## 2. Positive interpolation of probability densities

Put \(h=1/m\). There is a label-independent kernel on the scalar bin index \(z\) with circle density
\[
       K_z(y)=h^{-1}\,(1-\operatorname{dist}_{\mathbb T}(y,c_z)/h)_+ .
\]
It is nonnegative and integrates to 1. Its support may cross the boundary of the recorded bin. The resulting reconstructed density, at a scalar unshifted location, is
\[
 \widetilde f_b(y)=\sum_z \overline f_b(c_z)(1-\operatorname{dist}(y,c_z)/h)_+,
 \qquad
 \overline f_b(c)=h^{-1}\int_{c-h/2}^{c+h/2} f_b(v)\,dv .
\]
On the interval from \(c_z\) to \(c_{z+1}\) this is the linear interpolation of the two cell averages. A shift by any \(u/q\) commutes exactly with all these operations, since \(q\mid m\). Applying the kernel independently in each coordinate and keeping the sampled designs thus gives a \(\widetilde f_b\) product location law at every fixed label and design.

The Fourier series and its derivatives show \(\|f_b^{(j)}\|_\infty=O_j(b)\) for every fixed \(j\ge1\), as \(b\to0\). The difference between a cell average and its center value is \(O(bh^2)\) by symmetric Taylor expansion. The difference between linear interpolation of the center values and the original smooth density is also \(O(bh^2)\) uniformly. Hence \(\|f_b-\widetilde f_b\|_\infty=O(bh^2)\); both densities are uniformly \(1+O(b)\), in particular bounded below. The one-coordinate squared Hellinger distance is \(O(b^2h^4)\), and product Hellinger tensorization gives
\[
              \delta_m\le \min\{1,C\sqrt{kd}\,b/m^2\}
                     \le \min\{1,C'\sqrt d/m^2\}.                \tag{2}
\]
This proves vanishing at \(m\gg d^{1/4}\). The usual density constant on each bin approximates its cell values only to first order in \(h\); the nonnegative linear interpolation is what gives the improved rate.

For the critical upper bound, let \(0\le\vartheta\le1\) be the fractional position between adjacent centers \(c_z,c_{z+1}\). A more precise expansion, uniform in the interval and \(y\), is
\[
  \widetilde f_b(y)-f_b(y)
   =h^2\Big(\frac1{24}+\frac{\vartheta(1-\vartheta)}{2}\Big) f_b''(y)
       +O(bh^3).
\]
Here \(1/24\) is from averaging an interval symmetric about a center, and the second coefficient follows by Taylor expansion around \(y\) in the interpolated center values. The leading second derivative is \(-8\pi^2 b\cos(2\pi y)+O(b^4)\). In integrating its square, for each fixed \(\vartheta\) the exact center-grid average of \(\cos^2(2\pi y)\) is \(1/2\), since \(m\ge3\). Also
\[
 \int_0^1\Big(\frac1{24}+\frac{\vartheta(1-\vartheta)}{2}\Big)^2d\vartheta
   =\frac{49}{2880}.
\]
When \(m/d^{1/4}\to\gamma>0\) finite, this yields
\[
  kd \int (f_b-\widetilde f_b)^2/\widetilde f_b
    \ \longrightarrow\
  \lambda=\frac{49\pi^4 t}{90\gamma^4}.
\]
For detail put \(w=(f_b-\widetilde f_b)/\widetilde f_b\). Under \(\widetilde f_b\), \(w\) is centered and \(\|w\|_\infty=O(bh^2)=o(1)\). The product log likelihood is the sum of \(kd\) copies of \(\log(1+w)\); Taylor expansion gives limiting mean \(-\lambda/2\), variance \(\lambda\), and the centered CLT by boundedness and the nonzero limiting summed variance. The likelihood ratios have bounded second moments by the exact iid second-moment formula \((1+\int w^2\widetilde f_b)^{kd}\). Thus their \(L^1\) deviations from 1 converge to those of \(e^{\sqrt\lambda Z-\lambda/2}\), \(Z\) standard Gaussian. Half that expectation is \(2\Phi(\sqrt\lambda/2)-1\). The calculation is the same under every design and label, proving the critical upper bound in (1).

## 3. Quantization changes the position of the statistical critical window

Set \(\rho_m=\sin(\pi/m)/(\pi/m)\). The scalar probability of a bin, at shift \(u/q\), is
\[
 Q_{b,m}(z\mid u)=m^{-1}\{1+2b\rho_m\cos(2\pi(c_z-u/q))+O(b^4)\}.
\]
The remainder is uniform even as \(m\) varies; it follows by integrating the first Fourier term exactly and bounding the higher terms. Use as scalar reference the averaged bin probability \(g_{b,m}(z)=q^{-1}\sum_u Q_{b,m}(z\mid u)\); it is \(m^{-1}(1+O(b^{q^2}))\), and is exactly invariant under the grid shifts induced by \(u/q\). In the continuous experiment use the analogous \(g_b=q^{-1}\sum_u f_b(\cdot-u/q)\). The random true log likelihood \(Z_{\rm bin}\) of all quantized responses against the independent reference, conditional on the true label and design, has iid scalar terms whose common distribution is independent of the label and design. This holds for the continuous true log likelihood \(Z_{\rm full}\) as well. The first-harmonic expansion gives
\[
 \begin{array}{lll}
 E Z_{\rm full}=t_dd+O(1),      & \operatorname{Var}Z_{\rm full}=2t_dd+O(1),\\
 E Z_{\rm bin}=t_dd\,\rho_m^2+O(1), &
 \operatorname{Var}Z_{\rm bin}=2t_dd\,\rho_m^2+O(1).
 \end{array}                                                       \tag{3}
\]
Indeed the leading scalar KL divergence is half the squared first-harmonic norm and the variance is the squared norm. The grid averages of the cosine and its square are 0 and \(1/2\) for all \(m\ge3\); the scalar error \(O(b^3)\) suffices, even for \(m=3\), since \(kdb^3=O(1)\). The scores are sums of terms \(O(b)\) and have Gaussian standardized limits by the triangular CLT, uniformly along all allowed bin sequences because \(\rho_m\) is bounded below by a positive constant.

We include a bounded-overlap argument to see that (3) really controls the success window for a deterministic subset of candidate labels, not merely a heuristic information count. Conditional on the design, in either experiment let \(L_s\) be the response likelihood relative to the product reference. For \(s\ne v\), at a scalar coordinate of phases \(a/q,a'/q\), the reference integral of \(L_sL_v\) equals
\[
        1+2b^2 \rho^2\cos(2\pi(a-a')/q)+O(b^4),
\]
with \(\rho=\rho_m\) for bins and \(\rho=1\) for the full observation. Each centered scalar likelihood has exactly zero reference mean, and the product of the two first harmonics gives the quadratic term using the exact scalar second Fourier average (discrete or continuous). This controls the displayed scalar error uniformly. Thus the logarithm of the full pair integral is
\[
 2b^2\rho^2\sum_{i,j}\cos(2\pi(\langle A_i,s-v\rangle_R)_j/q)+O(kdb^4).       \tag{4}
\]
For any nonzero difference, its image under one uniform \(A_i\) is uniform in a nonzero ideal. At fixed odd \(q\) every such ideal is the interleaved product of copies of an ideal at a fixed dyadic degree \(d_0(q)\); this follows from the common factor degree \(\operatorname{ord}_{2d}(p)\) doubling for large \(d\), monic coprime prime-power lifting, and CRT (see [the base-ideal proof](https://github.com/mxym/math/blob/ce786bb5e0060a7574add4ea103adb7c200c0a4f/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-common-law-ambiguity.md#3-uniform-coherence-from-the-fixed-base)). Every coordinate projection is nonzero by signed rotation. The cosine sum in (4) is therefore a sum of \(kd/d_0\) independent centered variables in \([-d_0,d_0]\). Hoeffding and a union bound over \(q^{rd}\) differences show that its \(b^2\)-multiple is bounded in absolute value by a constant with probability \(1-o(1)\), because \(kdb^4=O(d^{-1})\) and \(r\) is fixed. On that one design event all conditional off-diagonal pair integrals in both experiments are at most a fixed constant \(C_0\).

For a deterministic set of \(M\) labels with the uniform prior, let \(p_{\rm opt}(A)\) be the best possible conditional exact-label success. If \(Z\) is the corresponding true log likelihood under either experiment, then on the design event for every \(\ell\ge0\),
\[
 \Pr[Z>\log M+\ell]-C_0 e^{-\ell}
   \ \le p_{\rm opt}(A)
   \le \Pr[Z\ge\log M-\ell]+e^{-\ell}.                           \tag{5}
\]
The upper bound includes the true label in the analysis: on the event \(L_s/M<e^{-\ell}\), any decision rule's chosen label captures reference-integrated true mass at most \(e^{-\ell}\). For the lower bound the total of all wrong weights \(M^{-1}\sum_{v\ne S}L_v\) has expectation at most \(C_0\) under the true law by the pair integral. If the true weight exceeds \(e^\ell\), the event that some wrong weight alone beats it requires this total to exceed \(e^\ell\). This yields (5) for an unrestricted optimal decision, not a computational rule. With \(\ell\to\infty\), \(\ell=o(\sqrt d)\), the two probabilities have the same Gaussian limit by (3). Thus the conditional optimum tends to this limit in probability over designs and its expectation tends to the same value.

## 4. Lower bound for all output randomizations

Choose a deterministic subset of size \(M_d\) with
\[
             \log M_d=\frac12 t_dd(1+\rho_m^2)+o(1).
\]
This is feasible by rounding to an integer size: \(t_d\to t<r\log q\) ensures exponentially many unused labels. The subset is fixed before the public designs. An arbitrary kernel of worst-label error at most \(\delta\) could carry any full-experiment decision with its success probability reduced by at most \(\delta\) under this prior. Thus \(\delta_m\) is at least the full optimal average success minus the bin optimal average success even if kernels can change the design or bin on output. This is the elementary bounded-loss comparison for the directed TV deficiency.

The two information means in (3) differ by
\[
       D_d=t_dd(1-\rho_m^2),\qquad
       1-\rho_m^2=\frac{\pi^2}{3m^2}+O(m^{-4}).
\]
If \(m/d^{1/4}\to0\), then \(D_d/\sqrt d\to\infty\), including bounded \(m\ge3\) (there the factor \(1-\rho_m^2\) is bounded away from zero). By (5), the full success tends to 1 and the bin success tends to 0, proving \(\delta_m\to1\). If \(m/d^{1/4}\to\gamma\in(0,\infty)\), then \(D_d/\sqrt d\to t\pi^2/(3\gamma^2)\) and \(\rho_m\to1\). The centered cutoff \(\log M_d\) is asymptotically half this difference away from each mean, in opposite directions; both standardized score variances divided by \(d\) tend to \(2t\). Hence the success difference tends to \(2\Phi(\pi^2\sqrt t/(6\sqrt2\,\gamma^2))-1\), yielding the lower bound in (1). If \(m/d^{1/4}\) fails to tend to infinity, a bounded subsequence has a further finite limit, so the positive lower limits prove necessity for vanishing deficiency.

## 5. The critical constant for marginal-preserving scalar kernels

Restrict attention to an identical independent scalar kernel in every coordinate, leaving the design untouched. Assume the scalar kernel commutes with the cyclic shifts induced by \(1/q\), and maps the uniform law on bin indices to Haar measure. It may depend on \(d\) and need not keep its output in the reported bin. For any such sequence of kernels at \(m/d^{1/4}\to\gamma\in(0,\infty)\), the limiting error cannot be less than the upper limit in (1).

For proof let \(k_z(y)\) denote the output density conditional on bin \(z\). These densities exist because their uniform average is Haar, and \(p_z(y)=k_z(y)/m\) are nonnegative summing to 1 almost everywhere. Write
\[
 v(y)=\sum_z p_z(y)e^{2\pi i c_z}
       \in \operatorname{conv}\{e^{2\pi i c_z}:0\le z<m\}.
\]
If \(\widetilde f_a\) is the reconstructed density at phase \(a/q\) and \(f_a\) the full one, then
\[
 f_a(y)-\widetilde f_a(y)
      =2b\,\operatorname{Re}\!\big[e^{-2\pi i a/q}
              (e^{2\pi i y}-\rho_m v(y))\big]+O(b^4)
\]
uniformly, by the exact first harmonic in §3 and \(\sum_z p_z(y)=1\). In the \(L^2\) norm averaging \(a\) uniformly and integrating \(y\), the leading term has norm \(\sqrt2 b\|e^{2\pi iy}-\rho_m v(y)\|_2\); the average complex second Fourier moment of \(e^{-2\pi i a/q}\) is zero since \(q\ge3\). Commutation with the shifts means the squared error at each phase is the same as its average.

For \(y\) having position \(\vartheta\) between two neighboring centers, take the unit normal to the chord joining those two phases, pointing radially outward at their angular midpoint. The entire scaled polygon \(\rho_m\operatorname{conv}\{e^{2\pi i c_z}\}\) is at normal coordinate at most \(\rho_m\cos(\pi h)\). The normal component of the distance from \(e^{2\pi i y}\) to every point of this polygon is therefore at least
\[
 \begin{split}
 \cos(2\pi h(\vartheta-1/2))-\rho_m\cos(\pi h)
    &=4\pi^2h^2\Big(\frac1{24}+\frac{\vartheta(1-\vartheta)}2\Big)
          +O(h^4).
 \end{split}
\]
This bound is nonnegative before expanding. Square, integrate by the interval fraction, and combine with the \(L^2\) triangle inequality for the \(O(b^4)\) density remainder. In the critical regime \(b^4=o(bh^2)\), and all reconstructed densities are \(1+O(b)\) by the reference-preserving condition. It follows that for every phase \(a\),
\[
  kd \int (f_a-\widetilde f_a)^2/\widetilde f_a
          \ \ge\ \frac{49\pi^4 t}{90\gamma^4}-o(1).              \tag{6}
\]
All constants are uniform over the allowed kernels.

The log likelihood argument of §2 works for any such kernels along a subsequence on which the summed variance parameter in (6) tends to a finite positive limit: the scalar relative errors are uniformly \(O(b)=o(1)\), all phase-specific relative-error laws are shifted copies, and their product second moments are bounded on that subsequence. If instead the summed parameter tends to infinity, product Hellinger affinity tends to zero because the one-coordinate affinity equals \(1-\frac18\int(f_a-\widetilde f_a)^2/\widetilde f_a\) plus a relative \(o(1)\) in its deficit (the same uniform small-error Taylor expansion). In this case TV tends to 1. Every subsequence thus has lower error at least the profile at the parameter in (6). The tent kernel of §2 belongs to this class and attains it. This does not exclude a better critical constant using collective reconstructions or ones that change the coefficient design.

## 6. Context and limitations

For directed comparison of experiments see [Le Cam](https://doi.org/10.1214/aoms/1177700372); [Carter](https://carter.faculty.pstat.ucsb.edu/multi.pdf) uses jittering in a different asymptotic equivalence problem. The first-harmonic loss under these bins is the classical projection-of-score mechanism. The contribution here is to match the lower power of \(d\) forced by the shifted label-information window with a genuinely positive second-order interpolation bound, in a finite-label family with growing dimension and a random public design. The [earlier within-response information bottleneck](https://github.com/mxym/math/blob/27381dbb91194c272fc9d65875df9abd95ad11a8/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-response-bottleneck.md) addresses retained information under rate constraints rather than worst-label distributional equivalence; its statements do not imply this threshold. The condition \(t<r\log q\) is used for the lower bound to select a subfamily at the midpoint of the two statistical thresholds. There is no necessity claim above that range, when label information itself can be more concentrated, nor a claim that the two critical constants in (1) coincide.
