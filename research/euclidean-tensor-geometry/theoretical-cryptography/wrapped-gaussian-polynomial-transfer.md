# Polynomial-probability transfer for wrapped product Gaussian noise

Wrapping can preserve inverse-polynomial probabilities even when the ratio of the two raw variances diverges. It does not, however, justify replacing an aggregate tail requirement by a coordinatewise cap. For independent, centered heat laws on circles, one relative-entropy bound and one aggregate cap give an exact criterion.

## Statement

Write \(\mathbb T=\mathbb R/\mathbb Z\) with normalized Haar measure, and let \(H_s\) be the law modulo \(\mathbb Z\) of the real density \(s^{-1}\exp(-\pi x^2/s^2)\), with width \(s>0\). For each \(n\ge2\) take arbitrary positive widths \(s_i,t_i\) and define
\[
 P_n=\bigotimes_{i=1}^n H_{s_i},\qquad Q_n=\bigotimes_{i=1}^n H_{t_i},\qquad
 \bar s_i=\min(s_i,1),\quad \bar t_i=\min(t_i,1),\quad
 \gamma_i=\bar s_i^2/\bar t_i^2,\quad k_i=\bar t_i^{-2}.
\]
All logarithms are natural. The following properties are equivalent.

1. For every \(a>0\) there is \(b>0\) such that for all sufficiently large \(n\), every measurable event with \(P_n(A)\ge n^{-a}\) has \(Q_n(A)\ge n^{-b}\). The same statement can use all measurable tests \(0\le h\le1\), replacing probabilities by expectations.
2. \(D(P_n\Vert Q_n)=O(\log n)\), and for some fixed \(K>1\)
   \[
      \sum_{i:\gamma_i>K} k_i=O(\log n).                        \tag{1}
   \]
3. For some fixed \(\theta>0\), \(D_{1+\theta}(P_n\Vert Q_n)=O(\log n)\), where \(D_\alpha\) is Rényi divergence in the same direction.

The constants in (1) and the fixed order in (3) may depend on the triangular array, but not on \(n\) or the event. To require transfer both ways, apply (2) with both orders of the two arrays. The particular numerical cutoff 1 is only a choice of scale for a unit torus; the half-open representative interval has no effect on the statement.

## Proof

### Uniform estimates for a single circle

Write \(f_s\) for the density of \(H_s\). On the representative interval \(I=[-1/2,1/2]\), for absolute \(C\ge1\),
\[
 C^{-1}\bar s^{-1}e^{-\pi x^2/\bar s^2}
   \le f_s(x)\le C\bar s^{-1}e^{-\pi x^2/\bar s^2},\qquad
 \mathbb E_{H_s} X^2\le C\bar s^2.                              \tag{2}
\]
For \(s\le1\), retain the zero translate for the lower bound and use \((x+j)^2-x^2\ge j^2-|j|\) in the sum for the upper bound. The square of the nearest representative cannot exceed the square of the original real Gaussian, which proves the second assertion for \(s\le1\). For \(s\ge1\), the absolutely convergent Fourier series \(f_s(x)=1+2\sum_{m\ge1}e^{-\pi m^2s^2}\cos(2\pi m x)\) gives bounds away from zero and infinity, and the representative has absolute value at most \(1/2\).

For any \(K>1\) fixed there is \(\theta>0\) such that uniformly on \(\gamma=\bar s^2/\bar t^2\le K\),
\[
   D_{1+\theta}(H_s\Vert H_t)\le C_K D(H_s\Vert H_t)
          \le C'_K B(H_s,H_t),\qquad
   B(P,Q)=-\log\int\sqrt{pq}.                                   \tag{3}
\]
Here \(p,q\) denote the densities in the affinity. To see this, first suppose \(p/q\le M\) pointwise. The two ratios comparing
\[
    u^{1+\theta}-(1+\theta)u+\theta,\quad
    u\log u-u+1,\quad
    (\sqrt u-1)^2
\]
in that order extend at \(u=1\) by their Taylor limits and are bounded on \([0,M]\). Integrate against \(q\); use \(\log(1+y)\le y\) for Rényi divergence, and \(\int q(\sqrt{p/q}-1)^2=2(1-\int\sqrt{pq})\le2 B(P,Q)\).

If \(\bar s\le\bar t\), put \(r=\bar t/\bar s\). By (2), \(p/q\le C^2r\), handling bounded \(r\) above. For large \(r\), (2) gives \(D(H_s\Vert H_t)\ge\log r-O(1)\) by integrating the lower bound on \(\log(p/q)\) against \(p\) and using \(\mathbb E_{H_s}X^2=O(\bar s^2)\). Also \(D_{1+\theta}\le\log r+O(1)\) by the pointwise bound, and \(\int\sqrt{pq}\le C_1 r^{-1/2}\) by extending the Gaussian envelope integral to the line. Thus (3) holds for sufficiently large \(r\), with the intervening bounded range handled by the density-ratio argument.

Suppose \(1<\gamma\le K\). If \(t\ge 1/(2\sqrt K)\), (2) bounds the density ratio by a \(K\)-constant. Otherwise \(s\le \sqrt K t<1\), and data processing from the real line bounds \(D_{1+\theta}\) by its real Gaussian value
\[
       \frac{-\theta\log\gamma-\log(1-\theta(\gamma-1))}{2\theta}.
\]
Take \(\theta=1/(2K)\). The displayed function has a second-order zero at \(\gamma=1\) and bounded second derivative on \([1,K]\); hence it is \(O_K((\gamma-1)^2)\). Set the integer \(m=\lfloor 1/(2t)\rfloor\ge1\). Then \(mt\in [1/4,1/2]\). The difference of the two expectations of \(\cos(2\pi m X)\) is \(e^{-\pi m^2t^2}-e^{-\pi m^2s^2}\), at least \(c_K(\gamma-1)\) by the mean value theorem on a fixed compact interval. Thus \(\operatorname{TV}(H_s,H_t)\ge (c_K/2)(\gamma-1)\). Pinsker's inequality gives the needed lower bound on \(D\), and \(\operatorname{TV}^2\le 2(1-\int\sqrt{pq})\le 2B\) gives the lower bound on \(B\). The upper bound on \(D\) follows from \(D\le D_{1+\theta}\). This completes (3).

For the remaining coordinates with \(\gamma>K\), (2) and \(\bar t<\bar s\) give the uniform bound
\[
       \log(f_s/f_t)\le 2\log C+(\pi/4)\bar t^{-2}
                         \le C_2 k,\quad k=\bar t^{-2}.         \tag{4}
\]
In particular both their KL and their Rényi divergence are at most the bound in (4).

### Sufficiency

By tensorization, (3), (4), and the two budgets in (2) of the statement imply \(D_{1+\theta}(P_n\Vert Q_n)\le C_3\log n\). To use that latter bound, put \(L=\log(dP_n/dQ_n)\), so \(\log\mathbb E_{P_n}e^{\theta L}=\theta D_{1+\theta}(P_n\Vert Q_n)\). For each \(a>0\) a sufficiently large \(c_a\) gives \(P_n[L>c_a\log n]\le n^{-a}/2\) for all large \(n\), by Markov's inequality. Any test of \(P_n\)-expectation at least \(n^{-a}\) still has expectation at least \(n^{-a}/2\) on the complementary region, where \(dQ_n/dP_n\ge n^{-c_a}\). This proves the claimed transfer uniformly over tests.

### Why the aggregate cap is necessary

If (1) fails for every fixed \(K\), then for every sufficiently large integer \(M\) there are arbitrarily large \(n\) with \(\sum_{\gamma_i>M^2} k_i>64 M\log n\). Use only coordinates in this sum. Fix \(a_0\in(0,1/8)\). For each chosen coordinate take an interval \([r_i,2r_i]\) with \(a_0\bar s_i\le r_i\le1/8\), and write \(b_i=r_i^2/\bar t_i^2\). This cost runs through all values in \([a_0^2\gamma_i,k_i/64]\). Their coordinate probabilities, by the lower envelope and the upper Gaussian tail from (2), satisfy
\[
      P_i([r_i,2r_i])\ge e^{-C_4 b_i/\gamma_i},\qquad
      Q_i([r_i,2r_i])\le e^{-c_4 b_i}.                            \tag{5}
\]
For the first bound, integrate the lower envelope over the whole interval and absorb the prefactor \(C^{-1}r_i/\bar s_i\ge C^{-1}a_0\) in the exponential since \(b_i/\gamma_i\ge a_0^2\). For the second, absorb the absolute tail constant using \(b_i\ge a_0^2M^2\) for large \(M\).

Take successive costs at capacity \(k_i/64\) until the next interval can bring the total past \(M\log n\). For that last interval choose the residual needed to reach the target, or its lower endpoint \(a_0^2\gamma_i\) if the residual is smaller. The \(Q\)-cost is at least \(M\log n\); the \(P\)-cost is at most \((\log n)/M+a_0^2\), because all ratios exceed \(M^2\) and the possible overshoot has \(P\)-cost at most \(a_0^2\). Taking the product event, with unrestricted remaining coordinates, (5) gives \(P_n(A)\ge n^{-1}\) for sufficiently large \(M,n\), but \(Q_n(A)\le n^{-c_4 M}\). Choosing increasing \(M,n\) contradicts transfer for \(a=1\). This argument does not replace the sum by a maximum.

### Why KL is necessary once the cap holds

Assume transfer and retain only the coordinates with \(\gamma_i\le K\), called the regular marginal. Transfer passes to marginal events by using cylinders in the full space. The discarded coordinates contribute only \(O(\log n)\) to KL, by (1) and (4). If the regular KL were not \(O(\log n)\), choose a subsequence where it divided by \(\log n\) tends to infinity. Additivity of \(B\) and (3) show that the same is true of the regular \(B=B_g\). For the regular log likelihood \(L_g\),
\[
       P_g[L_g\le B_g]\le e^{-B_g/2},
       \qquad Q_g[L_g>B_g]\le e^{-B_g}.
\]
The first inequality uses \(\mathbb E_{P_g} e^{-L_g/2}=e^{-B_g}\); the second integrates \(e^{-L_g}\) against \(P_g\) on the event. The regular event \(L_g>B_g\) therefore has \(P_g\)-probability tending to one and superpolynomially small \(Q_g\)-probability along this subsequence. This contradicts transfer and completes the proof.

## Interpretation and examples

* **One diverging ratio can be allowed.** Set \(s_1=1\), \(t_1^2=1/\log n\), and set \(s_i=t_i\) elsewhere. For large \(n\) the sole divergent coordinate contributes at most \(O(\log n)\) to both budgets by (4), so transfer holds under wrapping. It does not hold for the corresponding unwrapped real laws.
* **Individual caps are not enough.** For \(m=\lfloor\sqrt{\log n}\rfloor\) coordinates set \(s_i^2=(\log n)^{-1/2}\) and \(t_i^2=(\log n)^{-1}\), and match other widths. By data processing from the line the KL is at most \(m(\sqrt{\log n}-1-\log\sqrt{\log n})/2=O(\log n)\). All cap terms are individually \(\log n\), but their sum is of order \((\log n)^{3/2}\) at every fixed ratio cutoff. Taking \([1/8,1/4]\) in each of these coordinates provides a direct example with \(P_n(A)\ge n^{-C}\) and \(Q_n(A)\le e^{-c(\log n)^{3/2}}\).
* **An exact scalar budget after broad wrapping.** If all widths are bounded below by \(c>0\), the cap condition is automatic, and transfer is equivalent to
  \[
    \sum_i \left(e^{-\pi s_i^2}-e^{-\pi t_i^2}\right)^2=O(\log n).
  \]
  Indeed, the densities are bounded above and below by constants depending on \(c\), so KL is comparable to the squared \(L^2\) difference. With \(\alpha=e^{-\pi s^2}\) and \(\beta=e^{-\pi t^2}\), Parseval gives \(2\sum_{m\ge1}(\alpha^{m^2}-\beta^{m^2})^2\). Its first term gives the lower bound, and the squared derivative bounds are summable since \(\alpha,\beta\le e^{-\pi c^2}<1\).

This note is a comparison of standalone, independent centered probabilities on a product of circles. It does not apply to general correlated wrapped covariances, to a public parameter and its conditional error jointly, or to a proof that uses a finer observation than this wrapped projection. In particular it does not modify the stated guarantees of any hardness reduction. The square orthogonal quotient is one mathematical place where the model may occur; independence is a hypothesis, not a consequence of wrapping an arbitrary lattice.

## Relation to prior work

Peikert, Regev and Stephens-Davidowitz, [Pseudorandomness of Ring-LWE for Any Ring and Modulus](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf), §7 Claim 7.1, use transfer of non-negligible Gaussian mass **on the real vector space** under a uniform small relative width perturbation, tracing this to Lyubashevsky, Peikert and Regev, [On Ideal Lattices and Learning with Errors over Rings](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf), Claim 5.15 and Lemma 5.16. The unwrapped [companion note](gaussian-polynomial-event-transfer.md) treats arbitrary real covariance and means; its uniform bound on the upper variance ratio is not the wrapped threshold. The Rényi moment and tensorization arguments are standard (see van Erven and Harremoës, [Rényi Divergence and Kullback–Leibler Divergence](https://arxiv.org/abs/1206.2459)); the model-specific features here are the necessary aggregate cap for wrapped high-ratio coordinates and its sufficiency together with KL. A synthetic check is in verify-wrapped-gaussian-polynomial-transfer.js; the proof does not rely on numerical experiments.
