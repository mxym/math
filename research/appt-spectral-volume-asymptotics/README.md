# APPT spectral volume: sharp asymptotics and typical spectra

**Written analytic proof; not Lean-formalized.** This result uses flat Lebesgue measure on the eigenvalue probability simplex. It does not concern Hilbert–Schmidt or Bures measure on density matrices.

The preceding qutrit maximal-purity problem is already complete and published: proof Release `appt-qutrit-purity-complete-v1`, preprint DOI **10.5281/zenodo.23269470**. Those immutable artifacts are not changed here.

## Main result

For each fixed smaller local dimension m>=2, let D=mn with n tending to infinity. Put alpha=(m-1)/2, beta=(m+1)/2, R=m(m-1)/2, S=m(m+1)/2. Then

\[
V_{\rm APPT}(m,n)=C_m\sqrt D
 \left(\frac{\alpha^\alpha}{\beta^\beta}\right)^D(1+O_m(D^{-1})),
\quad C_m=\frac{\sqrt{2\pi}m^{m^2-1}\alpha^{R+1/2}\beta^{S-1/2}}{R!(S-1)!}.
\]

This gives the exponential rate and exact leading coefficient for every fixed m, not a set of numerical volume estimates. In particular,

\[
V_{\rm APPT}(2,n)\sim\frac{9\sqrt{3\pi}}2\sqrt n(4/27)^n,\qquad
V_{\rm APPT}(3,n)\sim\frac{2916\sqrt{3\pi}}5\sqrt n\,64^{-n}.
\]

The proof constructs an explicit containing affine simplex and proves that an asymptotically full fraction is genuinely APPT. A finite-dimensional error bound controls all physical PSD tests simultaneously through a Schur-complement estimate and exact Dirichlet moments. No chamber enumeration or numerical optimizer is a premise.

## Typical spectra and absolute separability

Absolutely separable spectra have the same exponential rate and square-root prefactor order, using Kondra et al.'s published spectral-ratio criterion. Their exact leading volume coefficient for m>=3 is not determined here.

Uniformly sampled APPT spectra and uniformly sampled absolutely separable spectra have the same limiting ordered profile:

\[
\max_i\left|D\lambda_i-\left(\alpha\log\frac\beta\alpha+
\log\frac\beta{\alpha+i/D}\right)\right|\longrightarrow0
\quad\text{in probability}.
\]

The scaled empirical eigenvalues have a truncated exponential limiting density. Typical scaled purity tends to `2-alpha*beta*(log(beta/alpha))^2`. This is a typical-spectrum law, not an extremal-purity bound. The limiting APPT-to-inner-polytope volume ratio is explicit: 3 for m=2 and 2187/40 for m=3.

## Proof and verification boundary

[PROOF.md](PROOF.md) contains the complete analytic argument and external inputs. The standard-library ancillary checker can be run by

```sh
python3 check.py --report verification/exact-checks.json
python3 -O check.py --self-test
```

It checks exact rational identities, slot coefficients, moment identities, empty-range cases, 36 finite dimension pairs / 2,760 simplex vertices, the special leading coefficients, and four deliberately incorrect controls. These finite checks support the calculations but do not replace the unbounded quantum/probability proof. No new Lean certificate is claimed.

## Research decision and attribution

The existing `../appt-all-dimensions/` results already settle all two-eigenvalue purity candidates but leave the multi-level global problem open. Three-level numerical searches in this cycle produced no certified counterexample or unrestricted upper bound. Rather than repeat the same search, the approach was reassessed and the complete fixed-local-dimension geometric law above was selected.

Hildebrand supplies the spectral APPT method; Ahiable–Kothakonda–Winter (arXiv:2608.03390v1) supply the permutation-invariant formulation and exact inner-polytope volume. Their Section 6.3 discusses volume comparisons numerically. Tran (arXiv:2609.18568) previously established the qubit order `Theta(sqrt(n)(4/27)^n)`. The absolute-separability consequence uses Kondra et al., arXiv:2605.29197v1, Supplemental Lemma 2. The new argument is the volume equivalence to the containing simplex, the general leading constant, and the conditional spectral limit shape. No exhaustive historical-priority certification is asserted.

The unrestricted arbitrary-dimension maximal-purity conjecture remains unresolved in this work. Equal typical profiles do not prove APPT=AS. There is no claim for proportional growth of both local dimensions, non-flat matrix measures, external peer review, or a new complete-Lean Release. AI assistance is disclosed. The frozen qutrit Lean theorem is a separate result and does not formally certify this analytic proof.
