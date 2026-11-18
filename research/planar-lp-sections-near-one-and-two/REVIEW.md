# Independent internal review of the two neighborhood proofs

**Status.** A separate AI-assisted internal review reconstructed the two arguments and found no mathematical gap in their stated fixed-dimension ranges. This is not external peer review or formal verification, and no claim of priority is made. Below is the alternate angular proof and a record of specific failure modes checked.

## An elementary angular proof

This gives the Poisson minimization and its needed local curvature independently of both the Cohn–Kumar theorem and the residue-class Hessian calculation in [the main proof](PROOF.md).

Fix $0<r<1$, put $a=(1+r^2)/(2r)>1$, and discard the positive prefactor in the Poisson potential to obtain $f(\cos\theta)=1/(a-\cos\theta)$. With $T_k$ the Chebyshev polynomial, set

$$
Q(\cos\theta)=\frac{T_n(\cos\theta)-1}{\cos\theta-1}
 =\left(\frac{\sin(n\theta/2)}{\sin(\theta/2)}\right)^2
 =n+2\sum_{k=1}^{n-1}(n-k)\cos(k\theta),\qquad
g(t)=\frac{1-Q(t)/Q(a)}{a-t}.
$$

Use $Q(1)=n^2$ by continuity. Here $Q(a)>0$, $Q$ is nonnegative on $[-1,1]$, and $g$ is a polynomial of degree $n-2$. To see that $g(\cos\theta)$ has nonnegative Fourier coefficients, write $a=\cosh v$ with $v>0$. Then

$$
\frac{T_k(a)-\cos(k\theta)}{a-\cos\theta}
 =\left|\frac{\sinh(k(v+i\theta)/2)}{\sinh((v+i\theta)/2)}\right|^2
 =\left|\sum_{j=0}^{k-1}e^{(k-1-2j)(v+i\theta)/2}\right|^2.
$$

Expanding this square gives positive terms at integer frequencies. Form the positive linear combination specified by $Q$ to obtain the claim about $g$.

Summing $g$ over all ordered pairs of $n$ sites (including the diagonal) gives a constant plus a nonnegative linear combination of $|P_k|^2$, $1\le k\le n-2$. The regular configuration kills all those terms. Subtracting the common diagonal sum does not change the comparison. At each off-diagonal pair the residual is

$$
f(\cos\theta)-g(\cos\theta)=\frac{Q(\cos\theta)}{Q(a)(a-\cos\theta)}\ge0 .
$$

It vanishes at every nonzero regular angle difference, but not at zero. Thus the full Poisson energy is minimized at the regular configuration, including against repeated sites. In fact equality forces every off-diagonal difference to be a nonzero multiple of $2\pi/n$, which determines the regular polygon.

The residual also has a strict quadratic zero as a function of the angle at each such difference (including $\pi$ for even $n$). Therefore in a sufficiently small fixed neighborhood of regular, the **excess** of the Poisson pair sum bounds $c(r,n)\sum_{i\ne j}(\eta_i-\eta_j)^2$ from below: the $g$-excess is nonnegative and the residuals sum to this bound. Restoring the positive Poisson prefactor preserves it. The bound is uniform in $r\in[1/3,2/3]$ by the explicit formula and compactness. For centered tuples divide the Poisson excess by $2r^2$ (frequency one vanishes), then integrate against the measure $\mu$ of Section 2; outside the indicated interval the integrand is nonnegative. Since this interval has positive $\mu$-mass, the energy gap controls the squared norm of the mean-zero angular increments near regular. In particular it controls that of their projection $y$ along the equal-weight tight submanifold. This independently gives the angular coercivity used at two. The argument is a special case of the auxiliary-polynomial method, not a new general optimality principle.

## Additional checks on possible failure modes

* **Compactness before local Taylor estimates.** The global expansion at two needs only uniformity of function values, not derivative bounds at frames with zero or repeated rows. In the two successive comparisons, $(A-A_{\min})/\delta$ is discarded with the correct sign. Existence uses compactness of the orthonormal frame space and joint continuity of the radial area integral.
* **Energy and normalization.** Polar area is $\pi$ times the normalized angular mean of the squared radius. The radial formula has exponent $-1/(1-\delta)$, not $-2/(1-\delta)$. In Parseval the two conjugate Fourier coefficients give $w_*^2/2$. The six-factor moment record begins at $k=2$. Universal Poisson comparison is made first on *all* tuples; only afterwards is $P_1=0$ used. Equality of continuous nonnegative Poisson excesses on a full-support measure yields equality for every $r$; Newton's identities exclude collisions.
* **Constraint chart and Hessian.** The chart has $(n-1)+(n-3)=2n-4$ coordinates. The first angular harmonic solves the complex tightness equation by an invertible real differential; the remaining angular variables transform cyclically just as their projection does. The regular point is stationary at each exponent, not just in the limit. The ambient angular gradient vanishes at regular, so chart acceleration adds no term in differentiating $\mathcal E$. The residue average counts the self-conjugate mode exactly once for even $n$. The mixed Hessian penalty has order $\delta^2|U||H|$ and costs only $O(\delta^3)|H|^2$ after consuming part of the order-$\delta$ weight term.
* **Moving cusps.** On a fixed local chart the $2n$ zero rays are uniformly separated. A disjoint cutoff around each ray translates with it, making the only non-smooth spatial factor independent of the chart variables. Powers multiplied by up to three logarithms are uniformly bounded for exponents bounded away from zero. The residual cutoff and all its differentiated terms vanish near the zeros. Nothing requires twice differentiating $|s|^p$ with respect to $s$ below one.
* **Quantitative use of the known $p=1$ proof.** The triangle factor is $4\sin^3\beta/\cos\beta$, and the full reciprocal-radius integral is $4\sum\sqrt{w_j}$. The $2n$ half-apertures use one quarter of the *doubled* angle gaps, each twice. The weight and aperture bounds enter the area excess with the same sign; rotation is removed by the cyclic Poincaré inequality. This supplies true Hessian positivity at one instead of inferring it from bare uniqueness.
* **Equality and scope.** The only continuous freedom removed is the choice of orthonormal basis of the plane; the ambient equivalences remaining are coordinate permutations and sign changes. At two every plane gives area $\pi$. The two interval widths are dimension-dependent and non-effective. Neither proof concerns the remaining exponents, noncentral sections, complex spaces, the general hyperplane problem or any claim to external priority.

The [exact and optional numerical checks](CHECKS.md) corroborate parts of these calculations. The local-to-global arguments are analytic; the finite tests do not establish them.
