# Minimum-area planar sections of real ℓₚ balls near one and two

Which two-dimensional subspace cuts the least area from the unit ball of ℓₚⁿ? At $p=1$ the answer is known: the minimizing section is a regular $2n$-gon. [Chasapis, Nayar and Tkocz, §8](https://arxiv.org/abs/2109.05645v2) conjectured that the **same subspace** minimizes for every $0<p<2$. This note gives a proof in two dimension-dependent neighborhoods, not on the whole interval.

**Result.** For every fixed integer $n\ge4$ there are positive numbers $\eta_n,\varepsilon_n<1/2$ such that, if $|p-1|<\eta_n$ or $2-\varepsilon_n<p<2$, the unique minimum-area central two-dimensional section, up to ambient coordinate permutations and sign changes, occurs on the plane spanned by the columns of the matrix with rows

$$
\sqrt{\frac2n}\bigl(\cos(\pi j/n),\sin(\pi j/n)\bigr),\qquad j=0,\ldots,n-1.
$$

The interval around one is two-sided, including exponents for which the ball is not convex. No dimension-independent interval, explicit radius, or result for the intervening exponents is asserted. It is the **plane**, not the polygonal shape of the section, that persists. At two every plane has the same section area.

* [Proof near two](PROOF.md): at first order only the lengths of the frame rows are selected. At second order, the directions minimize an angular energy whose Poisson-kernel representation singles out the regular polygon on the circle of *doubled* angles. A positive transverse Hessian and symmetry turn asymptotic selection into exact minimization.
* [Proof near one](NEAR-ONE.md): retaining the two quadratic deficits in the known polygonal proof of Chasapis–Nayar–Tkocz (credited by them to Fedor Nazarov) gives strict curvature. Integrating in coordinates that move with each zero handles the nonsmooth radial integrand even below one.
* [Independent internal review](REVIEW.md), including an elementary second proof of the Poisson-kernel comparison and its curvature; [reproducible finite checks](CHECKS.md); [attribution and search scope](SOURCES.md).

**Status.** AI-assisted research draft with a separate adversarial AI-assisted internal review. No external peer review or proof-assistant certification. The checks corroborate specific identities, not the continuous optimization or the general theorem. No worldwide priority claim.

**中文摘要。** 对每个固定的 $n\ge4$，在 $p=1$ 的一个双侧邻域和 $p=2$ 的一个左邻域中，实 ℓₚⁿ 球面积最小的二维中心截面由同一个平面给出，除坐标符号和置换外唯一。$p=1$ 的定理已知；此处不证明全部 $0<p<2$，也不主张邻域对维数统一。
