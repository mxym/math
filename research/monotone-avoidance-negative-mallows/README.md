# Few inversions under monotone-pattern avoidance: ground-state energy and the mesoscopic plot

Fix $d\ge3$ and forbid a decreasing subsequence of length $d+1$. Give each allowed permutation $\sigma$ of $n$ weight $e^{-b\operatorname{inv}(\sigma)/n}$ for fixed $b>0$. The leading exponential growth $d^{2n}$ does not see the bias. At the next scale the partition function satisfies
$$\log Z_n=2n\log d-b^{2/3}\Lambda_d n^{1/3}+o(n^{1/3}).$$
Here $\Lambda_d$ is the lowest Dirichlet eigenvalue of $-\Delta_E/d+d^{-1}\sum_{i<j}(x_i-x_j)$ on $\{x_1>\cdots>x_d,\ \sum_i x_i=0\}$, with the Euclidean metric in the sum-zero hyperplane $E$. This is an exact variational coefficient, not an elementary evaluation for arbitrary $d$.

Two consequences expose what the partition estimate measures. The tilted inversion count divided by $n^{4/3}$ concentrates at $(2/3)b^{-1/3}\Lambda_d$. Under the *uniform* avoiding law its lower tail satisfies, for each fixed $z>0$,
$$\lim_{n\to\infty} n^{-1/3}\log\Pr(\operatorname{inv}\le z n^{4/3})=-4\Lambda_d^3/(27z^2).$$

The diagonal limit hides a second feature: magnifying each signed displacement by recording $(\sigma(i)-i)/n^{1/3}$ gives a nontrivial empirical distribution. A uniformly sampled position has limiting macroscopic time uniform on $[0,1]$, independently of its canonical colour $J$ and rescaled displacement $dX_J$. Here $J$ is uniform on the colours and independent of $X$, whose density is the square of the normalized ground state of $-\Delta_E/d+bV$, with $V=d^{-1}\sum_{i<j}(x_i-x_j)$. The random empirical measure converges in probability. This is not a fixed-time or full path-process convergence claim.

The proofs also apply at $d=2$: $\Lambda_2=4^{-1/3}|a_1|$, where $a_1$ is the first negative Airy zero. At this width the coefficient already follows from the 321 area-path encoding and older area-tilted walk theory; the higher-rank permutation transfer is the point of this note. [Sources and a derivation of that prior implication](SOURCES.md).

- [Ground energy, inversion concentration and uniform lower tail](GROUND.md); [separate internal proof review](REVIEW.md).
- [Mesoscopic empirical plot](MESOSCOPIC.md); [separate internal review of this conclusion](MESOSCOPIC-REVIEW.md).
- [Finite verifier](check.py) and [expected output](CHECKS.txt). Run `python3 -O check.py` and `sha256sum -c SHA256SUMS`. Word identities are exact; printed spectra at width two are finite-dimensional floating diagnostics, not the justification for the eigenvalue theorem.

No universal forbidden-pattern, increasing-width, or crossover result is asserted. AI-assisted mathematical work and separate internal AI verification, not external peer review. No priority guarantee.
