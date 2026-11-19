# How much does requiring a star center to be an input point cost?

For a finite point set in Euclidean space, compare the least sum of distances from one **input point** with the least sum from **any center** (a geometric median). The supremum of their ratio over all finite sets in dimension \(d\) is the **star Steiner ratio** \(\rho_d\).

[The main theorem](PROOF.md) gives \(\rho_d=\mathbb E\|U-e\|\) for every integer \(d\ge3\), where \(U\) is uniform on the unit sphere and \(e\) is any unit vector. In particular \(\rho_3=4/3\). This matches the classical lower bound from approximately uniform spherical sets. It gives the three-dimensional conjecture of Fekete and Meijer and all dimensions **except the plane** in the general conjecture of Dumitrescu, Tóth and Xu. No assumption that the input lies on a single sphere is needed.

The upper bound comes from choosing the center with probability inversely proportional to its distance from a geometric median. A positive-definite kernel in the log-radii allows rotational averaging without requiring radii and directions to be independent. Concavity of the resulting scalar function gives the sharp bound. This main proof is analytic and does not depend on computation.

[The separate planar appendix](PLANE.md) gives only \(4/\pi\le\rho_2<2573/2000=1.2865\). It does not prove the conjectural planar value. Neither result concerns the Steiner-minimal-tree/minimum-spanning-tree ratio, matching ratios, or the optimum for a fixed number of points.

## Verification and status

See [the earlier results and search limits](SOURCES.md). This is an AI-assisted research draft with two internal mathematical reviews, not external peer review or a guarantee of priority. [Review 1](reviews/REVIEW.md) and its [signed-off delta](reviews/SUPPLEMENT.md), and [review 2](reviews/SECOND-REVIEW.md), track a preliminary proof and the final elementary positive-definiteness proof. The final proof is the one supplied here.

The numerical bound in the planar appendix can be checked in seconds with exact rational arithmetic. The independent checks on finite main-theorem examples are sanity checks, not the universal proof. From this directory, with standard Python 3:

```sh
python3 -B -O planar_check.py
python3 -B -O reviews/independent.py
python3 -B -O reviews/planar_tangent.py
python3 -B -O reviews/plane_interval_check.py
sha256sum -c SHA256SUMS
```

[Recorded checks](CHECKS.txt).
