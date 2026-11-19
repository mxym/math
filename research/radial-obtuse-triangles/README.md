# Which rotation-invariant law makes obtuse triangles least likely?

**Yongxian Zhang.** AI-assisted research manuscript, 19 November 2026. Independently checked internally by AI, not externally peer reviewed. No guarantee of priority.

In every sufficiently high dimension, choose three independent points uniformly on three concentric spheres of any prescribed positive radii. The probability that their Euclidean triangle is obtuse is smallest **exactly when the three radii agree**. Consequently the only minimizing nondegenerate iid rotation-invariant laws, up to translation and scaling, are uniform sphere laws. The proof covers arbitrarily extreme radius ratios without assuming bounded support. It does not give the first dimension from which the conclusion holds.

With $a=(d-1)/2$, the minimum is asymptotic to
$$
 \frac{9}{4\sqrt{\pi a}}\left(\frac{16}{27}\right)^a .
$$
The saddle is at pairwise direction dot product $-1/3$ for an obtuse angle at the opposite vertex. Merely substituting the usual nearly orthogonal angle into the known two-point-conditioned sphere integral gives a different exponential rate.

The [proof](PROOF.md) combines a twice-differentiable comparison near equal radii with a one-vertex lower bound away from that window. The underlying cap integral for equal radii is old. Greenwell treated concentric circles; Jandhyala proved the sharp concentric-spheres result in dimension three, where the deterministic equality class is larger. [Sources and scope](SOURCES.md) distinguish those results, Gaussian vertices, and uniform volume sampling. The unrestricted Lewis Carroll/Drivas–Retakh extremum is **not** determined here: a standard perturbation of known acute point sets already beats the best radial law exponentially.

[Internal review](REVIEW.md). To replay the finite rational checks:

~~~sh
sha256sum -c SHA256SUMS
python3 -O verify.py | diff - CHECKS.txt
~~~

Two exact expansions of the sphere value agree in 40 odd ambient dimensions. The script also checks algebraic identities for the saddle and the balanced-radius comparison. The general theorem is analytic, not inferred from those finite checks.
