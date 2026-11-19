# Acute triangles from true surface area on ellipsoids

The sphere is a **strict local maximizer**, among ellipsoids in each fixed ambient dimension \(d\ge2\), of the probability that three independent points sampled from normalized **boundary area** form an acute triangle. Translations, rotations and common dilations are immaterial.

The first nonzero variation is quadratic for \(d\ge3\), but quartic in the plane. For a planar ellipse with semiaxes \(e^{t/2},e^{-t/2}\),
\[
p(t)=\tfrac14-\tfrac{37}{16\pi^2}t^4+O(|t|^5).
\]
In three dimensions, for ellipsoids \(\exp(tH/2)S^2\) with \(H\) symmetric traceless, the quadratic loss is \((11/175)\operatorname{tr}(H^2)t^2\). In higher dimensions the proof gives a strict quadratic loss for every nonzero traceless deformation. The key change from affine pushforward sampling is that stretching also changes the sampling density: in dimension two its quadratic contribution cancels the metric effect.

Read [the higher-dimensional proof](PROOF-ALL.md) or [the planar computation](PROOF-PLANAR.md). The [independent review](REVIEW.md) derives the planar coefficient by a second method, without a clipped endpoint. The frozen proof files retain their original private-draft headers for checksum continuity. This is AI-assisted work with internal mathematical review only. No external review or priority claim.

**Limits.** This says nothing about arbitrary axis ratios or general convex hypersurfaces. It is not Hall's conjecture for volume-uniform points in a solid convex body. [A 2024 question and Christophe Boilley's 2025 answer](https://math.stackexchange.com/questions/5014676/probability-that-triangle-on-ellipse-is-acute) already give the true-perimeter ellipse setting and a conditional arc integral. [Akopyan, Edelsbrunner and Nikitenko](https://doi.org/10.1080/10586458.2021.1980459) prove the spherical three-dimensional probability and use the different homeoid measure on ellipsoids. See [scope and corpus](SOURCES.md) and the [review's source discussion](REVIEW.md).

**Reproduction.** With Python 3 and SymPy for the planar independent calculation:
```sh
sha256sum -c SHA256SUMS
python3 -B -O check_planar.py
python3 -B -O check_odd.py
python3 -B series.py
```
The first two programs explicitly check their exact coefficients, even in optimized Python. The third reproduces the planar proof's Laurent arithmetic. The finite odd-dimensional checks supplement the analytic proof for all dimensions; they do not substitute for it.
