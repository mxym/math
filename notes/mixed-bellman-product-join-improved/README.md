# Improved certified mixed Bellman ceiling

This supplement strengthens the published mixed quadratic/quartic Bellman
upper bound for entry 005's point-generated product/join class.

For
\[
D=d+1,\qquad H=1/a(K),\qquad
Q(K)=\frac{a(K)R(K)}{g(d)},\quad g(d)=\frac{d^d}{d!},
\]
it proves
\[
\log Q(K)\le
\frac{271}{6250}\left(D-\frac{H^2}{D}\right)
+\frac{5453}{10^6}\left(D-\frac{H^4}{D^3}\right)
\]
for every finite product/join expression generated from a point, up to
invertible affine equivalence. Consequently
\[
\boxed{2.8534<\Gamma_{\mathcal C}\le e^{1.048813}<2.854262.}
\]
The lower endpoint is inherited from the already certified self-similar
construction in 005 v2. The new contribution is the improved upper bound.

The proof is in `proof.md`. Exact certificate replay uses only Python's
standard library:

```sh
python3 verify.py
```

The finite certificate covers all 19,900 rectangles
\(1\le r\le s\le199\). The imbalanced-tail certificate has 22,311 dyadic
cells covering every \(1\le r<200,\ s\ge200\). The region
\(r,s\ge200\) is handled analytically with exact rational constant checks.
Both ordinary and optimized Python replays are required to agree byte for
byte on the finite and tail reports.

This is AI-assisted mathematical research. It is not external human peer
review or proof-assistant formalization, and it makes no claim about the
unrestricted class of all convex bodies or about optimality inside the
product/join class.
