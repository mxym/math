# Proof and assembly review: critical slowly varying boundary sources

7 October 2026. Scoped pass within the two explicitly imported public proof inputs. This is an independent model reconstruction followed by a full assembled-source review, not external peer review or formal verification.

## Final identities

- Source SHA-256: `68923efde65df299b9de5c6b4b21fa9ec60b1960dc2c97c9af24118899e0d5ad`
- PDF SHA-256: `287d391c841cf3e5497813eeeac20919f8d3ece4acf4d85f88131899da3d4e75`
- [Six-page paper](../notes/critical-boundary-slow-variation/manuscript.pdf), [source](../notes/critical-boundary-slow-variation/manuscript.tex), [artifact checks](../notes/critical-boundary-slow-variation/QA.txt).

## Decisive analytic checks

1. The two log-derivative hypotheses permit a globally strongly convex C2 potential on the open half-line with the exact prescribed density near zero and a quadratic tail. C-infinity is claimed only with the additional smoothness hypothesis. The source has a genuine boundary and is not asserted to be smooth across it.
2. Elementary integration of the small log derivative proves fixed-ratio slow variation, the near-zero integral bound, L(h)/H(h) tending to zero, and eventual invertibility of F. Neither monotonicity of L nor divergence of H is assumed. The inverse comparison is valid for each fixed multiplicative rescaling.
3. The zero-extended root translation norm is bounded using the emerging boundary interval and the integral of its classical derivative away from zero. The transport upper estimate uses the precisely stated all-P2 potential theorem in 001 v3 and the overlap inequality in 008; density regularity alone is not substituted for that input.
4. Every dyadic strip solves two cumulative mass equations. Local derivative bounds are uniform in the number of scales, and one fixed sufficiently small width-to-last-location ratio makes the symmetric-difference leading term positive. The raised planes are realized by two global convex maxima. All central and outer target labels match exactly.
5. Geometric slope sums yield a pth-moment budget proportional to the dyadic sum of L. The capped interval below the final cusp contributes at most the last summand. Normalization preserves uniform constants. Choosing the integer number of scales from each h, then using the inverse F, proves a lower bound for every sufficiently small distance; it is not merely a sequence argument.
6. The logarithmic hierarchy follows by exact integration. At the critical inverse-log factor, the iterated logarithm is necessary. The pure one-third equivalence follows from the sharp modulus and the root derivative's asymptotic integrand L(x)/x, including the zero trace. It is a necessity statement only within this family.
7. For L(x)=exp([log(1/x)]^alpha), one half < alpha < one, the computed inverse shift makes H(h_w)/H(w^(2/3)) diverge. The warning against that simplification is proved, not heuristic.

The final editorial diff only supplies the explicit small-interval quantifier in the Potter estimate and names the two normalized map/target distances. No proof correction was required. All six pages were inspected; the final separate build reproduces the layout text and has a clean log. All 24 labels and three citations resolve. The archive and release hashes were checked. Numerical tests are not substituted for the analytic all-scale statements.

## Attribution and limits

The multiscale mass-matching mechanism and overlap interpolation belong to 008 v1; the all-P2 potential theorem belongs to 001 v3 and retains its published verification status. Their exact versions and Git pins are linked in the paper. The supplement proves the varying-factor estimates, normalization and inversion. It does not claim a new basic multiscale mechanism, a general characterization of all stable sources, fixed atom-count sharpness, optimal numerical constants, novelty certification or publication priority. Every historical version file remains unchanged.
