# The sharp curvature constant of the standard Chernoff density

For the density $f$ of the maximizer of standard two-sided Brownian motion minus $t^2$, let $\kappa(x)=-(\log f)''(x)$. This computer-assisted proof shows that its global minimum is attained **only at zero**, with

$$3.4051898<\kappa(0)<3.4051899.$$

Consequently the Gaussian factor in [Balabdaoui and Wellner's Conjecture 3.1](https://doi.org/10.3150/12-BEJ483) can have standard deviation $\sigma$ exactly when $\sigma\ge1/\sqrt{\kappa(0)}$. The authors had already estimated the origin curvature numerically. [Zhang and Zhou](https://arxiv.org/abs/2607.18619) proved strong log-concavity and a tail bound, which is an input here. The step established in this note is the sharp comparison with the origin on the remaining compact interval, not the existence of some positive uniform bound. No global monotonicity of curvature is claimed.

Read [the proof](PROOF.md) and [source comparison](SOURCES.md). On the compact interval, the argument uses a uniform analytic error bound for the Airy Fourier formula and exact directed interval arithmetic on closed subintervals, not numerical evidence from sampled points. This AI-assisted draft received a separate [internal AI mathematical/code audit](INDEPENDENT_REVIEW.md); it has not been externally peer reviewed or checked in a formal proof assistant. The source screen does not establish priority.

## Reproduce the finite certificates

Run the following from this directory. The primary Python checker uses the standard library only. The optional second checker is a standalone JavaScript implementation of the same mathematical argument, using different arithmetic precision, term accumulation, and mesh initialization.

```sh
python3 -I -B -O cert.py > python-replay.txt
diff -u CHECKS.txt python-replay.txt
node independent_review_check.js > js-replay.json
diff -u INDEPENDENT-CHECKS.json js-replay.json
```

The first check was run with CPython 3.12.14 and the second with Node.js 24.22.3. Both certify 128 cells near the origin and 582 cells farther out; the reported subdivision depths differ because the initial meshes differ. The JS field `orig_scaled1e14` gives outward-rounded integer bounds with denominator $10^{14}$. Other decimal diagnostics are for display, not inputs to the proof decisions. [SHA256SUMS](SHA256SUMS) pins the included artifacts.
