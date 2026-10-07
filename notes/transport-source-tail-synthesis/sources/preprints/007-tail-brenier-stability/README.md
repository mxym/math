# Tail-sensitive convex-gradient interpolation and Brenier stability beyond bounded targets

**Latest: version 2, 2026-10-07.** Complete written proof draft, prepared with AI assistance; not independently peer reviewed or proof-assistant formalized.

[12-page PDF](v2/paper.pdf) · [Complete source](v2/main.tex) · [Build and theorem details](v2/README.md) · [Proof audit](v2/PROOF_AUDIT.md) · [Versioned release](https://github.com/mxym/math/releases/tag/tail-stability-20261007-v2)

## Main v2 advance: smoothness and full support do not suffice

For each dimension d>=2, one fixed strictly positive C-infinity source density on all of R^d, with Hessian of its negative logarithm at least I, has the following property: on exact unit-q-moment target classes, its optimal uniform power is `(q-2)/(3*q-2)` for every q>2. Two-atom targets witness failure of every larger exponent. The source is the same for all q and has no support boundary. At q=2 the same construction gives target distances tending to zero while map discrepancies stay bounded away from zero.

In contrast, the stated superquadratic product sources, including quartic confinement with unbounded Hessian, retain a sharp one-third exponent for every q>2. An integrable density translation-ratio condition explains the positive estimate. It is a sufficient condition, not a necessary-and-sufficient classification of every smooth source.

The counterexample's lower bounds are proved directly with explicit convex hinge potentials and exact two-atom costs. The matching upper estimates use the source potential-stability theorem from manuscript 001, with its dependency stated explicitly.

## Independent interpolation theorem

For finite convex potentials and a probability density with finite integrated coordinate-slice variation V, the squared gradient distance is bounded by

`12*d*delta^2/h^2 + 28*V*L^2*h + 4*tau(L)`

for every h,L>0. Here delta is centered L2 potential distance and tau is the actual second-moment gradient tail. This includes BV densities beyond log-concavity. The common interval on which both coordinate derivatives are bounded permits a sharp finite-moment potential-to-gradient exponent.

## Reconciliation with parallel work

Manuscript 001 v3, published at `5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3`, already contains the log-concave finite-moment transport estimate, hard-boundary sharpness examples, and Gaussian/global-bounded-Hessian one-third results. Those portions overlap 007 v1 and are not counted as a separate new project result. Version 2 credits that work and builds beyond it with the smooth full-support counterexample, superquadratic positive estimates, and the BV-density interpolation theorem. See the [comparison record](../../comparisons/2026-10-07-modulus-tail-reconciliation.md).

## Reproduce and preserve

From `v2/`:

```sh
python3 build.py
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
python3 ../v1/verification/check_interpolation.py --output verification/exact_checks.json
python3 verification/check_steep_example.py --output verification/steep_example_checks.json
```

The frozen v1 source is checked by Git blob identity during assembly. The exact regressions include 6000 piecewise-affine inequalities, 15 ramp cases, six exponent cases, 220 layer-parameter cases and 936 two-atom cost checks. They do not formalize the infinite analytic proof or compute the complete smooth density.

First v2 extension source: `c8d4fa9d7afc28d10123e666af0dfcdfc3f2681d`. Complete v2 assembly and audit: `e5695e2f013a7d0a9bda324f8459d3ff83a8be4f`.

[Historical v1 PDF](v1/paper.pdf), [source](v1/main.tex), and [audit](v1/PROOF_AUDIT.md) remain unchanged. First v1 source: `72eb17dfd6448f879192b6763b9b5c99b4c072f7`; release `modulus-tail-20261007-v1`.

Upstream licenses and notices remain applicable. No new license, priority certification, or journal-tier claim is implied.
