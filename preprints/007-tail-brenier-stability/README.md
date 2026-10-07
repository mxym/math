# Tail-sensitive convex-gradient interpolation and Brenier stability beyond bounded targets

**Version 1, 2026-10-07.** Complete written proof draft, prepared with AI assistance; not independently peer reviewed or proof-assistant formalized.

[Complete source](v1/main.tex) · [PDF](v1/paper.pdf) · [Proof audit](v1/PROOF_AUDIT.md) · [Exact finite checks](v1/verification/check_interpolation.py)

## Independent interpolation theorem

For finite convex potentials and a probability density with finite integrated coordinate-slice variation V, the squared gradient distance is bounded by

`12*d*delta^2/h^2 + 28*V*L^2*h + 4*tau(L)`

for every h,L>0. Here delta is centered L2 potential distance and tau is the actual second-moment gradient tail. This holds beyond log-concave densities, including BV probability densities. The proof clips the coordinate derivatives on each density superlevel interval; the common good set remains an interval.

Under a bounded pth gradient moment, p>2, the exponent `(p-2)/(3*p-2)` is sharp. An explicit one-dimensional boundary ramp proves sharpness, and p=2 cannot give a uniform potential-to-gradient modulus by moment control alone.

## Transport application and its dependency

Using the radius-independent potential estimate from manuscript 001, the same argument gives Brenier-map stability for unbounded targets with any p>2 in any dimension. Strongly log-concave sources and compact log-concave sources are covered. A tail-infimum modulus handles uniform integrability; stretched-exponential tails give one-third stability with a logarithmic correction.

**Sharpness of interpolation is not sharpness of the Wasserstein transport exponent.** The transport exponent is an upper bound; optimality is not established. Likewise the p=2 ramp is not a counterexample to uniform Brenier stability in Wasserstein distance. The application depends explicitly on manuscript 001 v2, source blob `d6896f8ac49e3a945324d5d57c54e1797775b1e5`, pinned commit `5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3`. It is not an external validation of that entire manuscript.

## Reproduce

From `v1/`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
cp main.pdf paper.pdf
python3 verification/check_interpolation.py --output verification/exact_checks.json
python3 -O verification/check_interpolation.py --cases 20 --output verification/optimized_mode_checks.json
```

The standard-library verifier performs 6000 rational piecewise-affine inequality checks, 15 exact boundary-ramp instances, and six exponent-identity cases. These are regression checks, not a machine proof of the coarea argument or the imported potential estimate.

## Disclosure and provenance

First complete source commit: `72eb17dfd6448f879192b6763b9b5c99b4c072f7`. The versioned release is `modulus-tail-20261007-v1`. The bounded-gradient finite-difference argument is attributed to manuscript 001 and OpenAI family 374; earlier transport interpolation literature is cited. Upstream licenses and notices remain applicable. No new license, priority certification, or journal-tier claim is implied.
