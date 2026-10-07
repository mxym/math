# Version 2: smooth full-support counterexample and superquadratic positive results

Complete written research proof, 12 pages. Prepared with AI assistance; not independently peer reviewed or proof-assistant formalized.

## New mathematical content

Theorem 6.1 constructs ONE fixed strictly positive C-infinity source density on R^d, d>=2, whose negative logarithm has Hessian at least the identity. For EVERY q>2, the best possible uniform power on exact unit-q-moment target classes is (q-2)/(3q-2). Two-atom targets suffice. Thus smoothness, full support and strong log-concavity do not imply the finite-moment one-third estimate. The construction has no hard support boundary. Its lower bounds are proved directly, independently of the source potential estimate used for the matching upper bound.

Proposition 5.1 isolates an integrable translation-ratio condition. Corollaries 5.2--5.3 verify it for superquadratic confinement, including sources with unbounded Hessian. Each fixed product source of the displayed class has sharp one-third exponent in dimension at least two. The proof distinguishes sharpness for a particular fixed source from sharpness merely over a larger class containing a Gaussian.

Sections 1--4 retain the independent BV-density interpolation theorem and earlier tail bounds. The log-concave finite-moment transport estimates overlap manuscript 001 v3; they are not counted as a distinct new project result. That parallel source also already has hard-boundary sharpness examples and Gaussian/bounded-Hessian one-third estimates. Version 2 explicitly acknowledges these facts.

## Assemble, build and check

From this directory:

```sh
python3 build.py
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
cp main.pdf paper.pdf
python3 ../v1/verification/check_interpolation.py --output verification/exact_checks.json
python3 verification/check_steep_example.py --output verification/steep_example_checks.json
```

The workflow supplies a complete generated `main.tex` and `paper.pdf`. The frozen `core.tex` is byte-for-byte the v1 source (Git blob 2d6f87539f93f87b33e2484334542ab924143057). `build.py` verifies that identity before assembling it with `extension.tex` and explicit version/attribution updates. No download is needed to build the source.

`check_steep_example.py` checks 220 rational parameter cases and 936 two-atom coupling/map identities. It records the first two recursion stages without materializing astronomically large powers. The infinite smooth density and its tail limits are proved analytically, not numerically certified by these finite tests.

## Provenance

First public source of the new extension: commit c8d4fa9d7afc28d10123e666af0dfcdfc3f2681d. Parallel source 001 v3: commit 5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3, blob 0007edf5e28e4b4b0d34b2043cffd6e13e9f5aed. Historical v1 remains unchanged. See PROOF_AUDIT.md and the repository comparison record. No priority or journal-tier claim is made.
