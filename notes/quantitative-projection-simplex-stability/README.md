# Effective simplex rigidity for the projection cone invariant

**Additive supplement to entry 005, 7 October 2026.** This package does not assign a new version number or replace versions 2--4.

Read the [complete manuscript](paper.md) or [typeset PDF](paper.pdf). The theorem gives an explicit dimension-dependent modulus

$$E(K,S)\le G_d\bigl(a(K)-1/(d+1)\bigr)^{1/[d(d^2+2d+2)]}$$

for every full-dimensional convex body and every maximum-volume inscribed simplex. All constants and the local threshold are specified. The proof permits arbitrary surface area and cone-volume measures, including nonatomic ones.

The constants are deliberately crude. In dimension two, a reduction to Rogers--Shephard stability yields the stronger prior-work consequence $d_{BM}(K,T_2)\le1+576(a(K)-1/3)$, explicitly attributed to Böröczky. No novelty, optimality, dimension-uniform estimate, effective symmetric upper-end stability, or spectral optimum is claimed.

## Evidence and replay

- [Independent mathematical audit](INDEPENDENT_AUDIT.md)
- [Verification report](VERIFICATION.md)
- [Manifest](MANIFEST.json), which pins package bytes rather than certifying the theorem
- [Exact modulus checks](code/check_constants_and_gates.py)
- [Exact planar identity checks](code/check_planar_identity.py)

The mathematical checkers need only Python 3.10 or newer and its standard library. From this directory:

```sh
python3 code/check_manifest.py
python3 code/check_constants_and_gates.py
python3 -O code/check_constants_and_gates.py
python3 code/check_planar_identity.py
python3 -O code/check_planar_identity.py
python3 code/check_manifest.py
```

The scripts deterministically rewrite their respective JSON result files. Recorded reports confirm ordinary and optimized Python agree. The checks comprise seven dimensions of exact constants, 400 determinant perturbations, 400 barycentric matrices, 8,320 nonatomic box-corner signs, and 200 polygon identities. These are finite regression tests; the manuscript contains the general proof.

## Build

Run `sh build.sh` to regenerate `paper.tex` and `paper.pdf` from `paper.md`. Dependencies are Pandoc, pdfLaTeX, and the standard LaTeX packages used by the Pandoc template plus `amsmath`, `amssymb`, `microtype`, and `xurl`. The script includes a fallback for a TeX Live installation with missing format-cache configuration. The provided `paper.tex` is also an editable standalone LaTeX source.

The PDF has been rendered and checked on every page. The literature comparison is bounded and the manuscript is AI-assisted research, not external human peer review or formal verification.
