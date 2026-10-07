# Modulus-controlled nonlinear avoidance and a differentiability boundary for null patterns

**Version 1, 2026-10-07.** Complete written proof draft, prepared with AI assistance; not independently peer reviewed or proof-assistant formalized.

[Complete source](v1/main.tex) · [PDF](v1/paper.pdf) · [Proof audit](v1/PROOF_AUDIT.md) · [Exact finite robust-cover checker](v1/verification/check_robust_cover.py)

## Main result

Positive upper Banach density of occupied logarithmic annuli permits a near-full-measure periodic set avoiding every finite-order image with any prescribed countable family of vanishing remainder moduli. The same set excludes all nonflat smooth germs, nonconstant analytic germs, and C^(1,alpha) germs with nonzero derivative, for every alpha>0. Every such image has infinitely many points outside the avoiding set. Countably many prescribed configurations can be handled simultaneously.

The proof is stronger than affine avoidance: the perturbation may be chosen independently at every input point. Uniform-tail template placement makes a finest-grid buffer cost arbitrarily little measure. The finite routing mechanism is reproved and attributed to OpenAI family 084 and manuscript 004.

The boundary statements matter. Lacunary sequences do embed into every positive-measure set by an increasing C^1 diffeomorphism. Arbitrary null sequences embed by a strictly increasing smooth map flat at zero. Thus we do not claim avoidance of all C^1 maps or all smooth maps. The positive C^1 construction is closely related to Feng--Lai--Xiong (IMRN 2024) and is not advertised as a new mechanism. Configurations with logarithmic indices n^2 or 2^n remain outside the density hypothesis.

## Reproduce

From `v1/`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
cp main.pdf paper.pdf
python3 verification/check_robust_cover.py --self-test --output verification/self_test.json
python3 verification/check_robust_cover.py verification/toy_robust_certificate.json
```

The checker uses standard-library Fraction arithmetic and closed half-plane intersection. Nine regression cases retain singleton and error-endpoint failures. The density-9/10 toy with common uncertainty radius 1/100 is not a computed small-density witness for the full theorem.

## Disclosure and provenance

First public core proof record: commit `61eb89311e19eb6539b97acb46207197b0508d64`. First complete manuscript source: `478be8879564e99843ad0bc69ca6192379e5b59e`. Cite a fixed commit, not the changing main branch. The versioned release is `modulus-tail-20261007-v1`.

OpenAI source snapshot: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; manuscript 004 snapshot: `e894ed8678052e45ecd9f1714b6a996cfea33cf3`. Upstream licenses and notices remain applicable. No new license for newly authored material, first-priority claim, or journal-tier claim is implied.
