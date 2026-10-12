# Positive sextic Bellman envelope for projection body growth

**Author: mxym. 7 October 2026. AI-assisted research with exact arithmetic verification and a separate model-conducted audit.**

For the full class C generated from a point by finite Cartesian products, joins, and invertible affine maps between full affine hulls,

2.8534 < Gamma_C <= exp(104867/100000) < 142693/50000 = 2.85386.

The new homogeneous invariant is

log Q <= (431/10000)(D-H^2/D) + (9/2500)(D-H^4/D^3) + (197/100000)(D-H^6/D^5),

where D=d+1, H=1/a(K), Q=a(K)R(K)/g(d), g(d)=d^d/d!, and R(K)=|Pi K|/|K|^(d-1). The definitions, exact state calculus, complete product reduction, and spectral argument are in [the PDF](paper.pdf), [editable TeX](paper.tex), and [the reader proof](proof.md).

This is an additive continuation. The older public 2.855 proof and its certificates remain valid and unchanged. The strict lower construction is inherited; no new lower construction, exact optimum, unrestricted convex-body bound, rank-dropping affine-image theorem, or publication-priority claim is made. The former quadratic/quartic method floor is not an extremal lower bound. The sextic envelope is not pointwise below the preceding envelope at every state.

## Full certificates and independent audit

[Download the corrected complete archive](certificates-and-independent-audit.zip), including:

- All 19,900 finite rational tangent points and exact checker/report pairs
- The complete 5,164,290-byte certificate for all 157,872 imbalanced-tail cells, not a partial or sampled substitute
- The exact all-large Bernstein and exponential-endpoint checker/report pairs
- The complete separately written independent checker, audit, reports, and 28 corruption rejection cases
- All 63 byte-preserved supplied ancestor-source files

Corrected public archive SHA-256:

`b069821e04e84b4d55c97bafd0820969bacedae0dcc84652f6f3075e4af1b533`

Original supplied archive SHA-256: `a8a6a21ec3d512b2d2bcb60eca8b8c9f9cc780267324680b5ceafde7eb18c112`. The original has 143 entries and 61 of the 63 ancestor-source files. The corrected copy retains every original entry unchanged and adds exactly the two recovered ancestor package manifests. [The complete archive inventory](ARCHIVE_INVENTORY.json) records all 145 entries, both archive hashes, and the two additions with their exact hashes. The original ZIP is retained unchanged separately. Historical archive-root manifests are preserved as historical records; the external inventory provides complete corrected-archive coverage.

The archived `nonquartic_envelope_20261007/PROOF.md` and `sextic_bellman_independent_audit_20261007/AUDIT.md` are the frozen research proof and completed audit. Their historical statements that nothing was published describe that original checkpoint. This reader edition changes presentation and supplies pinned inherited dependencies. The two-file packaging repair does not alter the proof, checker, certificate, or audit inputs. [Audit summary](AUDIT_SUMMARY.md) distinguishes recorded full replays from release-assembly checks. [Source map](SOURCE_MAP.json) identifies all imported statements and content hashes.

## Verify

Python 3.10 or newer is sufficient for submitted proof checking and inherited lower replay. The separately implemented symbolic and large modes also require SymPy. SciPy and NumPy are unnecessary for verification; they were used only for numerical discovery of rational candidates.

From this directory:

```sh
python3 verify_release.py
python3 verify_release.py --quick --output /tmp/sextic-quick
python3 verify_release.py --full --output /tmp/sextic-full
```

The default checks release and historical archived manifests, the complete corrected-archive inventory and ZIP hash, all 63 ancestor-source pins, certificate parameters and counts, and an independent integer coverage/membership audit of every tail cell. It does not rerun the arithmetic certificate inequalities. `--quick` additionally reruns finite, all-large, symbolic, corruption/necessity, and inherited lower checks in ordinary and optimized Python, and deliberately omits full tails. Only `--full` performs new complete submitted and independent tail replays in both modes. Full replay can take substantial time. Output directories must be absent or empty and outside the frozen release directory. No input is overwritten, no source is fetched, and no discovery optimizer is trusted.

For manual replay, first extract the ZIP in an empty directory, preserving its two sibling roots. In `nonquartic_envelope_20261007`, run `python3 verify.py`; run it again under `python3 -O`. These submitted checks use only the standard library. From the extraction root, run the independent audit's `independent_check.py` with each mode `finite`, `tail`, `large`, and `symbolic`, followed by `adversarial_tests.py`; repeat under `-O`. Use a disposable extraction or direct reports to a separate output location. The release wrapper handles this isolation and compares reports automatically.

The bundled unmodified `dependencies/v2/code/check.py` and `dependencies/v2/certificates/exact.json` reproduce the inherited `2.8534 < Lambda < 2.8535` lower construction, including four corrupt-certificate controls. The lower construction is not a new result of this note.

## Rebuild the note

```sh
bash build.sh
```

Required TeX packages: `fontenc`, `lmodern`, `amsmath`, `amssymb`, `amsthm`, `geometry`, `microtype`, and `hyperref`. Build uses two `pdflatex` passes without shell escape and fixes PDF metadata to the note date. The same TeX installation reproduces the prepared PDF byte for byte. Different TeX versions can change PDF bytes without changing the proof. Exact arithmetic verification is independent of TeX. Build logs and caches are not publication files.

## Scope and attribution

The exact projection-body calculus, affine invariants, lower construction, and all-dimensional spectral reduction are entry 005 v2 work, pinned to commit `3360e7191cf564a46d09edcbfbd107c9178bd98f`. Their copies are in [dependencies/v2](dependencies/v2). The new positive sextic coefficient and finite/tail certificates adapt the preceding mixed quadratic/quartic machinery, which is preserved in the corrected public archive. Robbins' factorial inequalities remain an explicit analytic input: H. Robbins, “A Remark on Stirling's Formula,” American Mathematical Monthly 62 (1955), 26-29, [doi:10.2307/2308012](https://doi.org/10.2307/2308012).

Neither completed exact replay nor independent model-conducted audit constitutes human peer review or proof-assistant formalization.
