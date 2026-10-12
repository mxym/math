# A certified mixed Bellman envelope for projection-body growth

This clean publication candidate provides a complete English proof in `paper.pdf`, editable LaTeX in `paper.tex`, and the original Markdown argument in `proof.md`. The class consists of bodies generated from a point by finite products, joins, and **invertible affine maps on their affine hulls**. These are affine equivalences; rank-dropping affine maps are outside the claimed class.

The original audited candidate remains immutable, with ZIP SHA-256 `fd67965b11233d115194b69b3fcd64ad4236783fadf858debfb12a0f2125e5cb`. This package is a faithful typesetting and portability assembly with the class-scope clarification requested by the parent's separate adversarial audit. The parent reports that a separate reimplementation, importing none of the candidate checker code, passed all finite rectangles and tail cells in normal and optimized Python and rejected 24 corrupted cases; its full audit report is maintained separately. No push or publication has been performed.

The new theorem for the entire point-generated product/join class is
\[
\log Q(K)\le\frac{49}{1000}D-\frac{87}{2000}\frac{H^2}{D}
-\frac{11}{2000}\frac{H^4}{D^3},
\qquad D=d+1,\ H=1/a(K).
\]
Consequently
\[
2.8534<\Gamma_{\mathcal C}\le e^{1049/1000}<2.855.
\]
This strictly improves the actual public quadratic ceiling, because
\((11/85)\log(189/128)>49/1000\). It does not improve the known lower construction or determine the optimum. The mixed-potential numerical direction was already recorded publicly; the contribution is complete exact certification over all recursive trees.

Read `proof.md` for the complete English proof, `combined_audit.md` for the component audit, and `PUBLIC_AUDIT.md` for the parent's independent adversarial reimplementation summary. `literature.md` compares current primary sources and acknowledges their limits. The most recently inspected public head is `3360e7191cf564a46d09edcbfbd107c9178bd98f`; `provenance.json` records the moving-head checks and proof inputs.

Run the complete exact verification from this directory:

```sh
python3 verify.py
```

Python 3.10 or newer and the standard library suffice. This runner checks file hashes and protected original inputs, then runs every new proof checker normally and under `python -O`; mathematical checks use explicit exceptions and remain active. The normal and optimized finite reports must agree exactly. The runner uses temporary output files and leaves the delivered certificate files intact. It can be invoked from any working directory using its path; no checkout or network connection is needed.

The proof evidence covers 19,900 complete finite state rectangles, 15,568 dyadic cells covering every remaining small-factor tail, and an analytic proof when both dimensions are at least 160. The checks include all real auxiliary states through concavity and interval bounds, rather than relying on a sampled grid.

Direct commands are also available:

```sh
python3 check_finite.py mixed_finite_points.json --quiet --report finite_replay.json
python3 check_mixed_tail.py
python3 check_mixed_large_dimensions.py
```

The two `generate_*.py` scripts are optional discovery tools requiring SciPy. Their floating optimization only proposes rational supporting points, and their convergence is not a proof assumption. Proposals must pass the exact checkers. Regeneration can choose different valid points or subdivisions across SciPy versions; the saved rational certificates and their exact replay are the authoritative evidence.

`primary_source_manifest.json` records the primary literature downloads inspected during research. Copyrighted primary PDFs are not included; `literature.md` links the original sources. `inherited_lower_replay.json` records successful replay of the existing v2 lower-rate certificate. The new upper verification does not require executing the prior lower checker.

## PDF build and dependencies

Run `bash build.sh` to build `paper.pdf` from `paper.tex`. The script runs `pdflatex` twice, writes temporary TeX output to `build/`, and copies the finished PDF beside its source. No shell escape or external download is used. The required TeX packages and every imported mathematical result are listed in `DEPENDENCIES.md` with complete hypotheses, precise uses, pinned sources, and hashes.

Verify the as-delivered package before rebuilding the PDF. TeX versions and PDF metadata can change the rebuilt PDF's bytes, so a rebuilt file need not match the delivery manifest. This does not alter the exact arithmetic certificates; byte-identical PDF regeneration is not claimed.

`SOURCE_MAP.json` maps immutable candidate inputs to the publication files. `VERIFICATION.md` documents certificate roles and individual commands; `MANIFEST.json` records the publication file hashes. All executable paths are local to this package.

The intended additive repository destination is `notes/mixed-bellman-product-join/`. The ZIP places these files under that directory. No numbered entry-005 version or shared catalogue file is part of this assembly; those release decisions belong to the parent thread.

Authorship: mxym repository account, prepared with AI assistance; no institutional affiliation, external human peer review, or proof-assistant formalization is asserted.

No repository content was edited, no push or publication was performed, and the old saved project was neither inspected nor resumed. The work was carried out in a separate temporary math directory. The exact optimal constant remains unresolved; there is no remaining mathematical or delivery blocker for the displayed upper theorem.

中文状态：已严格证明全 product/join 类的新上界 \(\Gamma_{\mathcal C}\le e^{1.049}<2.855\)，精确改善公开二次势上界。全部维数、连续辅助参数及两种 Python 模式均通过；未改善下界、未断言最优、未发布或推送。
