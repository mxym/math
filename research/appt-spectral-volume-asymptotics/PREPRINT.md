# Public analytic preprint

[Read the signed manuscript](main.pdf) or its [standalone LaTeX source](main.tex).

**Sharp flat-spectral volume asymptotics and typical spectra of absolutely PPT states**, Yongxian Zhang, October 2026.

The complete written argument is in [PROOF.md](PROOF.md). It determines the sharp APPT spectral-volume asymptotics, including the leading coefficient, for every fixed smaller dimension m>=2, and a common typical spectral profile for APPT and absolutely separable states. The measure is flat on the eigenvalue simplex, not Hilbert–Schmidt or Bures measure. The AS result uses the cited spectral-ratio separability criterion.

The [verification summary](verification/ci-20261010/SUMMARY.json) binds the PDF to successful CI run 38021396667 and source 2fe75f6229e97acda054af1de846070ba11f00d6. Exact ancillary calculations and deliberately corrupted checker tests passed. This is a written analytic proof, **not a Lean certification or external peer review**. No arXiv submission or new DOI is asserted. The unrestricted general-dimensional purity conjecture remains unresolved here.

Build the manuscript with `python3 build_manuscript.py`, using Pandoc and pdfLaTeX; `main.tex` can also be compiled directly twice with pdfLaTeX. Check the inputs and ancillary calculations with `python3 verify_sources.py`, `python3 check.py`, and `python3 test_checker.py`.

The preceding qutrit purity proof Release and preprint DOI 10.5281/zenodo.23269470 remain unchanged. They are separate results and do not formally certify this paper. The manuscript includes the author's affiliation, funding statement, and AI-assistance disclosure.
