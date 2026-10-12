#!/usr/bin/env python3
"""Typeset the published analytic proof. Requires Pandoc and pdfLaTeX.

This build is not a mathematical proof checker. It retains its exact proof input,
LaTeX source and compilation logs for separate human inspection.
"""
from pathlib import Path
import hashlib
import json
import subprocess
from format_inline import render

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'manuscript-build'
OUT.mkdir(exist_ok=True)
proof=render((ROOT/'PROOF.md').read_text())
metadata='''---
title: "Sharp flat-spectral volume asymptotics and typical spectra of absolutely PPT states"
author: "Yongxian Zhang"
date: "October 2026 — Version 1"
fontsize: 11pt
geometry: margin=1in
colorlinks: false
---

School of Computer Science and Engineering, South China University of Technology, Guangzhou, China. Correspondence: mxymmxym1@gmail.com. ORCID: 0009-0000-3864-3536.

**Abstract.** We determine the sharp asymptotic flat-spectral volume of absolutely positive-partial-transpose (APPT) states for every fixed smaller local dimension, including the leading coefficient and a relative error of order inverse total dimension. A full-rank Schmidt test defines an explicit containing affine simplex; a uniform Schur-complement estimate and Dirichlet concentration show that its non-APPT fraction vanishes at that rate. We also obtain a common conditional spectral limit shape for APPT and absolutely separable states, a truncated exponential limiting eigenvalue density, typical purity, and an exact asymptotic comparison with the known inner polytope. The separability consequence uses an established spectral-ratio criterion. These are analytic proofs, not Lean formalizations. The unrestricted maximal-purity conjecture and equality of APPT and absolute separability remain separate unresolved problems.

'''
disclosure='''

## Disclosure and availability

This research was conducted independently and received no external funding. AI assistance was used for research exploration, analytic derivation, exact-checker development, and manuscript preparation. The claims are presented for independent mathematical scrutiny; no external peer review is represented. The preceding qutrit Lean theorem is distinct from the present analytic proof. Sources, exact ancillary checks, deliberate-error controls, and verification records are available in the public repository `mxym/math`, under `research/appt-spectral-volume-asymptotics/`. No new blanket license or arXiv submission is asserted.
'''
(OUT/'manuscript.md').write_text(metadata+proof.split('\n',1)[1]+disclosure)
header=r'''\usepackage{amsmath,amssymb}
\usepackage{microtype}
\providecommand{\down}{\downarrow}
\setlength{\emergencystretch}{3em}
'''
(OUT/'header.tex').write_text(header)
commands=[['pandoc','manuscript.md','--from=markdown+tex_math_single_backslash','--standalone','--to=latex','--include-in-header=header.tex','-o','main.tex'],
          ['pdflatex','-interaction=nonstopmode','-halt-on-error','main.tex'],
          ['pdflatex','-interaction=nonstopmode','-halt-on-error','main.tex']]
checks=[]
for i,command in enumerate(commands):
    log=OUT/f'build-{i}.log'
    with log.open('w') as stream:
        result=subprocess.run(command,cwd=OUT,stdout=stream,stderr=subprocess.STDOUT,timeout=180)
    checks.append({'command':command,'exit_code':result.returncode,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()})
    if result.returncode:
        raise RuntimeError(log.read_text()[-5000:])
report={'status':'PASS','scope':'Typesetting build only; analytic proof and exact ancillary checks are separate',
        'proof_sha256':hashlib.sha256((ROOT/'PROOF.md').read_bytes()).hexdigest(),'checks':checks,
        'outputs':{name:hashlib.sha256((OUT/name).read_bytes()).hexdigest() for name in ['manuscript.md','header.tex','main.tex','main.pdf']}}
(OUT/'BUILD.json').write_text(json.dumps(report,indent=2)+'\n')
print('MANUSCRIPT_BUILD_PASS')
