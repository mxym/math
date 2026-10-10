#!/usr/bin/env python3
"""Typeset the complete analytic argument; does not run or replace proof checks."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess

ROOT=Path(__file__).resolve().parent
HEADER=r'''\documentclass[11pt]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{lmodern}
\usepackage[margin=1in]{geometry}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{microtype}
\usepackage[hidelinks]{hyperref}
\usepackage{bookmark}
\hypersetup{pdftitle={Global-unitary entanglement extraction: capacity and the exact PPT fidelity exponent},pdfauthor={Yongxian Zhang},pdfsubject={Written analytic proof, not Lean-formalized},pdfkeywords={entanglement extraction, global unitary, complete PPT, fidelity exponent}}
\usepackage{longtable,booktabs,array}
\setlength{\emergencystretch}{2em}
\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}
\setcounter{secnumdepth}{0}
\title{Global-unitary entanglement extraction:\\capacity and the exact PPT fidelity exponent}
\author{Yongxian Zhang\thanks{School of Computer Science and Engineering, South China University of Technology, Guangzhou, China. Email: \href{mailto:mxymmxym1@gmail.com}{mxymmxym1@gmail.com}. ORCID: \href{https://orcid.org/0009-0000-3864-3536}{0009-0000-3864-3536}.}}
\date{October 2026}
\begin{document}
\maketitle
\begin{abstract}
We determine the faithful entanglement-extraction capacity when arbitrary collective global-unitary preprocessing on an existing bipartite system is followed by local channels, LOCC, or a completely PPT channel. For every fixed $2\le m\le n$ and every input spectrum $p$, including zero eigenvalues, these three capacities equal
$\min\{\log m,[\log(mn)-H(p)]/2\}$.
We also determine the exact completely-PPT target-fidelity exponent at every rate. For $0\le R\le\log m$ it is
$\max_{1\le\alpha\le2}(\alpha-1)[2R-\log(mn)+S_\alpha(p)]/\alpha$;
above $\log m$ it is linear with intercept determined by the optimal logarithmic-negativity rate. The proof combines the Rains fidelity-effect SDP with a spectral-prefix approximation, a random Bell-projection construction using the matrix Bernstein inequality, and exact matching by spectral types and escort distributions. A separate deterministic local Kraus construction proves faithful achievability. The global preprocessing is part of the operation class: this is not a formula for ordinary mixed-state LOCC distillation. The exact exponent is claimed for completely PPT channels, not for LOCC. Exact ancillary checks are supplied; the analytic theorem is not Lean-formalized or externally peer reviewed.
\end{abstract}
'''
FOOTER=r'''
\section*{Verification scope and disclosures}
The mathematical argument uses the stated external matrix Bernstein theorem, together with finite-dimensional matrix analysis. The ancillary program independently checks full rational Choi and partially transposed Choi matrices, deterministic local Kraus maps, small cyclotomic Bell-projector identities, exact constants, type cardinalities, and escort algebra; it also rejects deliberately corrupted inputs and source programs. These checks do not by themselves certify the unbounded analytic theorem. The present work is not Lean-formalized and has not been externally peer reviewed.

This research was conducted independently and received no external funding. AI assistance was used in research exploration, proof development, ancillary programming, and manuscript preparation. The affiliation identifies the author's institution of study and does not imply institutional commissioning or endorsement.

The complete proof, source, and ancillary checks are available in the repository \url{https://github.com/mxym/math}, directory \texttt{research/global-unitary-ppt-extraction}. The preceding qutrit APPT purity theorem and its immutable Lean release are separate results and do not formally certify this paper.
\end{document}
'''

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--tex-only',action='store_true')
    args=ap.parse_args()
    source=(ROOT/'PROOF.md').read_text()
    body=source[source.index('## 1.'):]
    result=subprocess.run(['pandoc','--from','markdown+tex_math_dollars+tex_math_single_backslash','--to','latex','--wrap=none'],input=body,text=True,capture_output=True,check=True,timeout=60)
    rendered=result.stdout
    tex=HEADER+'\n'+rendered+'\n'+FOOTER
    (ROOT/'main.tex').write_text(tex)
    if args.tex_only:return
    env=os.environ.copy();env['SOURCE_DATE_EPOCH']='1791504000';env['FORCE_SOURCE_DATE']='1'
    logs=[]
    for passno in (1,2):
        process=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','main.tex'],cwd=ROOT,env=env,capture_output=True,text=True,timeout=120)
        logs.append(process.stdout+process.stderr)
        if process.returncode:
            (ROOT/'manuscript-build.log').write_text('\n'.join(logs))
            raise RuntimeError('LaTeX failed:\n'+logs[-1][-6000:])
    (ROOT/'manuscript-build.log').write_text('\n'.join(logs))
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    report={'status':'PASS','scope':'Manuscript compilation only, not proof verification','inputs':{p:sha(ROOT/p) for p in ['PROOF.md','build_manuscript.py']},'outputs':{p:sha(ROOT/p) for p in ['main.tex','main.pdf']},'pandoc':subprocess.check_output(['pandoc','--version'],text=True).splitlines()[0],'pdflatex':subprocess.check_output(['pdflatex','--version'],text=True).splitlines()[0]}
    (ROOT/'verification').mkdir(exist_ok=True)
    (ROOT/'verification/manuscript-build.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
