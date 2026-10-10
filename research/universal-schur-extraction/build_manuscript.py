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
\hypersetup{pdftitle={State-independent entanglement extraction: exact exponents, reliability and a Gaussian threshold},pdfauthor={Yongxian Zhang},pdfsubject={Written analytic proof, not Lean-formalized},pdfkeywords={universal entanglement extraction, Schur-Weyl, reliability, Gaussian threshold}}
\usepackage{longtable,booktabs,array}
\setlength{\emergencystretch}{2em}
\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}
\setcounter{secnumdepth}{0}
\title{State-independent entanglement extraction:\\exact exponents, reliability and a Gaussian threshold}
\author{Yongxian Zhang\thanks{School of Computer Science and Engineering, South China University of Technology, Guangzhou, China. Email: \href{mailto:mxymmxym1@gmail.com}{mxymmxym1@gmail.com}. ORCID: \href{https://orcid.org/0009-0000-3864-3536}{0009-0000-3864-3536}.}}
\date{October 2026}
\begin{document}
\maketitle
\begin{abstract}
We construct one family of global unitaries and subsequent local product channels that depends only on local dimensions, copy number and requested target size, and simultaneously attains the state-aware extraction laws for every bipartite density matrix. Neither the spectrum nor the eigenbasis is known; no measurement or extra ancilla is supplied before the global unitary. A simultaneous Schur--Weyl packing retains entire unknown representation factors and known fractions of their maximally mixed multiplicities. It preserves the exact all-rate fidelity exponent, proves the optimal below-capacity reliability function in its strict direct regime, and attains the eventual-exact capacity. In the entropy-limited, positive-varentropy regime it also gives the same Gaussian threshold as state-aware completely PPT processing. The proof combines standard representation theory, deterministic local coding and scalar information-spectrum bounds. It does not solve ordinary fixed-input LOCC distillation: the global entangling preprocessing remains a resource. Earlier universal compression, concentration and distillation results are explicitly credited. Exact finite checks accompany the written proof; no Lean certification or external peer review is claimed.
\end{abstract}
'''
FOOTER=r'''
\section*{Verification scope and disclosures}
The mathematical argument uses standard Schur--Weyl representation theory and dimension/character formulas, the Rains effect constraints, and the ordinary central limit theorem. The finite checker independently compares hook dimensions with tableau recursion, Weyl dimensions with Schur characters, rank-deficient probabilities, noncommuting input matrices, coherent multiplicity selection, local code dyads, integer packing inequalities and exact algebra. Changed checker programs are required to fail for specific mathematical reasons. These checks do not certify the unbounded analytic theorem. The present work is not Lean-formalized and has not been externally peer reviewed.

This research was conducted independently and received no external funding. AI assistance was used in research exploration, proof development, ancillary programming, and manuscript preparation. The affiliation identifies the author's institution of study and does not imply institutional commissioning or endorsement.

The complete proof, source, and ancillary checks are available in the repository \url{https://github.com/mxym/math}, directory \texttt{research/universal-schur-extraction}. The preceding qutrit APPT purity theorem and its immutable Lean release are separate results and do not formally certify this paper. The entropy-deficit converse is also identified as a consequence of Lami's recent quadratic converse; no first-discovery or exhaustive priority claim is made for that bound.
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
