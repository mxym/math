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
\usepackage{longtable,booktabs,array}
\setlength{\emergencystretch}{2em}
\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}
\setcounter{secnumdepth}{0}
\title{The collective-unitary logarithmic-negativity rate\\of every bipartite spectrum}
\author{Yongxian Zhang\thanks{School of Computer Science and Engineering, South China University of Technology, Guangzhou, China. Email: \href{mailto:mxymmxym1@gmail.com}{mxymmxym1@gmail.com}. ORCID: \href{https://orcid.org/0009-0000-3864-3536}{0009-0000-3864-3536}.}}
\date{October 2026}
\begin{document}
\maketitle
\begin{abstract}
We determine the asymptotic maximum logarithmic negativity obtainable from tensor powers of an arbitrary bipartite density matrix by global unitaries on the original space. For fixed local dimensions $2\le m\le n$ and spectrum $p$, the per-copy rate is the minimum over $1\le\alpha\le2$ of
$[\log m+(\alpha-1)\log n+\log\sum_i p_i^\alpha]/\alpha$.
The result includes zero eigenvalues and unequal local dimensions. In the balanced case it reduces to one half of the logarithm of dimension times purity. We prove a one-shot spectral-prefix approximation using random Bell-basis projections and the matrix Bernstein inequality, then match a family of Schatten-norm upper bounds by spectral types and escort distributions. A fixed blockwise Bell output basis suffices at the exponential scale, with only the assignment of eigenvalues varying. An exact unequal-dimension example requires a strictly interior R\'enyi parameter. The rate is positive for every state except the maximally mixed state. This is a statement about logarithmic negativity under unrestricted collective global unitaries, not a claim about local distillation or efficient circuit implementation. Exact ancillary checks accompany the analytic proof; no Lean certification is asserted.
\end{abstract}
'''
FOOTER=r'''
\section*{Verification scope and disclosures}
The mathematical argument uses the stated external matrix Bernstein theorem, together with finite-dimensional matrix analysis. The ancillary program independently checks small cyclotomic Bell-projector identities, exact rational constants, type cardinalities, and algebraic identities; it also rejects deliberately corrupted inputs and source programs. These checks do not by themselves certify the unbounded analytic theorem. The present work is not Lean-formalized and has not been externally peer reviewed.

This research was conducted independently and received no external funding. AI assistance was used in research exploration, proof development, ancillary programming, and manuscript preparation. The affiliation identifies the author's institution of study and does not imply institutional commissioning or endorsement.

The complete proof, source, and ancillary checks are available in the repository \url{https://github.com/mxym/math}, directory \texttt{research/collective-unitary-negativity-rate}. The preceding qutrit APPT purity theorem and its immutable Lean release are separate results and do not formally certify this paper.
\end{document}
'''

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--tex-only',action='store_true')
    args=ap.parse_args()
    source=(ROOT/'PROOF.md').read_text()
    body=source[source.index('## 1.'):]
    result=subprocess.run(['pandoc','--from','markdown+tex_math_dollars+tex_math_single_backslash','--to','latex','--wrap=none'],input=body,text=True,capture_output=True,check=True,timeout=60)
    tex=HEADER+'\n'+result.stdout+'\n'+FOOTER
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
