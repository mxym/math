#!/usr/bin/env python3
"""Assemble the complete v2 LaTeX source from frozen v1 core and new extension.
No downloads, dependencies, or external commands. Compile main.tex afterward.
"""
from pathlib import Path
import hashlib

root = Path(__file__).resolve().parent
core = (root/'core.tex').read_bytes()
blob = hashlib.sha1(b'blob '+str(len(core)).encode()+b'\0'+core).hexdigest()
if blob != '2d6f87539f93f87b33e2484334542ab924143057':
    raise RuntimeError('Frozen v1 source does not match its published Git blob')
s = core.decode('utf-8')

def replace_once(old: str, new: str) -> None:
    global s
    if s.count(old) != 1:
        raise RuntimeError('Assembly anchor is missing or ambiguous: '+old[:70])
    s = s.replace(old, new, 1)

replace_once(r'\begin{document}\maketitle', r'\newcommand{\E}{\mathbb E}'+'\n'+r'\begin{document}\maketitle')
replace_once('October 7, 2026\\quad Version 1', 'October 7, 2026\\quad Version 2')
replace_once('We do not claim that the finite-moment exponent is optimal for transport maps themselves.', 'A separate two-atom construction proves the general finite-moment transport exponent sharp for one fixed smooth, full-support, strongly log-concave source. In contrast, superquadratic product sources retain a sharp one-third exponent. Thus full support and smoothness alone do not replace quantitative translation regularity.')
replace_once('No priority or journal-tier certification is asserted.', r'''A parallel update, manuscript 001 v3, was found during release reconciliation. It already contains the general log-concave target-tail bound, sharp truncated-source examples, and Gaussian and bounded-Hessian one-third estimates. Those overlapping transport bounds are not claimed as a distinct new result here. The present additional statements are the BV-density interpolation theorem, superquadratic-source translation estimates, and the fixed smooth full-support counterexample in Section~\ref{sec:steep}. No priority or journal-tier certification is asserted.''')
replace_once('We claim sharpness only for the interpolation theorem.', r'''The ramp proves sharpness only for interpolation. The different two-atom construction in Section~\ref{sec:steep} establishes transport sharpness for a fixed smooth source.''')
anchor = r'\section{Scope of verification and of the claimed advance}'
replace_once(anchor, (root/'extension.tex').read_text(encoding='utf-8')+'\n'+anchor)
old = 'The finite-moment \\emph{transport} exponent is an established upper estimate in this draft, not an optimality theorem.'
replace_once(old, r'The finite-moment \emph{transport} exponent is sharp for the fixed smooth source of Theorem~\ref{thm:steep}, not for every source; the product sources in Corollary~\ref{cor:product} have the better sharp exponent $1/3$.')
replace_once(r'\bibitem{O374}', r'''\bibitem{M001v3} mxym, \emph{Sharp Brenier stability under target moment bounds}, v3, October 7, 2026, manuscript 001. Pinned commit \texttt{5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3}; source blob \texttt{0007edf5e28e4b4b0d34b2043cffd6e13e9f5aed}. This parallel version precedes the full source publication of the present v1 and contains the overlapping tail and Gaussian results acknowledged above.
\bibitem{O374}''')
(root/'main.tex').write_text(s, encoding='utf-8')
print('Assembled complete v2 main.tex from the pinned v1 core and extension.tex')
