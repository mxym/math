#!/usr/bin/env python3
"""Deterministically assemble complete papers from the pinned research proofs.

No trusted checksum is refreshed by this script. The sharp-simplex paper is
edited directly; its truncation appendix is a verbatim proof extraction.
"""
from hashlib import sha256
import json
import os
from pathlib import Path
import re
from historical import HistoricalInputs

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
HISTORICAL = HistoricalInputs()


def read(path):
    if path in HISTORICAL.pins['files']:
        return HISTORICAL.read_bytes(path).decode()
    return (ROOT/path).read_text()


def relocate_links(text, source, destination):
    def replace(match):
        label, target = match.groups()
        if target.startswith(('http:', 'https:', '#', 'mailto:')):
            return match.group(0)
        path, sep, fragment = target.partition('#')
        resolved = (ROOT/source).parent/path
        relative = os.path.relpath(resolved, (ROOT/destination).parent)
        return '['+label+']('+relative+(sep+fragment if sep else '')+')'
    return re.sub(r'\[([^\]]+)\]\(([^)]+)\)', replace, text)


def scoped(text, prefix):
    # Scope prose references without altering mathematical expressions such
    # as psi(0), and scope explicit equation tags inside display mathematics.
    tags=set(re.findall(r'\\tag\{([^}]+)\}',text))
    parts = re.split(r'(\\\([\s\S]*?\\\)|\\\[[\s\S]*?\\\])', text)
    for i, part in enumerate(parts):
        if i % 2:
            parts[i] = re.sub(r'\\tag\{([^}]+)\}',
                             lambda m: r'\tag{'+prefix+'.'+m[1]+'}', part)
        else:
            part = re.sub(r'\b(Theorem|Lemma|Corollary|Proposition|Section|Sections) (\d+[A-Za-z]?)',
                          lambda m:m[1]+' '+prefix+'.'+m[2], part)
            part = re.sub(r'(?m)^(#{2,4}) (\d+(?:\.\d+)*)\.',
                          lambda m:m[1]+' '+prefix+'.'+m[2]+'.', part)
            part = re.sub(r'(?<![A-Za-z0-9])\((\d+[A-Za-z]?)\)',
                          lambda m:'('+prefix+'.'+m[1]+')' if m[1] in tags else m[0], part)
            part = part.replace('Appendix A', 'Appendix '+prefix+'.A')
            parts[i] = part
    return ''.join(parts)


def main():
    HISTORICAL.verify_all()
    out = HERE/'fractional-cover-spectrum/paper.md'
    sections = []
    for prefix, title, source in [
        ('F','The intersecting frontier','notes/sharp-fractional-cover-frontier/paper.md'),
        ('D','Design-boundary stability','notes/fractional-design-stability/paper.md'),
        ('S','The complete matching spectrum','notes/fractional-matching-spectrum/paper.md')]:
        text = read(source)
        text = text[text.index('## 1.'):]
        text = scoped(text, prefix)
        text = relocate_links(text, source, out.relative_to(ROOT))
        sections.append('## Part '+prefix+': '+title+'\n\n'+text)
    out.write_text(read('manuscripts/fractional-cover-spectrum/introduction.md')+'\n\n'+'\n\n'.join(sections))
    source = 'notes/complex-permanent-determinant/PAPER.md'
    destination = 'manuscripts/complex-permanent-pencil/paper.md'
    text = read(source)
    text = text[text.index('## 1.'):]
    text = relocate_links(text, source, destination)
    source4='notes/four-row-permanent-tradeoff/PAPER.md'
    four=read(source4)
    four=four[four.index('## 1.'):]
    four=scoped(four,'Q')
    four=relocate_links(four,source4,destination)
    four=re.sub(r'(?m)^(~~~[A-Za-z0-9_-]*)\s*$',lambda m:'\n'+m[1]+'\n',four)
    text+='\n\n## Part Q: Four-row determinant tradeoffs and parity tensor norms\n\n'+four
    (ROOT/destination).write_text(read('manuscripts/complex-permanent-pencil/introduction.md')+'\n\n'+text)
    source = 'notes/sharp-robust-permanent/paper.md'
    destination = 'manuscripts/orbital-atom-stability/paper.md'
    text = read(source)
    text = text[text.index('## 15.'):]
    text = relocate_links(text, source, destination)
    text = text.replace('The fixed-point argument in Section 8 extends beyond the symmetric groups.',
                        'The fixed-point method applies beyond the symmetric groups.')
    text = text.replace('proved in Section 8. Here', 'obtained from Theorem 15. Here')
    text=text.replace('Because the action on ordered triples has exactly the four orbitals',
                      'Because the action on ordered pairs of three-element subsets has exactly the four orbitals')
    johnson='notes/johnson-short-cycle-spectrum/README.md'
    extra=read(johnson)
    extra=extra[extra.index('## 1.'):]
    extra=scoped(extra,'J')
    extra=re.sub(r'\b(Theorem|Lemma) ([A-E])\b',lambda m:m[1]+' J.'+m[2],extra)
    extra=relocate_links(extra,johnson,destination)
    text+='\n\n## Part J: All-rank transfer, hierarchy and four-subset certificates\n\n'+extra
    cert=json.loads(read('notes/johnson-short-cycle-spectrum/certificates/k4_n26_50.json'))
    extension=read('manuscripts/orbital-atom-stability/four-subset-extension.md')
    rows=['| Degree | Exact coefficient |','| ---: | ---: |']
    for record in cert['records']:
        rows.append('| '+str(record['n'])+' | '+record['C']+' |')
    text+='\n\n'+extension+'\n\n'+'\n'.join(rows)+'\n'
    text+='\n\n'+read('manuscripts/orbital-atom-stability/cramer-appendix.md')
    text=re.sub(r'\\\(\\texttt\{([^}]+)\}\\\)',
                lambda m:r'\nolinkurl{'+m[1].replace(r'\_','_')+'}',text)
    text = text.replace(r'\ge0, \tag{83}'+'\n'+r'\end{aligned}',
                        r'\ge0,'+'\n'+r'\end{aligned}\tag{83}')
    def outside_tag(match):
        body=match[1]
        tags=re.findall(r'\\tag\{[^}]+\}',body)
        if len(tags)>1:
            raise RuntimeError('Multiple tags in one aligned environment')
        body=re.sub(r'\\tag\{[^}]+\}','',body)
        body=re.sub(r'\n[ \t]*\n','\n',body)
        return r'\begin{aligned}'+body+r'\end{aligned}'+''.join(tags)
    text=re.sub(r'\\begin\{aligned\}([\s\S]*?)\\end\{aligned\}',outside_tag,text)
    text = text.replace(r'L_o(g)=\frac{n^2-6n+11}{2}\,A(g)-(2n-7)\,F(g),\quad'+'\n'+
                        r'D_o=\frac{(n-3)(n-2)(n+3)(n+4)}8,'+'\n'+
                        r'\quad h_o(g)=\mathbf1_{\{g=\mathrm{id}\}}+\frac{L_o(g)}{D_o}. \tag{81}',
                        r'\begin{gathered}'+ '\n'+
                        r'L_o(g)=\frac{n^2-6n+11}{2}\,A(g)-(2n-7)\,F(g),\\'+'\n'+
                        r'D_o=\frac{(n-3)(n-2)(n+3)(n+4)}8,\qquad'+'\n'+
                        r'h_o(g)=\mathbf1_{\{g=\mathrm{id}\}}+\frac{L_o(g)}{D_o}.'+'\n'+
                        r'\end{gathered}\tag{81}')
    # Keep the full local numbering of the five connected theorem sections.
    # There is no dependence on the earlier permanent inequalities.
    (ROOT/destination).write_text(read('manuscripts/orbital-atom-stability/introduction.md')+'\n\n'+text)
    source = 'notes/continuum-power-avoidance-unified/source/continuum-avoidance.tex'
    text = read(source)
    text = text.replace(r'\author{}', r'\author{mxym/math research project\\AI-assisted research manuscript}')
    start = text.index('The delivered normal and optimized harness reports')
    end = text.index('The fixed environment is Lean', start)
    text = text[:start]+read('manuscripts/continuum-power-avoidance/formal-evidence.tex')+'\n\n'+text[end:]
    text = text.replace('archives in the supplement.',
                        'projects in the public repository: '+
                        r'\nolinkurl{formalizations/geometric-avoidance} and '+
                        r'\nolinkurl{formalizations/continuum-remainder-avoidance}.')
    text = text.replace(r'\usepackage[hidelinks]{hyperref}',
                        r'\usepackage[hidelinks]{hyperref}'+'\n'+r'\emergencystretch=3em')
    text = text.replace(r'\newcommand{\code}[1]{\texttt{\small\detokenize{#1}}}',
                        r'\newcommand{\code}[1]{{\small\nolinkurl{#1}}}')
    (HERE/'continuum-power-avoidance/paper.tex').write_text(text)
    (HERE/'continuum-power-avoidance/correspondence.tex').write_text(read('notes/continuum-power-avoidance-unified/source/correspondence.tex'))
    source = read('notes/simplex-truncation-stability/proof.tex')
    start = source.index(r'\section{The obstruction family')
    end = source.index('Combining the released upper estimate')
    fragment = source[start:end].replace(r'\section{The obstruction family and its complete calculation}',
                                         r'\section{The truncation obstruction: complete calculation}')
    (HERE/'sharp-simplex-stability/truncation.tex').write_text(fragment.rstrip()+'\n')
    print('Assembled five complete manuscript sources from fixed historical proofs.')


if __name__ == '__main__':
    main()
