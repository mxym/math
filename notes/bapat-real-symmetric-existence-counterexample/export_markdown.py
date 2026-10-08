#!/usr/bin/env python3
"""Create a complete Markdown reading copy from the authoritative LaTeX source.
Requires pandoc and paper.aux from two successful LaTeX passes. No mathematics
is re-authored: cross-references are resolved and theorem wrappers flattened.
"""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
source = (ROOT / 'paper.tex').read_text()
aux = (ROOT / 'paper.aux').read_text()
labels = dict(re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}', aux))
source = re.sub(r'\\eqref\{([^}]+)\}', lambda m: '(' + labels[m[1]] + ')', source)
source = re.sub(r'\\ref\{([^}]+)\}', lambda m: labels[m[1]], source)
source = source.replace(r'\cite{Mitchell}', '[1]').replace(r'\cite{ComplexArchive}', '[2]')
source = re.sub(r'\\label\{([^}]+)\}',
                lambda m: r'\tag{' + labels[m[1]] + '}' if m[1].startswith('eq:') else '', source)
# Separate this two-line definition so every display has its own equation tag.
source = source.replace(r'\begin{align}', r'\begin{equation}').replace(r'\end{align}', r'\end{equation}')
source = source.replace(r'\tag{2}\\', r'\tag{2}\end{equation}' + '\n' + r'\begin{equation}')
source = source.replace(r'\ell_i(z)&=', r'\ell_i(z)=').replace(r'S_{ab}(z)&=', r'S_{ab}(z)=')
body = subprocess.run(['pandoc', '-f', 'latex', '-t', 'markdown+tex_math_dollars',
                       '--wrap=none'], input=source, text=True,
                      check=True, capture_output=True).stdout
# pandoc omits the abstract in non-standalone Markdown; convert it separately.
abstract_tex = re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}', source, re.S)[1]
abstract = subprocess.run(['pandoc', '-f', 'latex', '-t', 'markdown+tex_math_dollars',
                          '--wrap=none'], input=abstract_tex, text=True,
                         check=True, capture_output=True).stdout.strip()
# The main conversion knows the source macros; the separate abstract does not.
abstract = abstract.replace(r'\Z', r'\mathbb Z')
body = re.sub(r'^:::.*\n', '', body, flags=re.M)
body = re.sub(r'\{#[^\n]*\.unnumbered\}', '', body)
# The final raw bibliography is retained by pandoc but gets a numeric heading.
body = body.replace('\n9\n\nL. Mitchell,', '\n## References\n\n1. L. Mitchell,')
body = body.replace('\n*Bapat $q$-permanent counterexample*,', '\n2. *Bapat $q$-permanent counterexample*,')
count = 0
lines = []
for line in body.splitlines():
    if line.startswith('# ') and 'Verification and limitations' not in line:
        count += 1
        line = '## ' + str(count) + ' ' + line[2:]
    elif line.startswith('# Verification and limitations'):
        line = '## Verification and limitations'
    lines.append(line)
body = '\n'.join(lines).strip()
# Put display delimiters on their own lines for common Markdown renderers.
chunks = body.split('$$')
assert len(chunks) % 2 == 1
body = ''.join(part if i % 2 == 0 else '\n\n$$\n' + part.strip() + '\n$$\n\n'
               for i, part in enumerate(chunks))
body = re.sub(r'(?m)^ +(?=\S)', '', body)
body = re.sub(r'(?m)^[ \t]+$', '', body)
body = re.sub(r'\n{3,}', '\n\n', body)
text = ("# Real symmetric counterexamples to Bapat's $q$-permanent conjecture\n\n"
        "Research note | October 8, 2026\n\n"
        "This is the full reading copy of paper.tex. Equation numbers agree with paper.pdf.\n\n"
        "## Abstract\n\n" + abstract + '\n\n' + body + '\n')
assert 'reference-type=' not in text and '[@' not in text and '\\label{' not in text
assert '## 7 Rational' in text and '## References' in text
(ROOT / 'proof.md').write_text(text)
print('Wrote proof.md with resolved references and complete source text.')
