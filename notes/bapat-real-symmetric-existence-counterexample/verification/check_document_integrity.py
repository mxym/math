#!/usr/bin/env python3
"""Structural manuscript QA; visual page inspection remains a separate check."""
import sys

# Fail closed: these verifiers require assertions to remain enabled.
if not __debug__:
    sys.stderr.write("ERROR: assertions are disabled. Run without -O/-OO and without PYTHONOPTIMIZE.\n")
    raise SystemExit(2)

from pathlib import Path
import re
import subprocess
import xml.etree.ElementTree as ET

root = Path(__file__).resolve().parent.parent
text = (root / 'qa/paper.txt').read_text()
pages = text.split('\f')
if not pages[-1].strip():
    pages.pop()
assert len(pages) == 9, len(pages)
for i, page in enumerate(pages, 1):
    assert len(page.strip()) > 100, (i, 'empty or truncated page')
    assert re.search(r'(?m)^\s*' + str(i) + r'\s*$', page), (i, 'footer missing')
assert '\ufffd' not in text, 'Replacement glyph in extracted text'
assert '??' not in text, 'Unresolved cross-reference in extracted text'
assert 'integer assertion' in text and 'References' in pages[-1]
tex = (root / 'paper.tex').read_text()
aux = (root / 'paper.aux').read_text()
labels = dict(re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}', aux))
refs = re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', tex)
assert all(label in labels for label in refs)
assert sorted(int(v) for k, v in labels.items() if k.startswith('eq:')) == list(range(1, 27))
md = (root / 'proof.md').read_text()
assert sorted(map(int, re.findall(r'\\tag\{(\d+)\}', md))) == list(range(1, 27))
assert 'reference-type=' not in md and '[@' not in md and '\\label{' not in md
log = (root / 'build-pass2.log').read_text()
assert not re.search(r'Overfull|Underfull|undefined references|undefined citations|^!', log, re.M)
subprocess.run(['pdftotext', '-bbox', str(root / 'paper.pdf'), str(root / 'qa/bbox.html')], check=True)
# Poppler maps some large math delimiters to XML-forbidden control bytes.
# Strip only those text characters; bounding-box attributes are untouched.
bbox_text = (root / 'qa/bbox.html').read_text()
bbox_text = ''.join(c for c in bbox_text if ord(c) >= 32 or c in '\t\n\r')
tree = ET.ElementTree(ET.fromstring(bbox_text))
ns = {'h': 'http://www.w3.org/1999/xhtml'}
page_nodes = tree.findall('.//h:page', ns)
assert len(page_nodes) == 9
for i, page in enumerate(page_nodes, 1):
    width, height = float(page.attrib['width']), float(page.attrib['height'])
    for word in page.findall('h:word', ns):
        a = word.attrib
        assert 0 <= float(a['xMin']) <= float(a['xMax']) <= width, (i, word.text)
        assert 0 <= float(a['yMin']) <= float(a['yMax']) <= height, (i, word.text)
print('PASS: 9 extracted nonempty pages; sequential page footers 1..9.')
print('PASS: all 26 numbered equations and source cross-references resolved.')
print('PASS: complete Markdown reading copy has matching equation tags 1..26.')
print('PASS: no replacement glyphs or unresolved markers in PDF text extraction.')
print('PASS: no overfull/underfull boxes or unresolved references in second LaTeX pass.')
print('PASS: all extracted word bounding boxes lie inside their PDF pages.')
print('Visual inspection is recorded separately in qa/QA_REPORT.md.')
