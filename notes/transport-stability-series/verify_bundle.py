#!/usr/bin/env python3
"""Lightweight source/tag/build integrity check; this is not a proof checker."""
from pathlib import Path
import hashlib, json, re, subprocess, sys

ROOT = Path(__file__).resolve().parent
mapping = json.loads((ROOT / 'SOURCE_MAP.json').read_text())
results = []
for paper in mapping['papers']:
    src = ROOT / paper['included_source']
    actual = hashlib.sha256(src.read_bytes()).hexdigest()
    if actual != paper['sha256']:
        raise SystemExit(f"Source hash mismatch: {src.name}")
    body = (ROOT / paper['body_tex']).read_text()
    tags = re.findall(r'\\tag\{([^}]+)\}', body)
    expected = paper['source_equation_tags']
    if len(tags) != len(set(tags)) or set(tags) != set(expected):
        raise SystemExit(f"Equation tag discrepancy: {paper['paper']}")
    if len(re.findall(r'\\section\{', body)) != len(paper['sections']):
        raise SystemExit(f"Section count discrepancy: {paper['paper']}")
    if re.search(r'await a limited recheck|remain subject to the limited recheck|pending the user', body):
        raise SystemExit(f"Stale status in current typeset body: {paper['paper']}")
    pdf = ROOT / paper['pdf']
    if not pdf.is_file() or not pdf.read_bytes().startswith(b'%PDF-'):
        raise SystemExit(f"Missing PDF: {pdf}")
    text = subprocess.check_output(['pdftotext', '-layout', str(pdf), '-'], text=True)
    compact = re.sub(r'\s+', '', text)
    for tag in tags:
        if '(' + tag + ')' not in compact:
            raise SystemExit(f"Missing rendered equation tag {tag}: {paper['paper']}")
    if '\ufffd' in text or '??' in text:
        raise SystemExit(f"Suspicious unresolved PDF text: {paper['paper']}")
    info = subprocess.check_output(['pdfinfo', str(pdf)], text=True)
    pages = int(re.search(r'^Pages:\s+(\d+)', info, re.M).group(1))
    log = ROOT / paper['paper'] / 'build/main.log'
    checked_log = False
    if log.exists():
        bad = re.findall(r'^.*(?:Overfull \\[hv]box|Missing character:|undefined references|undefined on input line).*$|^!.*$', log.read_text(errors='replace'), re.M)
        if bad:
            raise SystemExit('\n'.join(bad))
        checked_log = True
    results.append({'paper': paper['paper'], 'source_sha256': actual,
                    'sections': len(paper['sections']), 'equation_tags': len(tags),
                    'pdf_pages': pages, 'pdf_sha256': hashlib.sha256(pdf.read_bytes()).hexdigest(),
                    'pdf_text_sha256': hashlib.sha256(text.encode()).hexdigest(),
                    'available_build_log_checked': checked_log})
print(json.dumps({'status': 'PASS', 'scope': 'Source identity, section/tag coverage, rendered tag presence, and available build diagnostics only; not mathematical verification.', 'papers': results}, indent=2))
