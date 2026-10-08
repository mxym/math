#!/usr/bin/env python3
"""Rebuild all three papers in fresh directories using installed TeX only."""
from pathlib import Path
import hashlib, json, re, shutil, subprocess, tempfile

root = Path(__file__).resolve().parent
papers = ['top-n', 'binary-mass', 'general-moment']
with tempfile.TemporaryDirectory(prefix='transport-series-replay-') as temporary:
    replay = Path(temporary)
    for name in ['build.sh', 'preamble.tex']:
        shutil.copy2(root / name, replay / name)
    for paper in papers:
        (replay / paper).mkdir()
        for tex in (root / paper).glob('*.tex'):
            shutil.copy2(tex, replay / paper / tex.name)
    subprocess.run(['bash', str(replay / 'build.sh')], check=True)
    results = []
    for paper in papers:
        a, b = root / paper / 'main.pdf', replay / paper / 'main.pdf'
        ta = subprocess.check_output(['pdftotext', '-layout', str(a), '-'])
        tb = subprocess.check_output(['pdftotext', '-layout', str(b), '-'])
        pages = lambda p: int(re.search(rb'^Pages:\s+(\d+)', subprocess.check_output(['pdfinfo', str(p)]), re.M).group(1))
        results.append({'paper': paper,
                        'pdf_byte_identical': a.read_bytes() == b.read_bytes(),
                        'text_and_page_breaks_identical': ta == tb,
                        'pages_identical': pages(a) == pages(b),
                        'replay_sha256': hashlib.sha256(b.read_bytes()).hexdigest()})
    print(json.dumps(results, indent=2))
    if not all(r['pdf_byte_identical'] and r['text_and_page_breaks_identical'] and r['pages_identical'] for r in results):
        raise SystemExit('Replay differs; check whether TeX/font/toolchain versions match BUILD_INFO.md.')
