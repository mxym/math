#!/usr/bin/env python3
from pathlib import Path
import subprocess, tempfile, json, sys

ROOT=Path(__file__).resolve().parent

def run(cmd):
    p=subprocess.run(cmd,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    if p.returncode:
        sys.stderr.write(p.stdout+p.stderr)
        raise SystemExit(p.returncode)
    return p.stdout

with tempfile.TemporaryDirectory() as td:
    td=Path(td)
    for opt,tag in [([], 'normal'), (['-O'], 'optimized')]:
        run([sys.executable,*opt,'check_finite.py','mixed_finite_points.json','--quiet','--report',str(td/f'finite_{tag}.json')])
        run([sys.executable,*opt,'check_mixed_tail.py','mixed_tail_certificate.json','--report',str(td/f'tail_{tag}.json')])
        run([sys.executable,*opt,'check_large_200.py'])
    if (td/'finite_normal.json').read_bytes() != (td/'finite_optimized.json').read_bytes():
        raise SystemExit('finite normal/optimized reports differ')
    if (td/'tail_normal.json').read_bytes() != (td/'tail_optimized.json').read_bytes():
        raise SystemExit('tail normal/optimized reports differ')
    finite=json.loads((td/'finite_normal.json').read_text())
    tail=json.loads((td/'tail_normal.json').read_text())
print('PASS: ordinary and optimized exact replays are byte-identical.')
print('PASS: finite rectangles =', finite['rectangles'])
print('PASS: tail cells =', tail['cells'], 'maximum depth =', tail['maximum_depth'])
print('PASS: Gamma_C <= exp(1.048813) < 2.854262.')
