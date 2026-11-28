#!/usr/bin/env python3
"""Run the exact labeled-measure verifier against the 131-point proof data."""
import hashlib,json,runpy
from pathlib import Path
def main():
    root=Path(__file__).resolve().parent
    prev=root/'verify-kissing-component-measure.py'
    if hashlib.sha256(prev.read_bytes()).hexdigest()!='b24478aa381465e7708feba99fa13ebc0ba99b0f2aa8379aa4e0a4ef2e2db718':
        raise RuntimeError('different prerequisite harmonic verifier')
    data=json.loads((root/'kissing-131-component-data.json').read_text())
    if len(data['targets'])!=1 or data['targets'][0][:2]!=[131,62]:
        raise ValueError('different target')
    lib=runpy.run_path(str(prev))
    lib['verify'](data)
    full=lib['residual'](data['weights'],132,63)
    candidates={p for p in full if len(p)==8 and sum(p)==132 and min(p)>=5}
    if len(candidates)!=1159:raise ArithmeticError('different eight-component count')
    print('PASS 132-point structural count:',len(candidates),'candidate size multisets')
if __name__=='__main__':main()
