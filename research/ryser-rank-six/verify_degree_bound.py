"""Verify publication hashes and reproduce the exact degree-bound checks."""
from argparse import ArgumentParser
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parent


def require(condition,message):
    if not condition:
        raise RuntimeError(message)


def main():
    p=ArgumentParser()
    p.add_argument('--lean',action='store_true')
    a=p.parse_args()
    m=json.loads((ROOT/'DEGREE_MANIFEST.json').read_text())
    for name,digest in m['files'].items():
        require(sha256((ROOT/name).read_bytes()).hexdigest()==digest,f'hash mismatch: {name}')
    lines=''.join(f'{digest}  {name}\n' for name,digest in m['files'].items())
    require((ROOT/'DEGREE_SHA256SUMS').read_text()==lines,'checksum list mismatch')
    print(f"Degree-bound inventory: {len(m['files'])} payload files PASS",flush=True)
    for flags in ([],['-O']):
        for checker in ('check_degree_bound.py','check_root_flower.py'):
            subprocess.run([sys.executable,'-B',*flags,str(ROOT/checker)],cwd=ROOT,check=True)
    if a.lean:
        result=subprocess.run(['lake','env','lean','DegreeCertificate.lean'],cwd=ROOT/'formal',
                              check=True,text=True,capture_output=True)
        require('sorryAx' not in result.stdout+result.stderr,'unproved Lean placeholder')
        require(result.stdout==(ROOT/'results/degree-lean-axioms.txt').read_text(),'Lean export drift')
        require(result.stderr=='','unexpected Lean diagnostics')
        print('Three scalar Lean certificates and exact recorded axioms PASS',flush=True)


if __name__=='__main__':main()
