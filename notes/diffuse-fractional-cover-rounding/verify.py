"""Replay the frozen diagnostics and optional partial Lean exports."""
from argparse import ArgumentParser
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parent


def require(ok,message):
    if not ok:
        raise RuntimeError(message)


def main():
    parser=ArgumentParser()
    parser.add_argument('--lean',action='store_true')
    args=parser.parse_args()
    manifest=json.loads((ROOT/'MANIFEST.json').read_text())
    for name,digest in manifest['files'].items():
        require(sha256((ROOT/name).read_bytes()).hexdigest()==digest,f'hash mismatch: {name}')
    lines=''.join(f'{digest}  {name}\n' for name,digest in manifest['files'].items())
    require((ROOT/'SHA256SUMS').read_text()==lines,'checksum inventory differs')
    for record in json.loads((ROOT/'source-lineage.json').read_text())['repository_inputs']:
        path=ROOT.parent.parent/record['path']
        require(sha256(path.read_bytes()).hexdigest()==record['sha256'],f"predecessor changed: {record['path']}")
    print(f"Frozen inventory: {len(manifest['files'])} files and predecessor source inputs PASS",flush=True)
    expected=(ROOT/'results/exact.txt').read_text()
    for flags in ([],['-O']):
        result=subprocess.run([sys.executable,*flags,str(ROOT/'check_exact.py')],cwd=ROOT,
                              text=True,capture_output=True,check=True)
        require(result.stderr=='' and result.stdout==expected,'exact replay mismatch')
    print(expected,end='',flush=True)
    print('Normal and optimized exact replay agree PASS',flush=True)
    if args.lean:
        source=(ROOT/'formal/Diffuse.lean').read_text()
        require('sorry' not in source and 'native_decide' not in source,'unproved proof escape')
        result=subprocess.run(['lake','env','lean','Diffuse.lean'],cwd=ROOT/'formal',
                              text=True,capture_output=True,check=True)
        require(result.stderr=='' and result.stdout==(ROOT/'results/lean-axioms.txt').read_text(),
                'Lean replay mismatch')
        require('sorryAx' not in result.stdout,'unproved export')
        print('Six finite Lean exports and standard axiom lists PASS',flush=True)


if __name__=='__main__':
    main()
