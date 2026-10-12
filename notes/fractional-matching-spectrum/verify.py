"""Replay frozen spectral diagnostics and optional partial anchor Lean."""
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
    lineage=json.loads((ROOT/'source-lineage.json').read_text())
    for name,data in lineage['copies'].items():
        require(sha256((ROOT/name).read_bytes()).hexdigest()==data['sha256'],f'copied source changed: {name}')
    print(f"Frozen inventory: {len(manifest['files'])} files and two source copies PASS",flush=True)
    expected=(ROOT/'results/exact.txt').read_text()
    for flags in ([],['-O']):
        result=subprocess.run([sys.executable,*flags,str(ROOT/'check_exact.py')],
                              cwd=ROOT,text=True,capture_output=True,check=True)
        require(result.stderr=='' and result.stdout==expected,'exact replay mismatch')
    print(expected,end='',flush=True)
    print('Normal and optimized exact replay agree PASS',flush=True)
    if args.lean:
        for name in ('FrontierCertificate.lean','Spectrum.lean'):
            source=(ROOT/'formal'/name).read_text()
            require('sorry' not in source and 'native_decide' not in source,'unproved proof escape')
        subprocess.run(['lake','build','FrontierCertificate'],cwd=ROOT/'formal',
                       text=True,capture_output=True,check=True)
        for name,record in (('FrontierCertificate.lean','base-lean-axioms.txt'),('Spectrum.lean','lean-axioms.txt')):
            result=subprocess.run(['lake','env','lean',name],cwd=ROOT/'formal',
                                  text=True,capture_output=True,check=True)
            require(result.stderr=='' and result.stdout==(ROOT/'results'/record).read_text(),'Lean replay mismatch')
            require('sorryAx' not in result.stdout,'unproved export')
        print('Nine reused and three additional finite anchor Lean exports and axioms PASS',flush=True)


if __name__=='__main__':
    main()
