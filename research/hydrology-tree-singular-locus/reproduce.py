#!/usr/bin/env python3
"""Source-isolated exact diagnostics; not a proof assistant for the manuscript."""
from __future__ import annotations
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
INPUTS = ['THEOREMS.md','README.md','LITERATURE.md','PROOF_DEPENDENCIES.md',
          'exact.py','independent.py','reproduce.py','requirements.txt']


def require(ok: bool, message: str) -> None:
    if not ok:
        raise RuntimeError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot() -> dict[str, str]:
    return {name:digest(ROOT/name) for name in INPUTS}


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,required=True)
    args=parser.parse_args()
    out=args.output_dir.resolve()
    out.mkdir(parents=True,exist_ok=False)
    report={'status':'RUNNING','scope':'Finite exact and symbolic diagnostics; arbitrary-tree proof is written mathematics, not Lean',
            'started_utc':dt.datetime.now(dt.timezone.utc).isoformat(),'commands':[]}
    try:
        before=snapshot()
        report['source_sha256']=before
        report['python_version']=platform.python_version()
        import sympy, mpmath
        report['sympy_version']=sympy.__version__
        report['mpmath_version']=mpmath.__version__
        require(sympy.__version__=='1.14.0','Unexpected SymPy version')
        require(mpmath.__version__=='1.3.0','Unexpected mpmath version')
        source=out/'fresh-source';source.mkdir()
        for name in INPUTS:
            shutil.copyfile(ROOT/name,source/name)
        require({name:digest(source/name) for name in INPUTS}==before,'Copy hash mismatch')
        env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env.pop('PYTHONPATH',None)
        for script in ['exact','independent']:
            for optimized in [False,True]:
                label=script+('-optimized' if optimized else '-normal')
                command=[sys.executable,'-B']+(['-O'] if optimized else [])+[str(source/(script+'.py')),'--output',str(out/(label+'.json'))]
                start=time.monotonic()
                with (out/(label+'.log')).open('w') as stream:
                    p=subprocess.run(command,cwd=source,env=env,stdout=stream,stderr=subprocess.STDOUT,timeout=240)
                report['commands'].append({'command':[Path(x).name if x.startswith(str(out)) else x for x in command],
                    'returncode':p.returncode,'elapsed_seconds':round(time.monotonic()-start,3),'log':label+'.log'})
                require(p.returncode==0,'Failed checker: '+label)
                require(json.loads((out/(label+'.json')).read_text())['status']=='PASS','Missing pass status: '+label)
                print(label+': PASS',flush=True)
            require((out/(script+'-normal.json')).read_bytes()==(out/(script+'-optimized.json')).read_bytes(),
                    'Normal/optimized mismatch: '+script)
        exact=json.loads((out/'exact-normal.json').read_text())
        independent=json.loads((out/'independent-normal.json').read_text())
        require(exact['matrix_jacobian_cases']==7230,'Incorrect exhaustive fixture count')
        require(exact['singular_cases']==3221,'Incorrect singular fixture count')
        require(len(exact['rejected_controls'])==4,'Missing formula mutation control')
        require(independent['symbolic_identities']==11,'Incorrect symbolic identity count')
        require(independent['positive_spectral_collision']['false_claim_all_positive_distinct_rates_implies_nonsingular']=='REJECTED','Missing distinct-rate false-claim control')
        require(snapshot()==before,'Source modified during verification')
        require({name:digest(source/name) for name in INPUTS}==before,'Fresh source changed during verification')
        report.update(status='PASS',source_hashes_unchanged=True,normal_optimized_identical=True,
                      matrix_jacobian_cases=7230,singular_cases=3221,symbolic_identities=11,
                      formula_mutations_rejected=4,false_interior_claim_rejected=True,
                      case_digest_sha256=exact['case_digest_sha256'])
    except Exception as exc:
        report.update(status='FAIL',error=f'{type(exc).__name__}: {exc}')
    report['finished_utc']=dt.datetime.now(dt.timezone.utc).isoformat()
    report['log_sha256']={p.name:digest(p) for p in sorted(out.glob('*.log'))}
    (out/'verification.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2,sort_keys=True))
    return 0 if report['status']=='PASS' else 1


if __name__=='__main__':
    raise SystemExit(main())
