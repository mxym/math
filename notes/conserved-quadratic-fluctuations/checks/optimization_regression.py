#!/usr/bin/env python3
"""Exercise successful checks and rejected corruption under normal and -O Python."""
from __future__ import annotations
import argparse,ast,json,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--source-root',type=Path);parser.add_argument('--output',type=Path,default=ROOT/'checks/optimization-regression.json');args=parser.parse_args();cases=[]
    for name in ['strict_check.py','verify_package.py']:
        if any(isinstance(n,ast.Assert) for n in ast.walk(ast.parse((ROOT/'checks'/name).read_text()))): raise RuntimeError('Optimization-sensitive assert: '+name)
    def run(name,package,checker,extra,expected):
        for optimized in [False,True]:
            cmd=[sys.executable]+(['-O'] if optimized else [])+[str(package/'checks'/checker)]+extra;p=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
            if (p.returncode==0)!=expected: raise RuntimeError(name+' unexpected result:\n'+p.stdout+p.stderr)
            cases.append({'case':name,'optimized':optimized,'exit_code':p.returncode,'expected_success':expected,'expectation_met':True})
    extra=['--source-root',str(args.source_root)] if args.source_root else []
    run('real symbolic, audit, manuscript and 32-source checks',ROOT,'strict_check.py',extra,True)
    run('explicit failure guard',ROOT,'strict_check.py',['--self-test-failure'],False)
    with tempfile.TemporaryDirectory(prefix='quadratic-negative-') as directory:
        package=Path(directory)/'package';shutil.copytree(ROOT,package,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        def corrupt(path,name):
            p=package/path;original=p.read_bytes();p.write_bytes(original+b'\nDeliberate negative-control corruption.\n');run(name,package,'strict_check.py',[],False);p.write_bytes(original)
        corrupt('audit/AUDIT.txt','corrupt public audit derivative')
        corrupt('sections/03_records.tex','corrupt corrected manuscript')
        manifest=json.loads((package/'provenance/upstream-manifest.json').read_text());corrupt('sources/'+manifest['commit']+'/'+manifest['files'][0]['path'],'corrupt pinned upstream source')
        p=package/'checks/strict_check.py';original=p.read_text();needle='angular_scalar == 2 * s.pi / 3'
        if original.count(needle)!=2: raise RuntimeError('Angular negative control cannot locate both guard occurrences.')
        p.write_text(original.replace(needle,'angular_scalar == 2 * s.pi / 4'));run('wrong angular normalization',package,'strict_check.py',[],False);p.write_text(original)
        # Package checks become available after manifest generation. Until then run only mathematical/source controls.
        if (ROOT/'package-manifest.json').is_file():
            run('real exact-inventory package',ROOT,'verify_package.py',[],True)
            p=package/'unexpected-public-file.txt';p.write_text('must be rejected\n');run('unlisted file rejected',package,'verify_package.py',[],False);p.unlink()
            p=package/'README.txt';original=p.read_bytes();p.write_bytes(original+b'corruption\n');run('listed content corruption rejected',package,'verify_package.py',[],False);p.write_bytes(original)
            p=package/'package-manifest.json';original=p.read_text();m=json.loads(original);m['files'].append(m['files'][0]);p.write_text(json.dumps(m));run('duplicate manifest row rejected',package,'verify_package.py',[],False);p.write_text(original)
    report={'public_checker_ast_asserts':0,'case_count':len(cases),'all_expectations_met':True,'cases':cases};args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__': main()
