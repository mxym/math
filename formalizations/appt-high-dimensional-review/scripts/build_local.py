#!/usr/bin/env python3
"""Bounded sequential compilation of this review's actual Lean dependency closure.
Uses the pinned Mathlib environment; compiles only imported modules, not the old 879-module target.
This is a build runner, not a replacement for the kernel replay.
"""
from __future__ import annotations
import argparse, hashlib, json, os, re, subprocess, sys, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
OLD = ROOT.parent / 'appt-qutrit-purity'
OUT = ROOT / '.lake/build/lib/lean'
LOGS = ROOT / 'verification/development'

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def source(name: str) -> tuple[Path, Path]:
    base = OLD if name.startswith('APPT.') or name.startswith('Verification.') else ROOT
    p = base / (name.replace('.', '/')+'.lean')
    if not p.is_file():
        raise FileNotFoundError(p)
    return base, p

def imports(path: Path) -> list[str]:
    return [x for match in re.finditer(r'^import\s+([^\n]+)', path.read_text(), re.M)
            for x in match[1].split() if x == 'APPTReview' or x.startswith(('APPT.', 'APPTReview.', 'Verification.'))]

def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('target',nargs='?',default='APPTReview.Star')
    ap.add_argument('--fresh',action='store_true')
    ap.add_argument('--only',action='store_true')
    ap.add_argument('--timeout',type=int,default=240)
    ap.add_argument('--memory',type=int,default=4096)
    args=ap.parse_args()
    OUT.mkdir(parents=True,exist_ok=True);LOGS.mkdir(parents=True,exist_ok=True)
    env=os.environ.copy()
    # LEAN_BIN may be supplied explicitly for a non-elan pinned installation.
    lean=env.get('LEAN_BIN','lean')
    env['PATH']=str(Path(lean).parent)+os.pathsep+env.get('PATH','')
    packages=ROOT/'.lake/packages'
    paths=[OUT]+[p/'.lake/build/lib/lean' for p in packages.iterdir() if p.is_dir()]
    env['LEAN_PATH']=os.pathsep.join(map(str,paths))
    ordered=[];seen=set()
    def visit(n):
        if n in seen:return
        seen.add(n);_,p=source(n)
        if not args.only:
            for d in imports(p):visit(d)
        ordered.append(n)
    visit(args.target)
    stamps_path=ROOT/'.lake/review-build-stamps.json'
    stamps=json.loads(stamps_path.read_text()) if stamps_path.exists() else {}
    for n in ordered:
        base,p=source(n);o=OUT/(n.replace('.','/')+'.olean')
        sig={'source':digest(p),'imports':{d:digest(OUT/(d.replace('.','/')+'.olean')) for d in imports(p)}}
        if not args.fresh and o.exists() and stamps.get(n)==sig:
            print('REUSE_SOURCE_BOUND',n,flush=True);continue
        o.parent.mkdir(parents=True,exist_ok=True)
        for old in o.parent.glob(o.name+'*'):old.unlink()
        cmd=[lean,'-j1','-M'+str(args.memory),'--root='+str(base),str(p),'-o',str(o)]
        start=time.monotonic();stamp=time.time_ns();log=LOGS/f'{stamp}-{n}.log'
        try:
            proc=subprocess.run(cmd,cwd=ROOT,env=env,text=True,capture_output=True,timeout=args.timeout)
            code=proc.returncode;text=proc.stdout+proc.stderr
        except subprocess.TimeoutExpired as e:
            code=124;text='TIMEOUT\n'+str(e.stdout or '')+'\n'+str(e.stderr or '')
        log.write_text(text)
        record={'module':n,'source_sha256':sig['source'],'command':cmd,'exit_code':code,
                'seconds':round(time.monotonic()-start,3),'log':str(log.relative_to(ROOT)),
                'log_sha256':digest(log)}
        with (LOGS/'events.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
        print(json.dumps(record),flush=True)
        if code:
            print(text,flush=True);sys.exit(code)
        if not o.exists():raise RuntimeError('Successful process did not create '+str(o))
        stamps[n]=sig;stamps_path.write_text(json.dumps(stamps,indent=2)+'\n')
    print('REVIEW_BUILD_PASS',args.target,len(ordered),'local modules in dependency closure',flush=True)
if __name__=='__main__':main()
