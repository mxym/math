#!/usr/bin/env python3
"""Bounded per-module Lean builds, with source hashes and resumable DAG scheduling."""
from __future__ import annotations
import argparse, concurrent.futures, hashlib, json, os, shutil, subprocess, time, signal
from pathlib import Path


def digest(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,default=Path('.'))
    ap.add_argument('--case',action='append',default=[])
    ap.add_argument('--jobs',type=int,default=2)
    ap.add_argument('--timeout',type=int,default=180)
    ap.add_argument('--fresh',action='store_true')
    ap.add_argument('--engine',choices=['lean','lake'],default='lean')
    args=ap.parse_args();root=args.root.resolve()
    lean=shutil.which('lean')
    if lean is None: raise RuntimeError('Run through lake env with the pinned Lean on PATH')
    graph={'APPT.Core':[]}
    for case in args.case or ['Uniform']:
        graph.update(json.loads((root/f'generated-{case}.json').read_text())['modules'])
    logdir=root/'logs'/'blocks';logdir.mkdir(parents=True,exist_ok=True)
    outdir=root/'.lake'/'build'/'lib'/'lean'
    done={};pending=set(graph);running={};failed=[]
    def execute(module: str) -> dict:
        source=root/(module.replace('.','/')+'.lean');out=outdir/(module.replace('.','/')+'.olean')
        out.parent.mkdir(parents=True,exist_ok=True)
        record=logdir/(module+'.json');source_hash=digest(source)
        dep_hashes={d:done[d]['olean_sha256'] for d in graph[module]}
        if not args.fresh and record.exists() and out.exists():
            old=json.loads(record.read_text())
            if old.get('engine','lean')==args.engine and old.get('exit_code')==0 and old.get('source_sha256')==source_hash and old.get('dependency_oleans')==dep_hashes and old.get('olean_sha256')==digest(out):
                return old
        command=([lean,'-j1','-M12288','-o',str(out),str(source)] if args.engine=='lean' else ['lake','build','+'+module])
        started=time.time();timed_out=False
        with (logdir/(module+'.log')).open('w') as f:
            proc=subprocess.Popen(command,cwd=root,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            try:
                code=proc.wait(timeout=args.timeout)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid,signal.SIGKILL)
                proc.wait()
                code=124;timed_out=True
        result={'engine':args.engine,'module':module,'source_sha256':source_hash,'dependency_oleans':dep_hashes,
                'command':command,'exit_code':code,'timed_out':timed_out,'seconds':round(time.time()-started,3),
                'olean_sha256':digest(out) if code==0 and out.exists() else None,
                'log_sha256':digest(logdir/(module+'.log'))}
        record.write_text(json.dumps(result,indent=2)+'\n')
        print(f'{module}: exit={code}, seconds={result["seconds"]}',flush=True)
        return result
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            if not failed:
                ready=sorted(m for m in pending if all(d in done for d in graph[m]))
                while ready and len(running)<args.jobs:
                    m=ready.pop(0);pending.remove(m);running[pool.submit(execute,m)]=m
            if not running:
                if pending and not failed: raise RuntimeError('Unresolved module dependency graph')
                break
            completed,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
            for f in completed:
                m=running.pop(f);result=f.result()
                if result['exit_code']==0:done[m]=result
                else:
                    failed.append(m)
                    print((logdir/(m+'.log')).read_text()[-7000:],flush=True)
    report={'status':'PASS' if not failed and not pending else 'FAIL','completed':len(done),
            'total':len(graph),'failed':failed,'blocked':sorted(pending),'timeout_seconds_per_module':args.timeout,
            'jobs':args.jobs,'lean_version':subprocess.check_output([lean,'--version'],text=True).strip()}
    (logdir/'SUMMARY.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)
    if report['status']!='PASS':raise SystemExit(1)

if __name__=='__main__':main()
