#!/usr/bin/env python3
"""Independent completion endpoint audit; all generated evidence has a new prefix.

--plan validates the draft scope without freezing it or building mathematics.
--freeze-source creates an immutable binding after the owner marks SCOPE READY.
The default requires that binding, builds, reports every selected axiom set,
then positively replays the whole endpoint/definition closure at trust zero and
requires rejection of same-type forged theorem proofs. Never modifies old audit
inputs or deletes a dependency cache.
"""
from pathlib import Path
import argparse, datetime, fcntl, hashlib, json, os, re, shutil, signal, subprocess, sys, time
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parent.parent
PIN='d13f23b723b8a846827a245b89c10fc7d3f11612'
ALLOW={'propext','Classical.choice','Quot.sound'}
NEW=['extraction-operational-completion','extraction-deviation-completion',
     'extraction-cp-interface','extraction-schur-completion',
     'extraction-circuit-completion','extraction-circuit-recursion',
     'extraction-completion-audit']
OLD=['extraction-connections','extraction-spectral-protocol',
     'spectral-extraction-core','appt-high-dimensional-review',
     'extraction-information-spectrum','appt-subunit-renyi',
     'extraction-symmetric-support','spectral-extraction-local-cap']


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def readj(p): return json.loads(p.read_text())
def dump(p,obj): p.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
def run(*args): return subprocess.check_output(args,cwd=REPO,text=True).strip()


def source_without_comments(txt):
    # Lean's nested block comments are respected. This scanner is only an
    # inventory aid; actual declaration existence and types are checked by Lean.
    out=[];depth=0;i=0
    while i<len(txt):
        if txt[i:i+2]=='/-': depth+=1;i+=2
        elif depth and txt[i:i+2]=='-/':depth-=1;i+=2
        elif depth:
            if txt[i]=='\n':out.append('\n')
            i+=1
        elif txt[i:i+2]=='--':
            e=txt.find('\n',i);i=len(txt) if e<0 else e
        else:out.append(txt[i]);i+=1
    if depth:raise RuntimeError('Unclosed comment')
    return ''.join(out)


def scope_lists():
    s=readj(ROOT/'SCOPE.json')
    roots=[n for g in s['groups'] for n in g['theorem_roots']]
    defs=[n for g in s['groups'] for n in g['definition_roots']]
    controls=[n for g in s['groups'] for n in g['controls']]
    for filename,ls in [('ROOTS.txt',roots),('DEFINITIONS.txt',defs),('CONTROLS.txt',controls)]:
        if len(ls)!=len(set(ls)) or (ROOT/filename).read_text().splitlines()!=ls:
            raise RuntimeError('Scope/list disagreement '+filename)
    if set(roots)&set(defs) or not set(controls)<=set(roots):raise RuntimeError('Bad declaration classes')
    expected='import CompletionAudit\n\n'+''.join('#check '+n+'\n#print axioms '+n+'\n' for n in roots+defs)
    if (ROOT/'Check.lean').read_text()!=expected:raise RuntimeError('Check.lean scope drift')
    audit='import CompletionAudit\nimport CompletionVerification.ReplaySupport\n\nrun_cmd CompletionVerification.replayAll [\n'+',\n'.join('  ``'+n for n in roots+defs)+'\n] "verification/completion-kernel"\n\n'+''.join('run_cmd CompletionVerification.rejectCorruptTheorem ``'+n+' "verification/completion-control-'+str(i+1)+'"\n' for i,n in enumerate(controls))
    if (ROOT/'Audit.lean').read_text()!=audit:raise RuntimeError('Audit.lean scope drift')
    return s,roots,defs,controls


def package_roots():
    # The audit root manifest contains every transitive local package.
    result=[ROOT]
    for d in readj(ROOT/'lake-manifest.json')['packages']:
        if d['type']=='path':
            p=(ROOT/d['dir']).resolve()
            if not p.is_relative_to(REPO.resolve()):raise RuntimeError('External local source '+str(p))
            result.append(p)
    return result


def inventory():
    pkgs=package_roots()
    owned={p for p in ROOT.rglob('*') if p.is_file() and
           not any(c in {'.lake','verification','__pycache__'} for c in p.relative_to(ROOT).parts)
           and p.name not in {'SOURCE_HASHES.json','FROZEN_OLD_INPUTS.json'}}
    todo=[ROOT/'CompletionAudit.lean'];selected=set(owned);seen=set()
    while todo:
        p=todo.pop()
        if p in seen:continue
        seen.add(p)
        raw=source_without_comments(p.read_text())
        if p.parent!=ROOT and re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',raw):
            raise RuntimeError('Forbidden mathematical proof token '+str(p))
        for line in re.findall(r'^import\s+([^\n]+)',raw,re.M):
            for mod in line.split():
                if mod in {'Lean','Mathlib'} or mod.startswith(('Mathlib.','Lean.','Batteries.','Aesop.','Qq.')):continue
                found=[q/(mod.replace('.','/')+'.lean') for q in pkgs]
                found=[q for q in found if q.is_file()]
                if len(found)!=1:raise RuntimeError('Missing/nonunique local import '+mod)
                if found[0] not in selected:selected.add(found[0])
                todo.append(found[0])
    for pkg in pkgs:
        for n in ['lakefile.toml','lakefile.lean','lake-manifest.json','lean-toolchain']:
            if (pkg/n).is_file():selected.add(pkg/n)
    return {p.relative_to(REPO).as_posix():sha(p) for p in sorted(selected)}


def old_inventory():
    # Every tracked old audit source/config/evidence remains bound byte-for-byte.
    names=run('git','ls-files',*[str(Path('formalizations')/p) for p in OLD]).splitlines()
    return {n:sha(REPO/n) for n in names}


def check_execution_inputs():
    for n,digest in readj(ROOT/'EXECUTION_INPUTS.json').items():
        p=Path(n)
        if not p.is_file() or sha(p)!=digest:raise RuntimeError('Changed execution input '+n)


def check_pins():
    if (ROOT/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.34.1':raise RuntimeError('Wrong Lean')
    deps=readj(ROOT/'lake-manifest.json')['packages']
    if [d.get('rev') for d in deps if d['name']=='mathlib']!=[PIN]:raise RuntimeError('Wrong Mathlib manifest pin')
    for d in deps:
        if d['type']!='git':continue
        p=ROOT/'.lake/packages'/d['name']
        if run('git','-C',str(p),'rev-parse','HEAD')!=d['rev']:raise RuntimeError('Wrong actual dependency '+d['name'])
        if subprocess.run(['git','-C',str(p),'diff','--quiet','HEAD','--']).returncode:raise RuntimeError('Dirty tracked dependency '+d['name'])
    # Preserve the previous audit's explicit safeguard against a nonstandard
    # Mathlib Multinomial cache without changing that audit or its cache.
    standard=REPO/'formalizations/extraction-connections/STANDARD_CACHE.json'
    for n,digest in readj(standard).items():
        p=ROOT/'.lake/packages/mathlib/.lake/build'/n
        if p.exists() and sha(p)!=digest:raise RuntimeError('Nonstandard Mathlib artifact '+n)


def check_binding():
    s,roots,defs,controls=scope_lists()
    if s['state']!='READY' or s['pending_required']:raise RuntimeError('Scope is preliminary; final endpoints are still pending')
    if inventory()!=readj(ROOT/'SOURCE_HASHES.json'):raise RuntimeError('Bound source/config changed')
    if old_inventory()!=readj(ROOT/'FROZEN_OLD_INPUTS.json'):raise RuntimeError('Older audit input/evidence changed')
    for n in inventory():
        if n.startswith(ROOT.relative_to(REPO).as_posix()+'/'):continue
        expected=subprocess.check_output(['git','show',s['source_head']+':'+n],cwd=REPO)
        if expected!=(REPO/n).read_bytes():raise RuntimeError('Source differs from frozen mathematical head '+n)
    check_pins()
    return s,roots,defs,controls


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--plan',action='store_true')
    ap.add_argument('--freeze-source',action='store_true')
    ap.add_argument('--check-only',action='store_true')
    ap.add_argument('--fresh',action='store_true')
    args=ap.parse_args()
    s,roots,defs,controls=scope_lists()
    if args.plan:
        print(json.dumps({'state':s['state'],'mathematical_source_head':s['source_head'],
          'source_inputs':len(inventory()),'endpoint_theorems':len(roots),'model_definitions':len(defs),
          'same_type_controls':len(controls),'pending_required':s['pending_required'],
          'verification_performed':False},ensure_ascii=False));return
    check_execution_inputs()
    # Imported only after read-only planning: all builds/evidence need the D guard.
    sys.path.insert(0,'/mnt/d/math/tmp/extraction-full-lean-20261016')
    from ensure_d_storage import configure_env
    env=configure_env(dict(os.environ))
    env['PATH']='/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env.get('PATH','')
    if args.freeze_source:
        if s['state']!='READY' or s['pending_required']:raise RuntimeError('Refusing preliminary freeze')
        if (ROOT/'SOURCE_HASHES.json').exists():raise RuntimeError('Binding already exists; start a new audit revision')
        check_pins()
        dump(ROOT/'FROZEN_OLD_INPUTS.json',old_inventory())
        dump(ROOT/'SOURCE_HASHES.json',inventory())
        check_binding()
        print('SOURCE_BINDING_CREATED_NOT_VERIFICATION');return
    s,roots,defs,controls=check_binding()
    if args.check_only:print('SOURCE_BINDING_PASS');return
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    out=ROOT/'verification'/('completion-'+stamp);out.mkdir(parents=True)
    records=[]
    dump(out/'EXECUTION.json',dict(execution_inputs=readj(ROOT/'EXECUTION_INPUTS.json'),
      python=sys.version,guard='D_BACKED_STORAGE_VERIFIED',
      environment={n:env.get(n) for n in ['TMPDIR','MATHLIB_CACHE_DIR','XDG_CACHE_HOME']}))
    def stage(label,cmd,limit):
        log=out/(label+'.log');start=time.monotonic()
        with log.open('w') as f:
            p=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            try:code=p.wait(timeout=limit)
            except subprocess.TimeoutExpired:
                os.killpg(p.pid,signal.SIGKILL);p.wait();code=124
        rec=dict(stage=label,command=cmd,exit_code=code,seconds=round(time.monotonic()-start,3),log=log.name,sha256=sha(log))
        records.append(rec);dump(out/'STAGES.json',records);print(json.dumps(rec),flush=True)
        if code:raise RuntimeError('Failed stage '+label+'; see '+str(log))
        return log.read_text()
    with open('/mnt/lean-research-d/tmp/extraction-shared-build.lock','a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        # Preflight every path before deleting only reproducible owned outputs.
        if args.fresh:
            outputs=[REPO/'formalizations'/n/'.lake/build' for n in NEW]
            for p in outputs:
                if p.is_symlink() or not p.resolve().is_relative_to(REPO.resolve()) or p.name!='build':raise RuntimeError('Unsafe fresh output '+str(p))
            for p in outputs:
                if p.exists():shutil.rmtree(p)
        stage('toolchain',['lake','env','lean','--version'],90)
        for label,target in [('deviation','@extractionDeviationCompletion/Deviation'),
          ('operational','@extractionOperationalCompletion/OperationalCompletion'),
          ('cp','@extractionCPInterface/CPInterface'),('schur','@extractionSchurCompletion/SchurCompletion'),
          ('circuits','@extractionCircuitRecursion/CircuitRecursion')]:
            stage('build-'+label,['lake','build',target],2400)
        stage('build-audit',['lake','build','CompletionAudit','CompletionVerification'],1800)
        stage('root-types-axioms',['lake','env','lean','-j1','-M10000','Check.lean'],600)
        audit=stage('trust0-replay',['lake','env','lean','-j1','-M11000','Audit.lean'],2400)
        if audit.count('EMPTY_KERNEL_REPLAY_PASS')!=1 or audit.count('CORRUPTED_PROOF_REJECTED')!=len(controls) or audit.count('TYPE_CLOSURE_REPLAY_PASS')!=len(controls):raise RuntimeError('Missing replay/control markers')
        axs=set((ROOT/'verification/completion-kernel-axioms.txt').read_text().splitlines())
        if not axs<=ALLOW:raise RuntimeError('Unexpected replay axiom')
        for p in (ROOT/'verification').glob('completion-*.txt'):shutil.copy2(p,out/p.name)
        shutil.copy2(ROOT/'SOURCE_HASHES.json',out/'SOURCE_HASHES.json')
        shutil.copy2(ROOT/'SCOPE.json',out/'SCOPE.json')
        check_binding()
        summary=dict(status='PASS',scope=s['scope_note'],mathematical_source_head=s['source_head'],
          source_inputs=len(inventory()),endpoint_theorems=len(roots),model_definitions=len(defs),
          same_type_forged_proof_controls=len(controls),kernel_trust=0,
          kernel_declarations=int(re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations',audit).group(1)),
          axioms=sorted(axs),fresh_owned_build=args.fresh,fresh_packages=NEW if args.fresh else [],
          source_manifest_sha256=sha(ROOT/'SOURCE_HASHES.json'),stages=records)
        dump(out/'SUMMARY.json',summary)
        dump(ROOT/'verification/LATEST.json',dict(directory=out.name,summary_sha256=sha(out/'SUMMARY.json')))
        print('COMPLETION_INDEPENDENT_REPRODUCTION_PASS '+str(out),flush=True)


if __name__=='__main__':main()
