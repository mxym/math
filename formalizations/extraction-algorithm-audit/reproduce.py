#!/usr/bin/env python3
"""Independent added algorithm audit; all generated evidence has a new prefix.

--plan validates the draft scope without freezing it or building mathematics.
--freeze-source creates an immutable binding after the owner marks SCOPE READY.
The default requires that binding, builds, reports every selected axiom set,
then positively replays the whole endpoint/definition closure at trust zero and
requires rejection of same-type forged theorem proofs. Never modifies old audit
inputs or deletes a dependency cache.
"""
from pathlib import Path
import argparse, datetime, fcntl, hashlib, json, os, re, resource, shutil, signal, subprocess, sys, time
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parent.parent
PIN='d13f23b723b8a846827a245b89c10fc7d3f11612'
OLD_BASELINE='aa1cd0c497a4a9963013ec6dde76a5ed296e2c61'
ALLOW={'propext','Classical.choice','Quot.sound'}
TEX_NAMES=['paper.tex','introduction.tex','spectral-principles.tex','universal-protocol.tex',
  'asymptotic-laws.tex','unknown-support.tex','applications-verification.tex','references.tex']
FROZEN_TEX='preprints/universal-entanglement-extraction-2026-10'
DRAFT_TEX='preprints/universal-entanglement-extraction-revision-2026-10'
NEW=['extraction-numerical-synthesis','extraction-effective-encoding','extraction-algorithm-audit']

OLD=['extraction-matrix-projector','extraction-universal-orbit',
     'extraction-minimax-profile','appt-qutrit-purity',
     'extraction-connections','extraction-spectral-protocol',
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
    expected='import AlgorithmAudit\nimport AlgorithmVerification.ReplaySupport\n\nset_option pp.universes true\nset_option pp.explicit true\nset_option pp.fullNames true\n\nrun_cmd (AlgorithmVerification.checkKinds [\n'+',\n'.join('  ``'+n for n in roots)+'\n] [\n'+',\n'.join('  ``'+n for n in defs)+'\n])\n\n'+''.join('#check '+n+'\nset_option pp.universes false in #print axioms '+n+'\n' for n in roots+defs)
    if (ROOT/'Check.lean').read_text()!=expected:raise RuntimeError('Check.lean scope drift')
    audit='import AlgorithmAudit\nimport AlgorithmVerification.ReplaySupport\n\nrun_cmd (AlgorithmVerification.replayAll [\n'+',\n'.join('  ``'+n for n in roots+defs)+'\n] "verification/algorithm-kernel")\n\n'+''.join('run_cmd AlgorithmVerification.rejectCorruptTheorem ``'+n+' "verification/algorithm-control-'+str(i+1)+'"\n' for i,n in enumerate(controls))
    if (ROOT/'Audit.lean').read_text()!=audit:raise RuntimeError('Audit.lean scope drift')
    declaration_map()
    manuscript_map()
    return s,roots,defs,controls



def declaration_map():
    rows=[]
    pattern=re.compile(r"^(?:@\[[^\n]*\]\s*)?(?P<nc>noncomputable\s+)?(?P<kind>theorem|lemma|def|abbrev|structure|inductive)\s+(?P<name>[A-Za-z_][A-Za-z0-9_.']*)",re.M)
    # Fixed reviewed files; unrelated later modules do not silently expand this scope.
    files=[]
    for d in readj(ROOT/'DECLARATIONS.json'):
        if d['source']not in files:files.append(d['source'])
    for rel in files:
        p=REPO/rel
        expected_namespace='CircuitRecursion'if rel.startswith('formalizations/extraction-numerical-synthesis/CircuitNumerical/')else'EffectiveEncoding'if rel.startswith('formalizations/extraction-effective-encoding/EffectiveEncoding/')else None
        if expected_namespace is None or not p.is_file():raise RuntimeError('Unexpected/missing explicitly selected source '+rel)
        raw=source_without_comments(p.read_text())
        if re.findall(r'^namespace\s+(\S+)',raw,re.M)!=[expected_namespace]:raise RuntimeError('Unexpected namespace '+str(p))
        for m in pattern.finditer(raw):
            rows.append(dict(name=expected_namespace+'.'+m['name'],kind=m['kind'],noncomputable=bool(m['nc']),source=p.relative_to(REPO).as_posix(),line=raw[:m.start()].count('\n')+1))
    if rows!=readj(ROOT/'DECLARATIONS.json'):raise RuntimeError('Source declaration inventory changed')
    s=readj(ROOT/'SCOPE.json')
    roots=[n for g in s['groups']for n in g['theorem_roots']]
    models=[n for g in s['groups']for n in g['definition_roots']]
    if roots!=[r['name']for r in rows if r['kind']in {'theorem','lemma'}] or models!=[r['name']for r in rows if r['kind']not in {'theorem','lemma'}]:raise RuntimeError('Selected scope omits or reclassifies source declarations')
    return rows


def manuscript_map():
    s=readj(ROOT/'SCOPE.json')
    paths=[p for p in s['manuscript_documents']if Path(p).name=='MANUSCRIPT_CLAIMS.json']
    if not paths:return []
    if len(paths)!=1:raise RuntimeError('Ambiguous manuscript map')
    core=readj(REPO/'formalizations/extraction-completion-audit/SCOPE.json')
    classes={}
    for label,scope in [('algorithm',s),('sealed_completion',core)]:
        for g in scope['groups']:
            for n in g['theorem_roots']:classes[n]=(label,'theorem')
            for n in g['definition_roots']:classes[n]=(label,'model')
    resolved=[]
    for claim in readj(REPO/paths[0])['claims']:
        for d in claim['declarations']:
            name=d['name']
            if name not in classes:raise RuntimeError('Mapped declaration outside both fixed proof scopes '+name)
            p=REPO/d['path'];lines=p.read_text().splitlines();line=d['line']
            if not p.resolve().is_relative_to((REPO/'formalizations').resolve())or not 0<line<=len(lines):raise RuntimeError('Invalid mapped source location')
            namespaces=re.findall(r'^namespace\s+(\S+)','\n'.join(lines[:line]),re.M)
            if len(namespaces)!=1 or not name.startswith(namespaces[0]+'.'):raise RuntimeError('Mapped namespace changed '+name)
            local=name[len(namespaces[0])+1:]
            if not re.search(r'^(?:noncomputable )?'+re.escape(d['kind'])+r'\s+'+re.escape(local)+r'(?=\s|\(|\{|:|$)',lines[line-1]):raise RuntimeError('Mapped kind/name/line changed '+name)
            label,kind=classes[name]
            if (d['kind']in {'theorem','lemma'})!=(kind=='theorem'):raise RuntimeError('Mapped declaration kind differs from proof scope '+name)
            resolved.append(dict(claim=claim['label'],manuscript=claim['manuscript'],name=name,kind=d['kind'],source=d['path'],line=line,proof_scope=label,conditions_and_scope=claim['conditions_and_scope']))
    if len(resolved)!=len({x['name']for x in resolved}):raise RuntimeError('Duplicate mapped declaration')
    expected=ROOT/'MANUSCRIPT_RESOLVED_ROOTS.json'
    if expected.exists()and readj(expected)!=resolved:raise RuntimeError('Resolved manuscript map changed')
    return resolved


def parse_axiom_report(log,expected):
    rows=[]
    for name,axioms in re.findall(r"^'(.*)' depends on axioms: \[([^\]]*)\]$",log,re.M):
        rows.append((name,[x.strip() for x in axioms.split(",") if x.strip()]))
    rows += [(name,[]) for name in re.findall(r"^'(.*)' does not depend on any axioms$",log,re.M)]
    if len(rows)!=len(expected) or {n for n,_ in rows}!=set(expected):raise RuntimeError("Missing/duplicate axiom report")
    if any(not set(axs)<=ALLOW for _,axs in rows):raise RuntimeError("Unexpected selected declaration axiom")
    return dict(rows)


def package_roots():
    # The audit root manifest contains every transitive local package.
    result=[ROOT]
    for d in readj(ROOT/'lake-manifest.json')['packages']:
        if d['type']=='path':
            p=(ROOT/d['dir']).resolve()
            if not p.is_relative_to(REPO.resolve()):raise RuntimeError('External local source '+str(p))
            result.append(p)
    return result



def frozen_manuscript_inventory():
    # Separate new-scope preservation safeguard; never enlarges an old Lean
    # audit or reuses its kernel result for manuscript coverage.
    result={}
    for name in TEX_NAMES:
        rel=FROZEN_TEX+'/'+name
        original=subprocess.check_output(['git','show',OLD_BASELINE+':'+rel],cwd=REPO)
        if (REPO/rel).read_bytes()!=original:raise RuntimeError('Frozen manuscript changed '+rel)
        result[rel]=hashlib.sha256(original).hexdigest()
    return result


def validate_source_head(s,inputs):
    for name in inputs:
        if name.startswith(ROOT.relative_to(REPO).as_posix()+'/'):continue
        original=subprocess.check_output(['git','show',s['source_head']+':'+name],cwd=REPO)
        if original!=(REPO/name).read_bytes():raise RuntimeError('Source differs from frozen mathematical/manuscript head '+name)


def inventory():
    pkgs=package_roots();s=readj(ROOT/'SCOPE.json')
    owned={p for p in ROOT.rglob('*')if p.is_file()and not any(c in {'.lake','verification','__pycache__'}for c in p.relative_to(ROOT).parts)and p.name not in {'SOURCE_HASHES.json','FROZEN_OLD_INPUTS.json'}}
    selected=set(owned);todo=[ROOT/'AlgorithmAudit.lean'];seen=set()
    for rel in s['manuscript_inputs']+s['manuscript_documents']+s['supporting_documents']:
        p=REPO/rel
        if not p.resolve().is_relative_to(REPO.resolve())or not p.is_file():raise RuntimeError('Missing/outside input '+rel)
        selected.add(p)
    core=REPO/'formalizations/extraction-completion-audit'
    selected.update(core/n for n in ['SOURCE_HASHES.json','FROZEN_OLD_INPUTS.json'])
    selected.update(REPO/n for n in frozen_manuscript_inventory())
    while todo:
        p=todo.pop()
        if p in seen:continue
        seen.add(p);raw=source_without_comments(p.read_text())
        if not p.resolve().is_relative_to(ROOT.resolve())and re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',raw):raise RuntimeError('Forbidden mathematical proof token '+str(p))
        for line in re.findall(r'^import\s+([^\n]+)',raw,re.M):
            for mod in line.split():
                if mod in {'Lean','Mathlib'}or mod.startswith(('Mathlib.','Lean.','Batteries.','Aesop.','Qq.')):continue
                found=[q/(mod.replace('.','/')+'.lean')for q in pkgs];found=[q for q in found if q.is_file()]
                if len(found)!=1:raise RuntimeError('Missing/nonunique local import '+mod)
                selected.add(found[0]);todo.append(found[0])
    for pkg in pkgs:
        for name in ['lakefile.toml','lakefile.lean','lake-manifest.json','lean-toolchain']:
            if (pkg/name).is_file():selected.add(pkg/name)
    return {p.relative_to(REPO).as_posix():sha(p)for p in sorted(selected)}


def old_inventory():
    # Compare to the first independent review commit, before generating a new
    # hash binding. A later accidental change cannot become the new baseline.
    paths=[str(Path('formalizations')/p) for p in OLD]
    entries=subprocess.check_output(['git','ls-tree','-r','-z',OLD_BASELINE,'--',*paths],cwd=REPO)
    expected={}
    for item in entries.split(b'\0'):
        if not item:continue
        meta,name=item.split(b'\t',1)
        mode,kind,oid=meta.decode().split()
        if kind!='blob':raise RuntimeError('Non-file old audit entry')
        expected[name.decode()]=(mode,oid)
    names=run('git','ls-files','--',*paths).splitlines()
    if len(expected)!=4378:raise RuntimeError('Historical protected inventory count changed')
    if set(names)!=set(expected):raise RuntimeError('Old audit tracked file inventory changed')
    hashes={}
    for n in sorted(names):
        p=REPO/n;mode,oid=expected[n]
        data=os.readlink(p).encode() if mode=='120000' else p.read_bytes()
        current=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if current!=oid:raise RuntimeError('Old audit changed from initial review baseline '+n)
        hashes[n]=hashlib.sha256(data).hexdigest()
    core=REPO/'formalizations/extraction-completion-audit'
    expected=readj(ROOT/'SCOPE.json')['protected_completion']
    if sha(core/'SOURCE_HASHES.json')!=expected['manifest_sha256']:raise RuntimeError('Frozen completion binding changed')
    frozen=readj(core/'SOURCE_HASHES.json')
    if len(frozen)!=605:raise RuntimeError('Completion input count changed')
    for name,digest in frozen.items():
        if sha(REPO/name)!=digest:raise RuntimeError('Frozen completion input changed '+name)
    if readj(core/'FROZEN_OLD_INPUTS.json')!=hashes:raise RuntimeError('Old 4378 baseline differs from sealed completion safeguard')
    seal=core/'verification/SEALED_LOCAL_EVIDENCE.json'
    if sha(seal)!=expected['seal_sha256']:raise RuntimeError('Frozen completion evidence seal changed')
    record=readj(seal)
    archive=core/'verification'/record['archive'];summary=core/record['summary_path']
    if sha(archive)!=expected['archive_sha256']or sha(summary)!=expected['summary_sha256']:raise RuntimeError('Sealed completion archive/summary changed')
    return dict(older_4378=hashes,completion_605=frozen,completion_manifest_sha256=expected['manifest_sha256'],completion_sealed_evidence=dict(seal_sha256=expected['seal_sha256'],archive_sha256=expected['archive_sha256'],summary_sha256=expected['summary_sha256']))


def check_execution_inputs(github_actions=False):
    if github_actions:
        from audit_runtime import check_ci_binaries
        records=check_ci_binaries()
    else:
        records={}
    for n,digest in ([] if github_actions else readj(ROOT/'EXECUTION_INPUTS.json').items()):
        p=Path(n)
        if not p.is_file() or sha(p)!=digest:raise RuntimeError('Changed execution input '+n)
    provenance=ROOT/'WRITTEN_REVIEW_EXECUTION_INPUTS.json'
    if provenance.exists():
        for n,digest in readj(provenance).items():
            p=ROOT/n
            if not p.resolve().is_relative_to(ROOT.resolve()) or sha(p)!=digest:
                raise RuntimeError('Changed written-review execution input '+n)
    return records


def check_pins():
    if (ROOT/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.34.1':raise RuntimeError('Wrong Lean')
    deps=readj(ROOT/'lake-manifest.json')['packages']
    if [d.get('rev') for d in deps if d['name']=='mathlib']!=[PIN]:raise RuntimeError('Wrong Mathlib manifest pin')
    for d in deps:
        if d['type']!='git':continue
        p=ROOT/'.lake/packages'/d['name']
        if run('git','-C',str(p),'rev-parse','HEAD')!=d['rev']:raise RuntimeError('Wrong actual dependency '+d['name'])
        if subprocess.check_output(['git','-C',str(p),'status','--porcelain=v1','--untracked-files=all'],text=True).strip():raise RuntimeError('Dirty/untracked dependency source '+d['name'])
    # Preserve the previous audit's explicit safeguard against a nonstandard
    # Mathlib Multinomial cache without changing that audit or its cache.
    standard=REPO/'formalizations/extraction-connections/STANDARD_CACHE.json'
    for n,digest in readj(standard).items():
        p=ROOT/'.lake/packages/mathlib/.lake/build'/n
        if p.exists() and sha(p)!=digest:raise RuntimeError('Nonstandard Mathlib artifact '+n)


def check_binding():
    s,roots,defs,controls=scope_lists()
    if s['state']!='READY'or s['pending_required']:raise RuntimeError('Scope is preliminary')
    if len(s['manuscript_inputs'])!=8 or {Path(n).name for n in s['manuscript_inputs']}!=set(TEX_NAMES):raise RuntimeError('Final new eight-TeX manuscript is not bound')
    if not s['manuscript_documents']or not any('MAP'in Path(n).name.upper()for n in s['manuscript_documents']):raise RuntimeError('Final new theorem/source map missing')
    if inventory()!=readj(ROOT/'SOURCE_HASHES.json'):raise RuntimeError('Bound source/config changed')
    if old_inventory()!=readj(ROOT/'FROZEN_OLD_INPUTS.json'):raise RuntimeError('Frozen completion or older inputs changed')
    validate_source_head(s,inventory());check_pins()
    return s,roots,defs,controls


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--plan',action='store_true')
    ap.add_argument('--preflight',action='store_true',help='D guard, execution pins and old-input preservation; no final binding or Lean verification')
    ap.add_argument('--freeze-source',action='store_true')
    ap.add_argument('--check-only',action='store_true')
    ap.add_argument('--fresh',action='store_true')
    ap.add_argument('--types-only',action='store_true',help='Preliminary ordinary build, kind/type/axiom and bytecode checks only; no freeze/replay')
    ap.add_argument('--github-actions',action='store_true',help='Explicit hosted Linux GitHub runtime; forbidden on local Windows/WSL')
    args=ap.parse_args()
    if sum([args.plan,args.preflight,args.freeze_source,args.check_only,args.types_only])>1:raise RuntimeError('Select only one preliminary/freeze/check mode')
    if args.github_actions and args.freeze_source:raise RuntimeError('CI requires a pre-existing source binding; it may not create one')
    s,roots,defs,controls=scope_lists()
    if args.plan:
        print(json.dumps({'state':s['state'],'mathematical_source_head':s['source_head'],
          'source_inputs':len(inventory()),'endpoint_theorems':len(roots),'model_definitions':len(defs),
          'same_type_controls':len(controls),'pending_required':s['pending_required'],
          'verification_performed':False},ensure_ascii=False));return
    binary_inputs=check_execution_inputs(args.github_actions)
    from audit_runtime import configure
    runtime=configure(args.github_actions)
    env=runtime['env']
    if args.preflight:
        check_pins()
        old=old_inventory()
        print(json.dumps(dict(status='PREFLIGHT_ONLY',source_head=s['source_head'],source_inputs=len(inventory()),protected_old_inputs=len(old['older_4378']),protected_completion_inputs=len(old['completion_605']),protected_frozen_tex=len(frozen_manuscript_inventory()),draft_tex_inputs=len(s['manuscript_inputs']),manuscript_documents=len(s['manuscript_documents']),verification_performed=False)))
        return
    if args.freeze_source:
        if s['state']!='READY' or s['pending_required']:raise RuntimeError('Refusing preliminary freeze')
        if (ROOT/'SOURCE_HASHES.json').exists():raise RuntimeError('Binding already exists; start a new audit revision')
        check_pins()
        old=old_inventory();inputs=inventory()
        validate_source_head(s,inputs)
        dump(ROOT/'FROZEN_OLD_INPUTS.json',old)
        dump(ROOT/'SOURCE_HASHES.json',inputs)
        check_binding()
        print('SOURCE_BINDING_CREATED_NOT_VERIFICATION');return
    if args.types_only:
        check_pins();old_inventory();validate_source_head(s,inventory())
        preliminary_inputs=inventory()
    else:s,roots,defs,controls=check_binding()
    if args.check_only:print('SOURCE_BINDING_PASS');return
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    outbase=runtime['output'];outbase.mkdir(parents=True,exist_ok=True)
    out=outbase/('algorithm-'+stamp);out.mkdir()
    records=[]
    dump(out/'EXECUTION.json',dict(execution_inputs=readj(ROOT/('CI_EXECUTION_POLICY.json' if args.github_actions else 'EXECUTION_INPUTS.json')),
      python=sys.version,guard=runtime['guard'],portable_binary_inputs=binary_inputs,
      runtime={k:str(v) for k,v in runtime.items() if k!='env'},
      environment={n:env.get(n) for n in ['TMPDIR','MATHLIB_CACHE_DIR','XDG_CACHE_HOME']}))
    def stage(label,cmd,limit):
        log=out/(label+'.log');start=time.monotonic()
        with log.open('w') as f:
            p=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            try:code=p.wait(timeout=limit)
            except subprocess.TimeoutExpired:
                os.killpg(p.pid,signal.SIGKILL);p.wait();code=124
        rec=dict(stage=label,command=cmd,exit_code=code,seconds=round(time.monotonic()-start,3),log=log.name,sha256=sha(log),peak_child_rss_kib_cumulative=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
        records.append(rec);dump(out/'STAGES.json',records);print(json.dumps(rec),flush=True)
        if code:raise RuntimeError('Failed stage '+label+'; see '+str(log))
        return log.read_text()
    with open(runtime['lock'],'a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        # Preflight every path before deleting only reproducible owned outputs.
        if args.fresh:
            outputs=[REPO/'formalizations'/n/'.lake/build' for n in NEW]
            for p in outputs:
                if p.is_symlink() or not p.resolve().is_relative_to(REPO.resolve()) or p.name!='build':raise RuntimeError('Unsafe fresh output '+str(p))
            for p in outputs:
                if p.exists():shutil.rmtree(p)
        stage('toolchain',['lake','env','lean','--version'],90)
        for label,target in [('numerical','@extractionNumericalSynthesis/CircuitNumerical'),('effective','@extractionEffectiveEncoding/EffectiveEncoding')]:
            stage('build-'+label,['lake','build',target],2400)
        stage('build-audit',['lake','build','AlgorithmAudit','AlgorithmVerification'],1800)
        types=stage('root-types-axioms',['lake','env','lean','-j1','-M'+str(min(10000,runtime['memory_mb'])),'Check.lean'],600)
        if types.count('DECLARATION_KIND_CHECK_PASS')!=1:raise RuntimeError('Missing declaration kind marker')
        dump(out/'AXIOM_REPORT.json',parse_axiom_report(types,roots+defs))
        bytecode=stage('finite-syntax-bytecode',['lake','env','lean','-j1','-M4000','--run','ExecutableCheck.lean'],300)
        if bytecode.count('FINITE_SYNTAX_BYTECODE_CHECK_PASS')!=1:raise RuntimeError('Missing actual finite syntax bytecode marker')
        if args.types_only:
            if inventory()!=preliminary_inputs:raise RuntimeError('Preliminary source/config drift')
            if binary_inputs!=check_execution_inputs(args.github_actions):raise RuntimeError('Preliminary execution binary drift')
            dump(out/'SUMMARY.json' ,dict(status='PRELIMINARY_KIND_TYPE_AXIOM_BYTECODE_PASS_NOT_KERNEL_REPLAY',source_head=s['source_head'],endpoint_theorems=len(roots),model_definitions=len(defs),control_candidates=len(controls),stages=records,source_inputs=inventory(),protected_inputs=old_inventory()))
            print('ALGORITHM_PRELIMINARY_TYPES_PASS '+str(out),flush=True);return
        invocation=out/'AuditInvocation.lean' 
        invocation.write_text((ROOT/'Audit.lean').read_text().replace('\"verification/algorithm-',json.dumps(str(out/'algorithm-'))[:-1]))
        audit=stage('trust0-replay',['lake','env','lean','-j1','-M'+str(runtime['memory_mb']),str(invocation)],7200)
        if audit.count('EMPTY_KERNEL_REPLAY_PASS')!=1 or audit.count('CORRUPTED_PROOF_REJECTED')!=len(controls) or audit.count('TYPE_CLOSURE_REPLAY_PASS')!=len(controls) or audit.count('CORRUPTED_PROOF_TYPE_MISMATCH_REJECTED')!=len(controls):raise RuntimeError('Missing replay/control markers')
        axs=set((out/'algorithm-kernel-axioms.txt').read_text().splitlines())
        if not axs<=ALLOW:raise RuntimeError('Unexpected replay axiom')
        shutil.copy2(ROOT/'SOURCE_HASHES.json',out/'SOURCE_HASHES.json')
        shutil.copy2(ROOT/'SCOPE.json',out/'SCOPE.json')
        check_binding()
        if binary_inputs!=check_execution_inputs(args.github_actions):raise RuntimeError('Execution binary drift during audit')
        summary=dict(status='PASS',scope=s['scope_note'],mathematical_source_head=s['source_head'],
          source_inputs=len(inventory()),endpoint_theorems=len(roots),model_definitions=len(defs),
          same_type_forged_proof_controls=len(controls),kernel_trust=0,
          runtime_guard=runtime['guard'],audit_invocation_sha256=sha(invocation),
          kernel_declarations=int(re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations',audit).group(1)),
          axioms=sorted(axs),fresh_owned_build=args.fresh,fresh_packages=NEW if args.fresh else [],
          source_manifest_sha256=sha(ROOT/'SOURCE_HASHES.json'),
          manuscript_source_head=s['source_head'],manuscript_inputs=s['manuscript_inputs'],
          manuscript_documents=s['manuscript_documents'],
          protected_frozen_tex=len(frozen_manuscript_inventory()),stages=records)
        dump(out/'SUMMARY.json',summary)
        dump(outbase/'LATEST.json',dict(directory=out.name,summary_sha256=sha(out/'SUMMARY.json')))
        print('ALGORITHM_INDEPENDENT_REPRODUCTION_PASS '+str(out),flush=True)


if __name__=='__main__':main()
