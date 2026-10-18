#!/usr/bin/env python3
"""Independent actual raw compiler and partial resource audit; all generated evidence has a new prefix.

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
NEW=['extraction-numerical-synthesis','extraction-effective-encoding','extraction-raw-resource-audit']

OLD=['extraction-matrix-projector','extraction-universal-orbit',
     'extraction-minimax-profile','appt-qutrit-purity',
     'extraction-connections','extraction-spectral-protocol',
     'spectral-extraction-core','appt-high-dimensional-review',
     'extraction-information-spectrum','appt-subunit-renyi',
     'extraction-symmetric-support','spectral-extraction-local-cap']


_FROZEN_ALGORITHM=None
def frozen_algorithm():
    global _FROZEN_ALGORITHM
    if _FROZEN_ALGORITHM is None:
        import importlib.util
        path=REPO/'formalizations/extraction-algorithm-audit/reproduce.py'
        spec=importlib.util.spec_from_file_location('frozen_algorithm_recipe_for_resource_protection',path)
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        _FROZEN_ALGORITHM=module
    return _FROZEN_ALGORITHM


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
    expected='import RawResourceAudit\nimport RawResourceVerification.ReplaySupport\n\nset_option pp.universes true\nset_option pp.explicit true\nset_option pp.fullNames true\n\nrun_cmd (RawResourceVerification.checkKinds [\n'+',\n'.join('  ``'+n for n in roots)+'\n] [\n'+',\n'.join('  ``'+n for n in defs)+'\n])\n\n'+''.join('#check '+n+'\nset_option pp.universes false in #print axioms '+n+'\n' for n in roots+defs)
    if (ROOT/'Check.lean').read_text()!=expected:raise RuntimeError('Check.lean scope drift')
    audit='import RawResourceAudit\nimport RawResourceVerification.ReplaySupport\n\nrun_cmd (RawResourceVerification.replayAll [\n'+',\n'.join('  ``'+n for n in roots+defs)+'\n] "verification/raw-resource-kernel")\n\n'+''.join('run_cmd RawResourceVerification.rejectCorruptTheorem ``'+n+' "verification/raw-resource-control-'+str(i+1)+'"\n' for i,n in enumerate(controls))
    if (ROOT/'Audit.lean').read_text()!=audit:raise RuntimeError('Audit.lean scope drift')
    declaration_map()
    manuscript_map()
    policy=readj(ROOT/'CI_EXECUTION_POLICY.json')['expected_scope']
    if policy!=dict(endpoint_theorems=len(roots),model_definitions=len(defs),same_type_controls=len(controls)):raise RuntimeError('CI policy/list disagreement')
    plan=readj(ROOT/'CONTROL_PLAN.json')
    if [(row['index'],row['theorem'])for row in plan]!=list(enumerate(controls,1)):raise RuntimeError('Exact strict-control plan disagreement')
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
    # This profile audits a resource package, not a new manuscript revision.
    claims=readj(ROOT/'CLAIMS.json');scope=readj(ROOT/'SCOPE.json')
    roots={name for group in scope['groups']for name in group['theorem_roots']}
    if claims['source_head']!=scope['source_head']or any(not set(group['roots'])<=roots for group in claims['claim_groups']):raise RuntimeError('Resource claim/source disagreement')
    return claims['claim_groups']


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
    return frozen_algorithm().frozen_manuscript_inventory()


def validate_source_head(s,inputs):
    for name in inputs:
        if name.startswith(ROOT.relative_to(REPO).as_posix()+'/'):continue
        original=subprocess.check_output(['git','show',s['source_head']+':'+name],cwd=REPO)
        if original!=(REPO/name).read_bytes():raise RuntimeError('Source differs from frozen mathematical/manuscript head '+name)


def claim_snapshots():
    manifest=readj(ROOT/'CLAIM_SNAPSHOTS.json');scope=readj(ROOT/'SCOPE.json')
    if manifest['source_head']!=scope['source_head']:raise RuntimeError('Claim snapshot source differs')
    names=set()
    for row in manifest['snapshots']:
        relative=Path(row['snapshot']);source=Path(row['original_repo_path']);path=ROOT/relative
        if relative.is_absolute()or relative.parts[0]!='claims'or '..'in relative.parts or relative.as_posix()in names or path.is_symlink()or not path.resolve().is_relative_to((ROOT/'claims').resolve()):raise RuntimeError('Unsafe/duplicate claim snapshot')
        if source.is_absolute()or '..'in source.parts or row['source_commit']!=scope['source_head']:raise RuntimeError('Wrong original claim provenance')
        names.add(relative.as_posix())
        original=subprocess.check_output(['git','show',row['source_commit']+':'+row['original_repo_path']],cwd=REPO)
        blob=run('git','rev-parse',row['source_commit']+':'+row['original_repo_path'])
        if path.read_bytes()!=original or sha(path)!=row['sha256']or blob!=row['git_blob']:raise RuntimeError('Claim snapshot differs from exact source Git blob')
    if {path.relative_to(ROOT).as_posix()for path in (ROOT/'claims').rglob('*')if path.is_file()}!=names:raise RuntimeError('Missing/extra claim snapshot')
    return manifest


def inventory():
    packages=package_roots();scope=readj(ROOT/'SCOPE.json');claim_snapshots()
    owned={p for p in ROOT.rglob('*')if p.is_file()and not any(c in {'.lake','verification','__pycache__'}for c in p.relative_to(ROOT).parts)and p.name not in {'SOURCE_HASHES.json','PROTECTED_INPUTS.json'}}
    selected=set(owned);todo=[ROOT/'RawResourceAudit.lean',ROOT/'RawResourceVerification/ReplaySupport.lean'];seen=set()
    for relative in scope['supporting_documents']:
        path=REPO/relative
        if not path.resolve().is_relative_to(REPO.resolve())or not path.is_file():raise RuntimeError('Missing/outside supporting input '+relative)
        selected.add(path)
    for relative in ['formalizations/extraction-algorithm-audit/SOURCE_HASHES.json','formalizations/extraction-algorithm-audit/FROZEN_OLD_INPUTS.json','formalizations/extraction-algorithm-execution-v2/EXECUTION_HASHES.json']:
        selected.add(REPO/relative)
    while todo:
        path=todo.pop()
        if path in seen:continue
        seen.add(path);raw=source_without_comments(path.read_text())
        if not path.resolve().is_relative_to(ROOT.resolve())and re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',raw):raise RuntimeError('Forbidden mathematical proof token '+str(path))
        for line in re.findall(r'^import\s+([^\n]+)',raw,re.M):
            for module in line.split():
                if module in {'Lean','Mathlib'}or module.startswith(('Mathlib.','Lean.','Batteries.','Aesop.','Qq.')):continue
                found=[q/(module.replace('.','/')+'.lean')for q in packages];found=[q for q in found if q.is_file()]
                if len(found)!=1:raise RuntimeError('Missing/nonunique import '+module)
                selected.add(found[0]);todo.append(found[0])
    closure=readj(ROOT/'IMPORT_CLOSURE_HASHES.json')
    actual_closure={q.relative_to(REPO).as_posix():sha(q)for q in seen if not q.resolve().is_relative_to(ROOT.resolve())}
    if actual_closure!=closure:raise RuntimeError('Explicit actual import closure changed')
    expected=set(scope['explicit_new_math_files'])
    if not expected<={q.relative_to(REPO).as_posix()for q in seen}:raise RuntimeError('Selected new mathematical source is not imported')
    for package in packages:
        for name in ['lakefile.toml','lakefile.lean','lake-manifest.json','lean-toolchain']:
            if (package/name).is_file():selected.add(package/name)
    if any(path.is_symlink()for path in selected):raise RuntimeError('Symlinked bound input')
    return {path.relative_to(REPO).as_posix():sha(path)for path in sorted(selected)}


def old_inventory():
    original=frozen_algorithm()
    prefix=REPO/'formalizations/extraction-algorithm-audit'
    if sha(prefix/'SOURCE_HASHES.json')!='8b99b7d144b8c27a4092028f557a47bf01fb38d0ded6eef543a4abd612e51386':raise RuntimeError('Original algorithm source binding changed')
    algorithm=original.readj(prefix/'SOURCE_HASHES.json')
    if len(algorithm)!=340 or original.inventory()!=algorithm:raise RuntimeError('Original 340 inputs changed')
    earlier=original.old_inventory()
    v2=REPO/'formalizations/extraction-algorithm-execution-v2'
    if sha(v2/'EXECUTION_HASHES.json')!='b3ff2c6d50d6397884144e6692e9f196ceaf937a8b7cd0cb6d513eb0fa31b787':raise RuntimeError('Frozen execution-v2 binding changed')
    execution=readj(v2/'EXECUTION_HASHES.json')
    for name,digest in execution['execution_inputs'].items():
        if sha(REPO/name)!=digest:raise RuntimeError('Frozen execution-v2 input changed '+name)
    workflow=REPO/execution['actual_workflow']['path']
    if sha(workflow)!=execution['actual_workflow']['template_sha256']:raise RuntimeError('Installed old execution-v2 workflow changed')
    evidence={}
    commit='13fecc54661d56e57647a27fce5f30d0f43fa57a'
    paths=run('git','diff-tree','--no-commit-id','--name-only','-r',commit).splitlines()
    for name in paths:
        if not name.startswith('formalizations/extraction-algorithm-audit/verification/'):raise RuntimeError('Unexpected old seal input')
        raw=subprocess.check_output(['git','show',commit+':'+name],cwd=REPO)
        if (REPO/name).read_bytes()!=raw:raise RuntimeError('Original sealed algorithm evidence changed '+name)
        evidence[name]=hashlib.sha256(raw).hexdigest()
    if len(evidence)!=35:raise RuntimeError('Old algorithm evidence inventory changed')
    return dict(earlier=earlier,algorithm_340=algorithm,algorithm_manifest_sha256=sha(prefix/'SOURCE_HASHES.json'),algorithm_local_evidence=evidence,execution_v2_manifest=execution,execution_v2_manifest_sha256=sha(v2/'EXECUTION_HASHES.json'),installed_execution_v2_workflow_sha256=sha(workflow))


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


def check_binding(check_dependencies=True):
    scope,roots,definitions,controls=scope_lists()
    if scope['state']!='READY'or scope['pending_required']:raise RuntimeError('Scope is preliminary')
    if scope['source_head']!='04044ad0e1dc94634a8005f5f6abebe4518a012b':raise RuntimeError('Wrong fixed mathematical source')
    if inventory()!=readj(ROOT/'SOURCE_HASHES.json'):raise RuntimeError('Bound source/config changed')
    if old_inventory()!=readj(ROOT/'PROTECTED_INPUTS.json'):raise RuntimeError('Frozen prior scope/evidence changed')
    validate_source_head(scope,inventory())
    if check_dependencies:check_pins()
    return scope,roots,definitions,controls


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
        print(json.dumps(dict(status='PREFLIGHT_ONLY',source_head=s['source_head'],source_inputs=len(inventory()),protected_old_inputs=len(old['earlier']['older_4378']),protected_completion_inputs=len(old['earlier']['completion_605']),protected_algorithm_inputs=len(old['algorithm_340']),protected_frozen_tex=len(frozen_manuscript_inventory()),draft_tex_inputs=len(s['manuscript_inputs']),manuscript_documents=len(s['manuscript_documents']),verification_performed=False)))
        return
    if args.freeze_source:
        if s['state']!='READY' or s['pending_required']:raise RuntimeError('Refusing preliminary freeze')
        if (ROOT/'SOURCE_HASHES.json').exists():raise RuntimeError('Binding already exists; start a new audit revision')
        check_pins()
        old=old_inventory();inputs=inventory()
        validate_source_head(s,inputs)
        dump(ROOT/'PROTECTED_INPUTS.json',old)
        dump(ROOT/'SOURCE_HASHES.json',inputs)
        check_binding()
        print('SOURCE_BINDING_CREATED_NOT_VERIFICATION');return
    if args.types_only:
        check_pins();old_inventory();validate_source_head(s,inventory())
        preliminary_inputs=inventory()
    else:s,roots,defs,controls=check_binding()
    if args.check_only:print('SOURCE_BINDING_PASS');return
    if not args.types_only and not args.fresh:raise RuntimeError('Whole independent verification requires --fresh')
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    outbase=runtime['output'];outbase.mkdir(parents=True,exist_ok=True)
    out=outbase/('raw-resource-'+stamp);out.mkdir()
    records=[]
    dump(out/'EXECUTION.json',dict(execution_inputs=readj(ROOT/('CI_EXECUTION_POLICY.json' if args.github_actions else 'EXECUTION_INPUTS.json')),
      python=sys.version,guard=runtime['guard'],portable_binary_inputs=binary_inputs,
      runtime={k:str(v) for k,v in runtime.items() if k!='env'},
      environment={n:env.get(n) for n in ['TMPDIR','MATHLIB_CACHE_DIR','XDG_CACHE_HOME']}))
    def snapshot():
        return dict(source_head=s['source_head'],source_inputs=inventory(),protected_inputs=old_inventory(),execution_inputs=readj(ROOT/('CI_EXECUTION_POLICY.json'if args.github_actions else'EXECUTION_INPUTS.json')),binaries=runtime.get('actual_executables',binary_inputs))
    before=snapshot()
    dump(out/'PRE_AUDIT.json',before)
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
        stage('build-audit',['lake','build','RawResourceAudit','RawResourceVerification'],1800)
        types=stage('root-types-axioms',['lake','env','lean','-j1','-M'+str(min(10000,runtime['memory_mb'])),'Check.lean'],600)
        if types.count('DECLARATION_KIND_CHECK_PASS')!=1:raise RuntimeError('Missing declaration kind marker')
        dump(out/'AXIOM_REPORT.json',parse_axiom_report(types,roots+defs))
        bytecode=stage('finite-syntax-bytecode',['lake','env','lean','-j1','-M'+str(min(7000,runtime['memory_mb'])),'--run','ExecutableCheck.lean'],300)
        if bytecode.count('RAW_RESOURCE_SYNTAX_CHECK_PASS')!=1:raise RuntimeError('Missing actual finite syntax bytecode marker')
        if args.types_only:
            if inventory()!=preliminary_inputs:raise RuntimeError('Preliminary source/config drift')
            if binary_inputs!=check_execution_inputs(args.github_actions):raise RuntimeError('Preliminary execution binary drift')
            dump(out/'SUMMARY.json' ,dict(status='PRELIMINARY_KIND_TYPE_AXIOM_BYTECODE_PASS_NOT_KERNEL_REPLAY',source_head=s['source_head'],endpoint_theorems=len(roots),model_definitions=len(defs),control_candidates=len(controls),stages=records,source_inputs=inventory(),protected_inputs=old_inventory()))
            print('RAW_RESOURCE_PRELIMINARY_TYPES_PASS '+str(out),flush=True);return
        invocation=out/'AuditInvocation.lean' 
        invocation.write_text((ROOT/'Audit.lean').read_text().replace('\"verification/raw-resource-',json.dumps(str(out/'raw-resource-'))[:-1]))
        audit=stage('trust0-replay',['lake','env','lean','-j1','-M'+str(runtime['memory_mb']),str(invocation)],7200)
        if audit.count('EMPTY_KERNEL_REPLAY_PASS')!=1 or audit.count('CORRUPTED_PROOF_REJECTED')!=len(controls) or audit.count('TYPE_CLOSURE_REPLAY_PASS')!=len(controls) or audit.count('CORRUPTED_PROOF_TYPE_MISMATCH_REJECTED')!=len(controls):raise RuntimeError('Missing replay/control markers')
        from evidence import axiom_set
        axs=axiom_set(out/'raw-resource-kernel-axioms.txt')
        if not axs<=ALLOW:raise RuntimeError('Unexpected replay axiom')
        shutil.copy2(ROOT/'SOURCE_HASHES.json',out/'SOURCE_HASHES.json')
        shutil.copy2(ROOT/'SCOPE.json',out/'SCOPE.json')
        check_binding()
        if binary_inputs!=check_execution_inputs(args.github_actions):raise RuntimeError('Execution binary drift during audit')
        after=snapshot()
        if before!=after:raise RuntimeError('Source/protected/execution pre-post drift')
        dump(out/'POST_AUDIT.json',after)
        summary=dict(status='PASS',scope=s['scope_note'],mathematical_source_head=s['source_head'],
          source_inputs=len(inventory()),endpoint_theorems=len(roots),model_definitions=len(defs),
          same_type_forged_proof_controls=len(controls),kernel_trust=0,
          runtime_guard=runtime['guard'],audit_invocation_sha256=sha(invocation),
          kernel_declarations=int(re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations',audit).group(1)),
          axioms=sorted(axs),fresh_owned_build=args.fresh,fresh_packages=NEW if args.fresh else [],
          source_manifest_sha256=sha(ROOT/'SOURCE_HASHES.json'),
          resource_source_head=s['source_head'],resource_scope=s['scope_name'],new_math_modules=len(s['explicit_new_math_files']),
          protected_frozen_tex=len(frozen_manuscript_inventory()),stages=records)
        dump(out/'SUMMARY.json',summary)
        dump(outbase/'LATEST.json',dict(directory=out.name,summary_sha256=sha(out/'SUMMARY.json')))
        print('RAW_RESOURCE_INDEPENDENT_REPRODUCTION_PASS '+str(out),flush=True)


if __name__=='__main__':main()
