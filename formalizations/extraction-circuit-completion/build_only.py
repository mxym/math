from pathlib import Path
import argparse,datetime,hashlib,importlib.util,json,os,re,subprocess,sys
BASE=Path(__file__).resolve().parent
PIN='d13f23b723b8a846827a245b89c10fc7d3f11612'
def inputs():
    return sorted([*BASE.glob('CircuitCompletion/*.lean'),BASE/'CircuitCompletion.lean',BASE/'Check.lean',
        BASE/'ROOTS.txt',BASE/'lean-toolchain',BASE/'lakefile.toml',BASE/'lake-manifest.json',
        BASE/'README.md',BASE/'SOURCE_REVIEW.md',BASE/'build_only.py',BASE/'.gitignore'])
def source_manifest():
    result={str(p.relative_to(BASE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs()}
    payload=json.dumps(result,sort_keys=True,separators=(',',':')).encode()
    return {'files':result,'tree_sha256':hashlib.sha256(payload).hexdigest()}
def check_source():
    expected=json.loads((BASE/'SOURCE_SHA256.json').read_text())
    if source_manifest()!=expected: raise SystemExit('Source binding mismatch; freeze and record reviewed inputs first.')
    for p in [*BASE.glob('CircuitCompletion/*.lean'),BASE/'CircuitCompletion.lean',BASE/'Check.lean']:
        if re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',p.read_text()):
            raise SystemExit('Disallowed proof escape in '+str(p))
    return expected
parser=argparse.ArgumentParser()
parser.add_argument('--check-only',action='store_true')
parser.add_argument('--record-inputs',action='store_true')
parser.add_argument('--build',action='store_true')
args=parser.parse_args()
if args.record_inputs:
    (BASE/'SOURCE_SHA256.json').write_text(json.dumps(source_manifest(),indent=2,sort_keys=True)+'\n')
    print('RECORDED',source_manifest()['tree_sha256'])
    raise SystemExit(0)
binding=check_source()
print('SOURCE_INPUTS_OK',len(binding['files']),binding['tree_sha256'],flush=True)
if not args.build: raise SystemExit(0)
env=dict(os.environ)
guard=Path('/mnt/d/math/tmp/extraction-full-lean-20261016/ensure_d_storage.py')
if guard.exists():
    spec=importlib.util.spec_from_file_location('circuit_d_storage_guard',guard)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    env=module.configure_env(env)
elan=Path('/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin')
if elan.exists():env['PATH']=str(elan)+os.pathsep+env.get('PATH','')
mathlib=(BASE/'.lake/packages/mathlib').resolve()
actual=subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],env=env,text=True).strip()
if actual!=PIN:raise SystemExit('Mathlib pin mismatch: '+actual)
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
out=BASE/'verification'/('build-only-'+stamp);out.mkdir(parents=True,exist_ok=False)
summary={'status':'BUILD_ONLY','fresh_empty_kernel_replay':False,'forged_proof_controls':False,
    'source_tree_sha256':binding['tree_sha256'],'input_count':len(binding['files']),
    'root_count':len((BASE/'ROOTS.txt').read_text().splitlines()),'mathlib':actual,'logs':{}}
for key,cmd in [('lake_build',['lake','build']),('root_types_axioms',['lake','env','lean','Check.lean'])]:
    log=out/(key+'.log')
    with log.open('w') as f:r=subprocess.run(cmd,cwd=BASE,env=env,stdout=f,stderr=subprocess.STDOUT)
    summary['logs'][key]={'exit_code':r.returncode,'sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
    print(key,'exit',r.returncode,'log',log,flush=True)
    if r.returncode:summary['status']='BUILD_FAILED';break
if summary['status']=='BUILD_ONLY':
    text=(out/'root_types_axioms.log').read_text()
    axiom_lines=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.S)
    found=set()
    for _,items in axiom_lines:found.update(x.strip().split('.{',1)[0] for x in items.split(',') if x.strip())
    summary['ordinary_printed_axioms']=sorted(found)
    empty_reports=re.findall(r"'([^']+)' does not depend on any axioms",text)
    reported={name for name,_ in axiom_lines}|set(empty_reports)
    expected_roots=set((BASE/'ROOTS.txt').read_text().splitlines())
    summary['printed_root_report_count']=len(reported)
    if reported!=expected_roots:summary['status']='ROOT_REPORT_FAILED'
    allowed={'propext','Classical.choice','Quot.sound'}
    if not found or not found<=allowed:summary['status']='AXIOM_REPORT_FAILED'
(out/'SUMMARY.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
print(json.dumps(summary,indent=2,sort_keys=True),flush=True)
raise SystemExit(0 if summary['status']=='BUILD_ONLY' else 1)
