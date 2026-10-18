"""Portable strict reader for the native-execution artifact, independent of Lean."""
from pathlib import Path
import argparse,re
import common as c

def lines(path,empty=False):
    raw=Path(path).read_text(encoding='utf-8')
    if not raw.endswith('\n'):raise ValueError('Noncanonical line file')
    if empty and raw=='\n':return []
    xs=raw[:-1].split('\n')
    if any(not x for x in xs)or len(xs)!=len(set(xs)):raise ValueError('Empty/duplicate line')
    return xs

def executable_object(value):
    if type(value)is not dict or set(value)!={'lean','lake'}:raise ValueError('Executable records must be objects')
    for name,row in value.items():
        if type(row)is not dict or set(row)!={'path','sha256'}or type(row['path'])is not str or not row['path'].startswith('/')or row['sha256']!=c.readj(c.ROOT/'CI_POLICY.json')['binary_sha256'][name]:raise ValueError('Malformed pinned executable record')

def verify(out,commit=None,run_id=None,attempt=None):
    out=Path(out);s,b=c.binding();manifest=c.readj(out/'EVIDENCE_HASHES.json')
    if manifest!=c.file_manifest(out):raise ValueError('Artifact byte inventory differs')
    for n in ['SCOPE.json','BINDING.json','SOURCE_HASHES.json','IMPORT_CLOSURE_HASHES.json','PROTECTED_OLD_INPUTS.json','CI_POLICY.json']:
        if (out/n).read_bytes()!=(c.ROOT/n).read_bytes():raise ValueError('Export differs from bound recipe '+n)
    summary=c.readj(out/'SUMMARY.json');pre=c.readj(out/'PRE_AUDIT.json');post=c.readj(out/'POST_AUDIT.json');stages=c.readj(out/'STAGES.json')
    if pre!=post:raise ValueError('Source/executable/protected pre-post drift')
    executable_object(pre['actual_executables'])
    if pre['source_inputs']!=c.readj(c.ROOT/'SOURCE_HASHES.json')or pre['protected_inputs']!=c.readj(c.ROOT/'PROTECTED_OLD_INPUTS.json')['files']or pre['source_commit']!=s['source_commit']:raise ValueError('Wrong bound snapshot')
    if summary['status']!='PASS'or summary['kernel_trust']!=0 or summary['fresh_owned_build']is not True or summary['memory_mb']!=4000 or summary['source_commit']!=s['source_commit']or summary['source_manifest_sha256']!=b['source_manifest_sha256']:raise ValueError('Incomplete full fresh trust-zero run')
    expected=[('toolchain',['lake','env','lean','--version']),('build',['lake','build','NativeExecutionAudit','NativeExecutionVerification']),('types',['lake','env','lean','-j1','-M4000','@EVIDENCE@/CheckInvocation.lean']),('kernel',['lake','env','lean','-j1','-M4000','@EVIDENCE@/AuditInvocation.lean'])]
    if type(stages)is not list or [(x['stage'],x['command'])for x in stages]!=expected:raise ValueError('Missing/changed stage or memory cap')
    for rec in stages:
        if rec['exit_code']!=0 or rec['sha256']!=c.sha(c.path_at(out,rec['log'])):raise ValueError('Failed/unbound actual log')
    typ=(out/'types.log').read_text();kernel=(out/'kernel.log').read_text()
    kind=f"DECLARATION_KIND_CHECK_PASS {len(s['theorems'])} theorems; {len(s['models'])} definitions"
    modelmarker=f"ACTUAL_MODEL_CORE_EXPR_EXPORT_PASS {len(s['models'])} models"
    if typ.count('DECLARATION_KIND_CHECK_PASS')!=1 or kind not in typ or typ.count(modelmarker)!=1 or c.parse_axioms(typ,s['theorems']+s['models'])!=c.readj(out/'AXIOM_REPORT.json'):raise ValueError('Wrong kinds/types/axioms/model export evidence')
    for name in ['CheckInvocation.lean','AuditInvocation.lean']:
        template=(c.ROOT/name.replace('Invocation','')).read_text()
        actual=(out/name).read_text().replace(str(out.resolve()),'@EVIDENCE@')
        # Downloaded artifacts retain the original absolute producer path.
        actual=actual.replace(summary['producer_output'],'@EVIDENCE@')
        if actual!=template:raise ValueError('Generated invocation drift')
    if lines(out/'kernel-roots.txt')!=s['theorems']+s['models']:raise ValueError('Wrong positive roots')
    closure=lines(out/'kernel-closure.txt');axs=lines(out/'kernel-axioms.txt',empty=True)
    if set(axs)-c.ALLOW or len(closure)!=summary['kernel_declarations']or not set(s['theorems']+s['models'])<=set(closure):raise ValueError('Wrong replay closure/axioms')
    if kernel.count('EMPTY_KERNEL_REPLAY_PASS')!=1 or f"EMPTY_KERNEL_REPLAY_PASS {len(closure)} declarations; {len(s['theorems']+s['models'])} roots; trust level zero"not in kernel:raise ValueError('Missing whole closure positive replay')
    for marker in ['TYPE_CLOSURE_REPLAY_PASS','CORRUPTED_PROOF_REJECTED','CORRUPTED_PROOF_TYPE_MISMATCH_REJECTED','EXPECTED_KERNEL_REJECTION:']:
        if kernel.count(marker)!=len(s['controls']):raise ValueError('Wrong strict control count '+marker)
    for i,name in enumerate(s['controls'],1):
        stem=out/('control-'+str(i))
        if lines(str(stem)+'-roots.txt')!=[name]or set(lines(str(stem)+'-axioms.txt',True))-c.ALLOW:raise ValueError('Wrong control root/axioms')
        deps=lines(str(stem)+'-type-dependencies.txt')
        if name in deps or 'True.intro'not in deps or f'CORRUPTED_PROOF_TYPE_MISMATCH_REJECTED {name}'not in kernel or f"while replaying declaration '{name}'"not in kernel:raise ValueError('Control did not reject exact same-type forged root')
    bodies=c.readj(out/'MODEL_BODIES.json')
    if type(bodies)is not list or [x['name']for x in bodies]!=s['models']:raise ValueError('Wrong actual model bodies')
    for i,row in enumerate(bodies,1):
        p=out/'models'/f'{i}.expr';raw=p.read_text()
        if row!={'name':s['models'][i-1],'file':f'models/{i}.expr','sha256':c.sha(p)}or not raw.startswith('name '+row['name']+'\nlevels ')or '\ntype 'not in raw or not ('\nvalue 'in raw or '\ninductive 'in raw):raise ValueError('Missing actual Core Expr body/type binding')
    owned=c.readj(out/'OWNED_OLEANS.json')
    if not owned or any(not n.endswith('.olean')or type(h)is not str or not re.fullmatch('[a-f0-9]{64}',h)for n,h in owned.items()):raise ValueError('No independently fresh owned outputs')
    if summary['fresh_packages']!=[p.relative_to(c.REPO).as_posix()for p in c.package_roots()]:raise ValueError('Wrong fresh package scope')
    if commit is not None:
        ctx=c.readj(out/'CI_CONTEXT.json')
        if ctx['commit']!=commit or ctx['run_id']!=str(run_id)or ctx['run_attempt']!=str(attempt)or ctx['repository']!='mxym/math'or ctx['workflow']!='.github/workflows/extraction-native-execution.yml':raise ValueError('Artifact CI identity mismatch')
        if c.git('rev-parse','HEAD').decode().strip()!=commit:raise ValueError('Verifier checkout differs from event commit')
    return {'status':'NATIVE_EXECUTION_ARTIFACT_PASS','source_commit':s['source_commit'],'theorems':len(s['theorems']),'models':len(s['models']),'controls':len(s['controls']),'kernel_declarations':len(closure),'artifact_files':len(manifest)}

def downloaded_directory(directory):
    root=Path(directory)
    if not (root/'LATEST.json').exists():return root
    latest=c.readj(root/'LATEST.json');name=latest['directory']
    if type(name)is not str or not re.fullmatch('native-execution-[0-9]{8}T[0-9]{12}Z',name):raise ValueError('Invalid latest evidence directory')
    if {p.name for p in root.iterdir()}!={'LATEST.json',name}:raise ValueError('Unexpected outer artifact entries')
    out=c.path_at(root,name)
    if c.sha(out/'SUMMARY.json')!=latest['summary_sha256']:raise ValueError('Wrong latest summary binding')
    return out

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('directory');p.add_argument('--expected-commit');p.add_argument('--run-id');p.add_argument('--run-attempt');a=p.parse_args()
    print(verify(downloaded_directory(a.directory),a.expected_commit,a.run_id,a.run_attempt))
