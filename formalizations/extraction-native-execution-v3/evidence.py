"""Portable native-v3 evidence verification; no Lean, no trusted import shortcut."""
from pathlib import Path
import argparse,re
import common as c

def lines(path,empty=False):
    raw=Path(path).read_text()
    if empty and raw=='\n':return []
    if not raw.endswith('\n'):raise ValueError('Noncanonical line file')
    names=raw[:-1].split('\n')
    if any(not n for n in names)or len(names)!=len(set(names)):raise ValueError('Empty/duplicate names')
    return names

def verify(out,commit=None,run_id=None,attempt=None):
    out=Path(out);s,b=c.binding()
    if c.readj(out/'EVIDENCE_HASHES.json')!=c.file_manifest(out):raise ValueError('Downloaded bytes differ')
    for n in ['SCOPE.json','BINDING.json','SOURCE_HASHES.json','IMPORT_CLOSURE_HASHES.json','PROTECTED_OLD_INPUTS.json','CI_POLICY.json','R2_FRESH_RECEIPT.json','Driver.lean']:
        if (out/n).read_bytes()!=(c.ROOT/n).read_bytes():raise ValueError('Export differs from frozen v3 recipe '+n)
    summary=c.readj(out/'SUMMARY.json');pre=c.readj(out/'PRE_AUDIT.json');post=c.readj(out/'POST_AUDIT.json');stages=c.readj(out/'STAGES.json')
    if pre!=post or pre['source_inputs']!=c.readj(c.ROOT/'SOURCE_HASHES.json')or pre['protected_inputs']!=c.readj(c.ROOT/'PROTECTED_OLD_INPUTS.json')['files']:raise ValueError('Source/execution/protected drift')
    if pre['sdk_inputs']!=c.readj(c.ROOT/'SDK_INPUTS.json'):raise ValueError('Native SDK archive/source pins differ')
    policy=c.readj(c.ROOT/'CI_POLICY.json');executables=pre['actual_executables']
    if type(executables)is not dict or set(executables)!=set(policy['binary_sha256']):raise ValueError('Executable records must be typed objects')
    for n,want in policy['binary_sha256'].items():
        row=executables[n]
        if type(row)is not dict or set(row)!={'path','sha256'}or type(row['path'])is not str or not row['path'].startswith('/')or row['sha256']!=want:raise ValueError('Invalid executable pin')
    deps={x['name']:x['rev']for x in c.readj(c.ROOT/'lake-manifest.json')['packages']if x['type']=='git'}
    if type(pre['dependencies'])is not dict or set(pre['dependencies'])!=set(deps):raise ValueError('Missing dependency pin')
    for n,h in deps.items():
        row=pre['dependencies'][n]
        if type(row)is not dict or set(row)!={'rev','path'}or row['rev']!=h or type(row['path'])is not str or not row['path'].startswith('/'):raise ValueError('Wrong dependency object')
    hosted=summary['mode']=='HOSTED_FRESH_MATHEMATICS'
    if summary['mode']not in ['HOSTED_FRESH_MATHEMATICS','LOCAL_REUSED_INDEPENDENT_R2_FULL_FRESH']or summary['status']!='PASS'or summary['execution_recipe']!='native-v3'or summary['kernel_trust']!=0 or summary['memory_bytes']!=4194304000 or summary['source_commit']!=s['source_commit']or summary['source_manifest_sha256']!=b['source_manifest_sha256']or summary['data_only_import_is_not_replay']is not True:raise ValueError('Not complete native-v3 trust-zero evidence')
    expected=[]
    if hosted:expected.append(('fresh-mathematics',['lake','build','ConcreteNativeExtraction.AssembledProgram']))
    expected += [('compile-driver',['lean','-j1','-M4000','-o','@EVIDENCE@/native/Driver.olean','-c','@EVIDENCE@/native/Driver.c','Driver.lean']),('link-driver',['leanc','-O2','-o','@EVIDENCE@/native/audit-driver','@EVIDENCE@/native/Driver.c'])]
    base=['lake','env','@EVIDENCE@/native/audit-driver']
    expected += [('types',base+['types','@EVIDENCE@']),('positive',base+['positive','@EVIDENCE@'])]
    expected += [('control-'+str(i),base+['control',str(i),'@EVIDENCE@'])for i in range(1,len(s['controls'])+1)]
    if [(r['stage'],r['command'])for r in stages]!=expected:raise ValueError('Incomplete/changed native execution plan')
    for row in stages:
        if row['exit_code']!=0 or c.sha(c.path_at(out,row['log']))!=row['sha256']:raise ValueError('Failed/unbound native stage')
        actual=[x.replace('@EVIDENCE@',summary['producer_output'])for x in row['command']];actual[0]=executables[actual[0]]['path']
        if row['actual_command']!=actual:raise ValueError('Actual command differs from bound tools/arguments')
    native_stages=[r for r in stages if r['stage']in ['types','positive']or r['stage'].startswith('control-')]
    for row in native_stages:
        log=(out/row['log']).read_text()
        if log.count('NATIVE_MAX_MEMORY_BYTES 4194304000')!=1 or log.count('DATA_ONLY_IMPORT_COMPLETE_NOT_KERNEL_REPLAY')!=1:raise ValueError('Missing actual native memory/import markers')
    binary=c.readj(out/'NATIVE_BINARY.json');bp=c.path_at(out,binary['file'])
    if binary['file']!='native/audit-driver'or binary['sha256']!=c.sha(bp)or binary['sha256']!=summary['native_binary_sha256']or binary['source_sha256']!=c.sha(c.ROOT/'Driver.lean')or binary['c_sha256']!=c.sha(out/'native/Driver.c')or binary['bytes']!=bp.stat().st_size or binary['memory_bytes']!=4194304000:raise ValueError('Native binary/source/cap mismatch')
    if bp.read_bytes()[:4]!=b'\x7fELF':raise ValueError('Not an actual native ELF')
    ax=c.readj(out/'AXIOM_REPORT.json')
    if type(ax)is not dict or set(ax)!=set(s['theorems']+s['models'])or any(type(v)is not list or len(v)!=len(set(v))or set(v)-c.ALLOW for v in ax.values()):raise ValueError('Wrong actual per-root axiom report')
    typ=(out/'types.log').read_text()
    if typ.count(f"DECLARATION_KIND_CHECK_PASS {len(s['theorems'])} theorems; {len(s['models'])} definitions")!=1 or typ.count(f"ACTUAL_MODEL_CORE_EXPR_EXPORT_PASS {len(s['models'])} models")!=1 or typ.count(f"ACTUAL_TYPE_AXIOM_REPORT_PASS {len(s['theorems']+s['models'])} roots")!=1:raise ValueError('Missing full kinds/types/model/axiom stage')
    for filename,key,folder in [('ROOT_TYPES.json',s['theorems']+s['models'],'root-types'),('MODEL_BODIES.json',s['models'],'models')]:
        rows=c.readj(out/filename)
        if type(rows)is not list or [r['name']for r in rows]!=key:raise ValueError('Wrong exported Core Expr roots')
        for i,row in enumerate(rows,1):
            p=out/folder/f'{i}.expr'
            if row!={'name':key[i-1],'file':f'{folder}/{i}.expr','sha256':c.sha(p)}:raise ValueError('Core Expr hash mismatch')
            text=p.read_text()
            if not text.startswith('name '+row['name']+'\nlevels ')or '\ntype 'not in text or folder=='models'and not ('\nvalue 'in text or '\ninductive 'in text and '\nconstructor name 'in text):raise ValueError('Missing full type/value/inductive constructor data')
    if lines(out/'kernel-roots.txt')!=s['theorems']+s['models']:raise ValueError('Wrong positive replay roots')
    closure=lines(out/'kernel-closure.txt');axioms=lines(out/'kernel-axioms.txt',True);positive=(out/'positive.log').read_text()
    if len(closure)!=summary['kernel_declarations']or not set(s['theorems']+s['models'])<=set(closure)or set(axioms)-c.ALLOW or positive.count(f"EMPTY_KERNEL_REPLAY_PASS {len(closure)} declarations; {len(s['theorems']+s['models'])} roots; trust level zero")!=1:raise ValueError('Missing actual complete positive empty-kernel replay')
    for i,name in enumerate(s['controls'],1):
        log=(out/f'control-{i}.log').read_text();deps=lines(out/f'control-{i}-type-dependencies.txt')
        if lines(out/f'control-{i}-roots.txt')!=[name]or set(lines(out/f'control-{i}-axioms.txt',True))-c.ALLOW or name in deps or 'True.intro'not in deps:raise ValueError('Wrong forged root/type dependencies')
        if log.count('TYPE_CLOSURE_REPLAY_PASS')!=1 or f'TYPE_CLOSURE_REPLAY_PASS {len(deps)} declarations; trust level zero'not in log or log.count('EXPECTED_KERNEL_REJECTION:')!=1 or f"while replaying declaration '{name}'"not in log or '(kernel) declaration type mismatch'not in log or log.count(f'CORRUPTED_PROOF_TYPE_MISMATCH_REJECTED {name}')!=1 or log.count(f'CORRUPTED_PROOF_REJECTED {name}')!=1:raise ValueError('Wrong exact same-type rejection')
    owned=c.readj(out/'MATHEMATICAL_OLEANS.json')
    if type(owned)is not dict or set(owned)!=c.expected_owned_outputs()or len(owned)!=427 or any(type(h)is not str or not re.fullmatch('[a-f0-9]{64}',h)for h in owned.values()):raise ValueError('Wrong actual mathematical build receipts')
    old=c.readj(c.ROOT/'R2_FRESH_RECEIPT.json')['owned_oleans']
    if hosted:
        if pre['reused_r2_oleans']is not None or summary['r2_reuse_count']!=0:raise ValueError('Hosted audit did not build independently')
    elif pre['reused_r2_oleans']!=old or summary['r2_reuse_count']!=430 or any(old[n]!=h for n,h in owned.items()):raise ValueError('Local reuse is not the independent full-fresh r2 build')
    if commit is not None:
        ctx=c.readj(out/'CI_CONTEXT.json')
        if not hosted or ctx!={'commit':commit,'run_id':str(run_id),'run_attempt':str(attempt),'repository':'mxym/math','workflow':'.github/workflows/extraction-native-execution-v3.yml'}or c.git('rev-parse','HEAD').decode().strip()!=commit:raise ValueError('Wrong downloaded CI identity')
    return {'status':'NATIVE_V3_ARTIFACT_PASS','theorems':33,'models':53,'controls':33,'kernel_declarations':len(closure),'mode':summary['mode'],'memory_bytes':4194304000}

def downloaded(directory):
    root=Path(directory)
    if not(root/'LATEST.json').exists():return root
    latest=c.readj(root/'LATEST.json');name=latest['directory']
    if type(name)is not str or not re.fullmatch('native-execution-v3-[0-9]{8}T[0-9]{12}Z',name)or {p.name for p in root.iterdir()}!={'LATEST.json',name}:raise ValueError('Wrong downloaded wrapper')
    out=c.path_at(root,name)
    if latest['summary_sha256']!=c.sha(out/'SUMMARY.json'):raise ValueError('Wrong latest summary')
    return out

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('directory');p.add_argument('--expected-commit');p.add_argument('--run-id');p.add_argument('--run-attempt');a=p.parse_args();print(verify(downloaded(a.directory),a.expected_commit,a.run_id,a.run_attempt))
