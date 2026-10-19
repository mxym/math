"""V3 reader fixtures only. No mathematical verification occurs here."""
from pathlib import Path
import tempfile,shutil,os
import common as c
import evidence as e

def fixture(out):
    s,b=c.binding();out.mkdir()
    for n in ['native','root-types','models']:(out/n).mkdir()
    for n in ['SCOPE.json','BINDING.json','SOURCE_HASHES.json','IMPORT_CLOSURE_HASHES.json','PROTECTED_OLD_INPUTS.json','CI_POLICY.json','R2_FRESH_RECEIPT.json','Driver.lean']:(out/n).write_bytes((c.ROOT/n).read_bytes())
    policy=c.readj(c.ROOT/'CI_POLICY.json');exe={n:{'path':'/fixture/'+n,'sha256':h}for n,h in policy['binary_sha256'].items()}
    deps={x['name']:{'rev':x['rev'],'path':'/fixture/'+x['name']}for x in c.readj(c.ROOT/'lake-manifest.json')['packages']if x['type']=='git'}
    old=c.readj(c.ROOT/'R2_FRESH_RECEIPT.json')['owned_oleans']
    snap={'source_commit':s['source_commit'],'source_inputs':c.readj(c.ROOT/'SOURCE_HASHES.json'),'protected_inputs':c.readj(c.ROOT/'PROTECTED_OLD_INPUTS.json')['files'],'actual_executables':exe,'dependencies':deps,'sdk_inputs':c.readj(c.ROOT/'SDK_INPUTS.json'),'reused_r2_oleans':old}
    c.dump(out/'PRE_AUDIT.json',snap);c.dump(out/'POST_AUDIT.json',snap)
    selected=s['theorems']+s['models'];marker='NATIVE_MAX_MEMORY_BYTES 4194304000\nDATA_ONLY_IMPORT_COMPLETE_NOT_KERNEL_REPLAY\n'
    (out/'types.log').write_text(marker+f"DECLARATION_KIND_CHECK_PASS {len(s['theorems'])} theorems; {len(s['models'])} definitions\nACTUAL_MODEL_CORE_EXPR_EXPORT_PASS {len(s['models'])} models\nACTUAL_TYPE_AXIOM_REPORT_PASS {len(selected)} roots\n")
    c.dump(out/'AXIOM_REPORT.json',{n:[]for n in selected})
    for filename,names,folder in [('ROOT_TYPES.json',selected,'root-types'),('MODEL_BODIES.json',s['models'],'models')]:
        rows=[]
        for i,n in enumerate(names,1):
            p=out/folder/f'{i}.expr';p.write_text('name '+n+'\nlevels []\ntype fixture\n'+('value fixture\n'if folder=='models'else''));rows.append({'name':n,'file':f'{folder}/{i}.expr','sha256':c.sha(p)})
        c.dump(out/filename,rows)
    closure=selected+['True.intro'];(out/'kernel-roots.txt').write_text('\n'.join(selected)+'\n');(out/'kernel-closure.txt').write_text('\n'.join(closure)+'\n');(out/'kernel-axioms.txt').write_text('\n')
    (out/'positive.log').write_text(marker+f'EMPTY_KERNEL_REPLAY_PASS {len(closure)} declarations; {len(selected)} roots; trust level zero\n')
    for i,n in enumerate(s['controls'],1):
        (out/f'control-{i}-roots.txt').write_text(n+'\n');(out/f'control-{i}-type-dependencies.txt').write_text('True.intro\n');(out/f'control-{i}-axioms.txt').write_text('\n')
        (out/f'control-{i}.log').write_text(marker+f"TYPE_CLOSURE_REPLAY_PASS 1 declarations; trust level zero\nEXPECTED_KERNEL_REJECTION: while replaying declaration '{n}': (kernel) declaration type mismatch\nCORRUPTED_PROOF_REJECTED {n}\nCORRUPTED_PROOF_TYPE_MISMATCH_REJECTED {n}\n")
    (out/'native/audit-driver').write_bytes(b'\x7fELFfixture-only-never-executed');(out/'native/Driver.c').write_text('fixture');c.dump(out/'NATIVE_BINARY.json',{'file':'native/audit-driver','sha256':c.sha(out/'native/audit-driver'),'bytes':(out/'native/audit-driver').stat().st_size,'c_sha256':c.sha(out/'native/Driver.c'),'source_sha256':c.sha(c.ROOT/'Driver.lean'),'memory_bytes':4194304000})
    base=['lake','env','@EVIDENCE@/native/audit-driver'];commands=[('compile-driver',['lean','-j1','-M4000','-o','@EVIDENCE@/native/Driver.olean','-c','@EVIDENCE@/native/Driver.c','Driver.lean']),('link-driver',['leanc','-O2','-o','@EVIDENCE@/native/audit-driver','@EVIDENCE@/native/Driver.c']),('types',base+['types','@EVIDENCE@']),('positive',base+['positive','@EVIDENCE@'])]+[('control-'+str(i),base+['control',str(i),'@EVIDENCE@'])for i in range(1,len(s['controls'])+1)]
    stages=[]
    for n,cmd in commands:
        if not(out/(n+'.log')).exists():(out/(n+'.log')).write_text('fixture-only\n')
        actual=[x.replace('@EVIDENCE@',str(out.resolve()))for x in cmd];actual[0]=exe[actual[0]]['path'];stages.append({'stage':n,'command':cmd,'actual_command':actual,'exit_code':0,'log':n+'.log','sha256':c.sha(out/(n+'.log'))})
    c.dump(out/'STAGES.json',stages);c.dump(out/'MATHEMATICAL_OLEANS.json',{n:old[n]for n in c.expected_owned_outputs()})
    c.dump(out/'SUMMARY.json',{'status':'PASS','execution_recipe':'native-v3','mode':'LOCAL_REUSED_INDEPENDENT_R2_FULL_FRESH','source_commit':s['source_commit'],'source_manifest_sha256':b['source_manifest_sha256'],'kernel_trust':0,'memory_bytes':4194304000,'data_only_import_is_not_replay':True,'producer_output':str(out.resolve()),'native_binary_sha256':c.sha(out/'native/audit-driver'),'kernel_declarations':len(closure),'r2_reuse_count':430})
    seal(out)
def seal(out):
    rows=c.readj(out/'STAGES.json')
    for row in rows:row['sha256']=c.sha(out/row['log'])
    c.dump(out/'STAGES.json',rows);c.dump(out/'EVIDENCE_HASHES.json',c.file_manifest(out))
def main():
    passed=[]
    with tempfile.TemporaryDirectory(dir=os.environ.get('TMPDIR','/mnt/lean-research-d/tmp'),prefix='native-v3-reader-')as tmp:
        out=Path(tmp)/'fixture';fixture(out);e.verify(out);passed.append('positive_empty_axioms_object_pins_and_independent_r2_reuse')
        def change(n,fn):d=c.readj(out/n);fn(d);c.dump(out/n,d)
        def reject(n,fn):
            fn();seal(out)
            try:e.verify(out)
            except (ValueError,KeyError,TypeError,FileNotFoundError):passed.append(n)
            else:raise ValueError('Accepted regression '+n)
            shutil.rmtree(out);fixture(out)
        reject('string_executables',lambda:[change(f,lambda d:d.update(actual_executables='legacy string'))for f in ['PRE_AUDIT.json','POST_AUDIT.json']])
        reject('missing_control_stage',lambda:change('STAGES.json',lambda d:d.pop()))
        reject('changed_memory_cap',lambda:change('STAGES.json',lambda d:d[0]['command'].__setitem__(2,'-M8000')))
        reject('missing_native_cap_marker',lambda:(out/'types.log').write_text((out/'types.log').read_text().replace('4194304000','8388608000')))
        reject('load_only_is_not_positive_replay',lambda:(out/'positive.log').write_text('NATIVE_MAX_MEMORY_BYTES 4194304000\nDATA_ONLY_IMPORT_COMPLETE_NOT_KERNEL_REPLAY\n'))
        reject('unexpected_axiom',lambda:(out/'kernel-axioms.txt').write_text('sorryAx\n'))
        reject('forged_wrong_root',lambda:(out/'control-1-roots.txt').write_text('Wrong.root\n'))
        reject('wrong_kernel_rejection_reason',lambda:(out/'control-1.log').write_text((out/'control-1.log').read_text().replace('(kernel) declaration type mismatch','memory exception')))
        reject('missing_positive_type_dependencies',lambda:(out/'control-1.log').write_text((out/'control-1.log').read_text().replace('TYPE_CLOSURE_REPLAY_PASS','absent')))
        reject('changed_model_body',lambda:(out/'models/1.expr').write_text('tampered\n'))
        reject('changed_actual_root_type',lambda:(out/'root-types/1.expr').write_text('tampered\n'))
        reject('changed_binary_bytes',lambda:(out/'native/audit-driver').write_bytes(b'changed'))
        reject('missing_math_receipt',lambda:change('MATHEMATICAL_OLEANS.json',lambda d:d.pop(next(iter(d)))))
        reject('author_cache_substitution',lambda:change('MATHEMATICAL_OLEANS.json',lambda d:d.__setitem__(next(iter(d)),'f'*64)))
        reject('post_source_drift',lambda:change('POST_AUDIT.json',lambda d:d.update(source_commit='0'*40)))
        reject('duplicate_json_key',lambda:(out/'SUMMARY.json').write_text('{"status":"PASS","status":"PASS"}'))
        (out/'nested').mkdir();(out/'nested/EVIDENCE_HASHES.json').write_text('{}')
        try:e.verify(out)
        except ValueError:passed.append('unsealed_nested_same_basename_manifest')
        else:raise ValueError('Accepted nested unsealed manifest')
        if 'EVIDENCE_HASHES.json'in c.file_manifest(out)or 'nested/EVIDENCE_HASHES.json'not in c.file_manifest(out):raise ValueError('Manifest boundary')
        passed.append('root_manifest_excluded_nested_manifest_included')
        for n in ['SOURCE_HASHES.json','BINDING.json','PREPARATION_RESULT.json']:
            if not c.root_metadata_file(c.ROOT/n)or c.root_metadata_file(c.ROOT/'nested'/n):raise ValueError('Metadata basename boundary')
        passed.append('root_metadata_excluded_nested_metadata_included')
        for bad in ['../outside','/absolute','a\\b','a/../b','a//b']:
            try:c.safe_relative(bad)
            except ValueError:passed.append('unsafe_path_'+bad)
            else:raise ValueError('Accepted unsafe path')
    print({'status':'NATIVE_V3_READER_SELFTEST_PASS','count':len(passed),'checks':passed,'kernel_run':False})
if __name__=='__main__':main()
