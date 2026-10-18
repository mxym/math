"""Reader regression fixtures only; these never claim Lean verification."""
from pathlib import Path
import copy,tempfile
import common as c
import evidence as e

def fixture(out):
    s,b=c.binding();out.mkdir();(out/'models').mkdir()
    for n in ['SCOPE.json','BINDING.json','SOURCE_HASHES.json','IMPORT_CLOSURE_HASHES.json','PROTECTED_OLD_INPUTS.json','CI_POLICY.json']:(out/n).write_bytes((c.ROOT/n).read_bytes())
    executables={n:{'path':'/fixture/'+n,'sha256':v}for n,v in c.readj(c.ROOT/'CI_POLICY.json')['binary_sha256'].items()}
    snap={'source_commit':s['source_commit'],'source_inputs':c.readj(c.ROOT/'SOURCE_HASHES.json'),'protected_inputs':c.readj(c.ROOT/'PROTECTED_OLD_INPUTS.json')['files'],'actual_executables':executables,'dependencies':{}}
    c.dump(out/'PRE_AUDIT.json',snap);c.dump(out/'POST_AUDIT.json',snap)
    for n in ['Check','Audit']:(out/(n+'Invocation.lean')).write_text((c.ROOT/(n+'.lean')).read_text().replace('@EVIDENCE@',str(out.resolve())))
    selected=s['theorems']+s['models'];typ=f"DECLARATION_KIND_CHECK_PASS {len(s['theorems'])} theorems; {len(s['models'])} definitions\nACTUAL_MODEL_CORE_EXPR_EXPORT_PASS {len(s['models'])} models\n"+'\n'.join("'"+n+"' does not depend on any axioms"for n in selected)+'\n';(out/'types.log').write_text(typ);c.dump(out/'AXIOM_REPORT.json',{n:[]for n in selected})
    names=selected+['True.intro'];(out/'kernel-roots.txt').write_text('\n'.join(selected)+'\n');(out/'kernel-closure.txt').write_text('\n'.join(names)+'\n');(out/'kernel-axioms.txt').write_text('\n')
    kernel=f'EMPTY_KERNEL_REPLAY_PASS {len(names)} declarations; {len(selected)} roots; trust level zero\n'
    for i,n in enumerate(s['controls'],1):
        stem=out/f'control-{i}';Path(str(stem)+'-roots.txt').write_text(n+'\n');Path(str(stem)+'-type-dependencies.txt').write_text('True.intro\n');Path(str(stem)+'-axioms.txt').write_text('\n')
        kernel+=f"EXPECTED_KERNEL_REJECTION: (kernel) declaration type mismatch while replaying declaration '{n}'\nTYPE_CLOSURE_REPLAY_PASS 1 declarations; trust level zero\nCORRUPTED_PROOF_REJECTED {n}\nCORRUPTED_PROOF_TYPE_MISMATCH_REJECTED {n}\n"
    (out/'kernel.log').write_text(kernel);(out/'toolchain.log').write_text('fixture only\n');(out/'build.log').write_text('fixture only\n')
    bodies=[]
    for i,n in enumerate(s['models'],1):
        p=out/'models'/f'{i}.expr';p.write_text('name '+n+'\nlevels []\ntype fixture\nvalue fixture\n');bodies.append({'name':n,'file':f'models/{i}.expr','sha256':c.sha(p)})
    c.dump(out/'MODEL_BODIES.json',bodies);c.dump(out/'OWNED_OLEANS.json',{'fixture.olean':'a'*64})
    commands=[('toolchain',['lake','env','lean','--version']),('build',['lake','build','NativeExecutionAudit','NativeExecutionVerification']),('types',['lake','env','lean','-j1','-M4000','@EVIDENCE@/CheckInvocation.lean']),('kernel',['lake','env','lean','-j1','-M4000','@EVIDENCE@/AuditInvocation.lean'])]
    c.dump(out/'STAGES.json',[{'stage':n,'command':cmd,'exit_code':0,'log':n+'.log','sha256':c.sha(out/(n+'.log'))}for n,cmd in commands])
    c.dump(out/'SUMMARY.json',{'status':'PASS','kernel_trust':0,'fresh_owned_build':True,'memory_mb':4000,'source_commit':s['source_commit'],'source_manifest_sha256':b['source_manifest_sha256'],'producer_output':str(out.resolve()),'kernel_declarations':len(names),'fresh_packages':[p.relative_to(c.REPO).as_posix()for p in c.package_roots()]})
    seal(out)
def seal(out):
    stages=out/'STAGES.json'
    if stages.exists():
        rows=c.readj(stages)
        for row in rows:row['sha256']=c.sha(out/row['log'])
        c.dump(stages,rows)
    c.dump(out/'EVIDENCE_HASHES.json',c.file_manifest(out))
def main():
    # Place this reversible regression output on D locally and RUNNER_TEMP in CI.
    import os
    base=Path(os.environ.get('TMPDIR','/mnt/lean-research-d/tmp'))
    with tempfile.TemporaryDirectory(prefix='native-reader-selftest-',dir=base)as tmp:
        out=Path(tmp)/'fixture';fixture(out);e.verify(out);passed=['positive_empty_axiom_set_and_object_executables']
        def reject(name,mutate):
            mutate();seal(out)
            try:e.verify(out)
            except (ValueError,KeyError,TypeError,FileNotFoundError):passed.append(name)
            else:raise ValueError('Reader accepted regression '+name)
            import shutil
            shutil.rmtree(out);fixture(out)
        def json_change(file,fn):
            data=c.readj(out/file);fn(data);c.dump(out/file,data)
        reject('string_executables',lambda:[json_change(f,lambda d:d.update(actual_executables='legacy string'))for f in ['PRE_AUDIT.json','POST_AUDIT.json']])
        reject('missing_control_root',lambda:(out/'control-1-roots.txt').write_text('Different.root\n'))
        reject('empty_dependency_line',lambda:(out/'control-1-type-dependencies.txt').write_text('\n'))
        reject('extra_axiom',lambda:(out/'kernel-axioms.txt').write_text('sorryAx\n'))
        reject('changed_memory_cap',lambda:json_change('STAGES.json',lambda d:d[-1]['command'].__setitem__(4,'-M8000')))
        reject('post_drift',lambda:json_change('POST_AUDIT.json',lambda d:d.update(source_commit='0'*40)))
        reject('changed_model_body',lambda:(out/'models/1.expr').write_text('value tampered\n'))
        reject('missing_kinds',lambda:(out/'types.log').write_text((out/'types.log').read_text().replace('DECLARATION_KIND_CHECK_PASS','absent')))
        reject('changed_invocation',lambda:(out/'AuditInvocation.lean').write_text('import Lean\n'))
        reject('duplicate_json_key',lambda:(out/'SUMMARY.json').write_text('{"status":"PASS","status":"PASS"}'))
        # Byte inventory must reject unsealed extras independently of semantic fields.
        (out/'unexpected').write_text('extra')
        try:e.verify(out)
        except ValueError:passed.append('unsealed_extra_file')
        else:raise ValueError('Accepted unsealed extra')
        import shutil
        shutil.rmtree(out);fixture(out)
        wrapper=Path(tmp)/'downloaded';wrapper.mkdir();name='native-execution-20261019T000000000000Z';shutil.move(out,wrapper/name)
        c.dump(wrapper/'LATEST.json',{'directory':name,'summary_sha256':c.sha(wrapper/name/'SUMMARY.json')})
        e.verify(e.downloaded_directory(wrapper));passed.append('downloaded_latest_wrapper')
        (wrapper/'extra').write_text('unsealed wrapper file')
        try:e.downloaded_directory(wrapper)
        except ValueError:passed.append('unexpected_outer_artifact_file')
        else:raise ValueError('Accepted outer artifact extra')
        for bad in ['../outside','/absolute','a\\b','a/../b','a//b']:
            try:c.safe_relative(bad)
            except ValueError:passed.append('unsafe_path_'+bad)
            else:raise ValueError('Accepted unsafe path')
    print({'status':'NATIVE_EXECUTION_READER_SELFTEST_PASS','checks':passed,'kernel_run':False})
if __name__=='__main__':main()
