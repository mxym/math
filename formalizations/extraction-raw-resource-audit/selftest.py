#!/usr/bin/env python3
"""Synthetic reader tamper tests only. Never produces mathematical audit evidence."""
from pathlib import Path
import copy,json,os,shutil,tempfile
import reproduce as a
import evidence as e
import ci_driver as c


def artifact_selftest(out,base):
    """Run the full downloaded-artifact reader on an explicitly synthetic binding.

    Exact event Git-blob/workflow checks are separately tested by production
    preflight. They are substituted only here because no actual workflow has
    been installed or mathematical manifest frozen in this preliminary stage.
    """
    import verify_artifact as v
    original_root=a.ROOT;original_packages=a.package_roots;packages=original_packages()
    original_commit_check,original_workflow=c.check_commit,c.workflow_binding
    fake=original_root/'verification'/('reader-SYNTHETIC-'+str(os.getpid()));fake.mkdir()
    try:
        inputs=a.inventory()
        for name in inputs:
            source=a.REPO/name
            if source.is_relative_to(original_root):
                target=fake/source.relative_to(original_root);target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,target)
        a.ROOT=fake;a.package_roots=lambda:[fake]+packages[1:]
        scope=a.readj(fake/'SCOPE.json');scope['state']='READY';scope['pending_required']=[];a.dump(fake/'SCOPE.json',scope)
        protected=a.old_inventory();inputs=a.inventory();a.dump(fake/'SOURCE_HASHES.json',inputs);a.dump(fake/'PROTECTED_INPUTS.json',protected)
        workflow=dict(path=c.WORKFLOW,sha256=a.sha(fake/c.TEMPLATE),bound_template_sha256=a.sha(fake/c.TEMPLATE))
        c.workflow_binding=lambda:workflow
        c.check_commit=lambda commit:a.check_binding(check_dependencies=False)
        who=dict(source_commit=scope['source_head'],workflow_commit=scope['source_head'],run_id='12345',run_attempt='2',repository='mxym/math',workflow_ref='mxym/math/'+c.WORKFLOW+'@refs/heads/main')
        ci_base=Path('/home/runner/work/_temp/extraction-raw-resource-12345-2');original_output=ci_base/'evidence'/out.name
        policy=a.readj(fake/'CI_EXECUTION_POLICY.json');binaries={tool:dict(path=str(ci_base/'elan/toolchains/pinned/bin'/tool),sha256=digest)for tool,digest in policy['binary_sha256'].items()}
        snapshot=dict(source_head=scope['source_head'],source_inputs=inputs,protected_inputs=protected,execution_inputs=policy,binaries=binaries)
        for name in ['PRE_AUDIT.json','POST_AUDIT.json']:a.dump(out/name,snapshot)
        a.dump(out/'EXECUTION.json',dict(guard='GITHUB_HOSTED_LINUX_RUNNER_VERIFIED',execution_inputs=policy,portable_binary_inputs=binaries,runtime={}))
        a.dump(out/'SOURCE_HASHES.json',inputs);a.dump(out/'SCOPE.json',scope)
        invocation=out/'AuditInvocation.lean';invocation.write_text((fake/'Audit.lean').read_text().replace('"verification/raw-resource-',json.dumps(str(original_output/'raw-resource-'))[:-1]))
        stages=a.readj(out/'STAGES.json');stages[-1]['command'][-1]=str(original_output/'AuditInvocation.lean');a.dump(out/'STAGES.json',stages)
        summary=a.readj(out/'SUMMARY.json');summary.update(stages=stages,source_inputs=len(inputs),source_manifest_sha256=a.sha(out/'SOURCE_HASHES.json'),runtime_guard='GITHUB_HOSTED_LINUX_RUNNER_VERIFIED',audit_invocation_sha256=a.sha(invocation));a.dump(out/'SUMMARY.json',summary)
        artifact=base/'downloaded-SYNTHETIC-artifact';artifact.mkdir();shutil.copytree(out,artifact/out.name)
        for name in c.EXPORTS:shutil.copy2(fake/name,artifact/name)
        recipe=artifact/'recipe';recipe.mkdir()
        for name in inputs:
            source=a.REPO/name
            if source.is_relative_to(fake):
                target=recipe/source.relative_to(fake);target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,target)
        latest=dict(directory=out.name,summary_sha256=a.sha(out/'SUMMARY.json'));a.dump(artifact/'LATEST.json',latest)
        context=dict(who,status='GITHUB_CI_AUDIT_COMPLETED_PENDING_ARTIFACT_DOWNLOAD_CHECK',actual_workflow=workflow,source_manifest_sha256=a.sha(fake/'SOURCE_HASHES.json'),latest=latest,actual_command=['reproduce.py','--github-actions','--fresh'],actual_cwd=fake.relative_to(a.REPO).as_posix(),synthetic_fixture_only=True);a.dump(artifact/'CI_CONTEXT.json',context)
        before=c.snapshot(binaries)
        for name in ['PRE_AUDIT.json','POST_AUDIT.json']:a.dump(artifact/name,before)
        a.dump(artifact/'BOOTSTRAP_BINARIES.json',binaries);a.dump(artifact/'BOOTSTRAP.json',dict(github=who,actual_workflow=workflow,source_manifest_sha256=a.sha(fake/'SOURCE_HASHES.json'),installer_url=policy['elan_init_url']))
        def rehash():a.dump(artifact/'ARTIFACT_HASHES.json',{path.relative_to(artifact).as_posix():a.sha(path)for path in artifact.rglob('*')if path.is_file()and path!=artifact/'ARTIFACT_HASHES.json'})
        def read():return v.verify(artifact,scope['source_head'],'12345','2')
        rehash();read();checks=['complete-synthetic-downloaded-artifact-positive']
        def mutation(label,change,restore):
            change();rehash()
            try:read()
            except (RuntimeError,ValueError,KeyError,FileNotFoundError):checks.append(label)
            else:raise RuntimeError('Downloaded artifact tamper accepted '+label)
            finally:restore();rehash()
        mutation('artifact-wrong-run',lambda:(context.update(run_id='9'),a.dump(artifact/'CI_CONTEXT.json',context)),lambda:(context.update(run_id='12345'),a.dump(artifact/'CI_CONTEXT.json',context)))
        mutation('artifact-wrong-actual-command',lambda:(context.update(actual_command=['reproduce.py']),a.dump(artifact/'CI_CONTEXT.json',context)),lambda:(context.update(actual_command=['reproduce.py','--github-actions','--fresh']),a.dump(artifact/'CI_CONTEXT.json',context)))
        path=recipe/'evidence.py';saved=path.read_bytes();mutation('artifact-changed-reader',lambda:path.write_bytes(saved+b'\n# changed\n'),lambda:path.write_bytes(saved))
        path=artifact/'POST_AUDIT.json';bad=copy.deepcopy(before);bad['source_inputs']={};mutation('artifact-prepost-drift',lambda:a.dump(path,bad),lambda:a.dump(path,before))
        path=artifact/out.name/'raw-resource-control-1-axioms.txt';mutation('artifact-noncanonical-empty-axioms',lambda:path.write_bytes(b''),lambda:path.write_bytes(b'\n'))
        bootstrap=a.readj(artifact/'BOOTSTRAP.json');mutation('artifact-bootstrap-identity',lambda:(bootstrap['github'].update(run_id='8'),a.dump(artifact/'BOOTSTRAP.json',bootstrap)),lambda:(bootstrap['github'].update(run_id='12345'),a.dump(artifact/'BOOTSTRAP.json',bootstrap)))
        read();return checks
    finally:
        a.ROOT=original_root;a.package_roots=original_packages;c.check_commit=original_commit_check;c.workflow_binding=original_workflow
        target=fake.resolve()
        if not target.is_relative_to((original_root/'verification').resolve())or not target.name.startswith('reader-SYNTHETIC-'):raise RuntimeError('Unsafe synthetic recipe cleanup')
        shutil.rmtree(target)


def main():
    from audit_runtime import configure,hosted_context
    configure(False)
    parent=Path('/mnt/d/math/tmp/extraction-resume-20261018');base=Path(tempfile.mkdtemp(prefix='raw-resource-reader-SYNTHETIC-',dir=parent))
    checks=[]
    def rejected(label,action):
        try:action()
        except (RuntimeError,ValueError,KeyError,FileNotFoundError):checks.append(label);return
        raise RuntimeError('Tamper accepted: '+label)
    try:
        atom=base/'axioms.txt'
        for raw,expected in [(b'\n',set()),(b'Classical.choice\n',{'Classical.choice'}),(b'Classical.choice\nQuot.sound\npropext\n',a.ALLOW)]:
            atom.write_bytes(raw);assert e.axiom_set(atom)==expected
        for index,raw in enumerate([b'',b'\n\n',b'propext',b'propext\r\n',b' propext\n',b'propext \n',b'propext\npropext\n',b'propext\n\n',b'Classical. choice\n',b'\xff\n',b'\t\n',b'propext\x0b\n',b'propext\xe2\x80\xa8Quot.sound\n']):
            atom.write_bytes(raw);rejected('malformed-axioms-'+str(index),lambda:e.axiom_set(atom))
        scope,roots,defs,controls=a.scope_lists();inputs=a.inventory();protected=a.old_inventory();out=base/'raw-resource-SYNTHETIC';out.mkdir()
        policy=a.readj(a.ROOT/'EXECUTION_INPUTS.json');binaries={tool:dict(path=path,sha256=digest)for tool in ['lean','lake']for path,digest in policy.items()if path.endswith('/'+tool)}
        snapshot=dict(source_head=scope['source_head'],source_inputs=inputs,protected_inputs=protected,execution_inputs=policy,binaries=binaries)
        for name in ['PRE_AUDIT.json','POST_AUDIT.json']:a.dump(out/name,snapshot)
        a.dump(out/'EXECUTION.json',dict(guard='D_BACKED_STORAGE_VERIFIED',execution_inputs=policy,portable_binary_inputs={},runtime=dict(actual_executables=binaries)))
        a.dump(out/'SOURCE_HASHES.json',inputs);a.dump(out/'SCOPE.json',scope)
        kind='DECLARATION_KIND_CHECK_PASS\n'+''.join("'"+name+"' does not depend on any axioms\n"for name in roots+defs)
        a.dump(out/'AXIOM_REPORT.json',{name:[]for name in roots+defs})
        closure=roots+defs+['True','True.intro']
        assert len(set(closure))==len(closure)
        (out/'raw-resource-kernel-roots.txt').write_text('\n'.join(roots+defs)+'\n');(out/'raw-resource-kernel-closure.txt').write_text('\n'.join(closure)+'\n');(out/'raw-resource-kernel-axioms.txt').write_bytes(b'\n')
        replay='SYNTHETIC FIXTURE: NO LEAN OR KERNEL WAS EXECUTED\nEMPTY_KERNEL_REPLAY_PASS '+str(len(closure))+' declarations\n'
        for index,name in enumerate(controls,1):
            stem=out/('raw-resource-control-'+str(index));Path(str(stem)+'-roots.txt').write_text(name+'\n');Path(str(stem)+'-type-dependencies.txt').write_text('True\nTrue.intro\n');Path(str(stem)+'-axioms.txt').write_bytes(b'\n')
            replay+='TYPE_CLOSURE_REPLAY_PASS 2 declarations\nCORRUPTED_PROOF_REJECTED '+name+'\nCORRUPTED_PROOF_TYPE_MISMATCH_REJECTED '+name+'\n'
        invocation=out/'AuditInvocation.lean';invocation.write_text((a.ROOT/'Audit.lean').read_text().replace('"verification/raw-resource-',json.dumps(str(out/'raw-resource-'))[:-1]))
        commands=[('toolchain',['lake','env','lean','--version'],'SYNTHETIC TOOLCHAIN\n'),('build-audit',['lake','build','RawResourceAudit','RawResourceVerification'],'SYNTHETIC BUILD\n'),('root-types-axioms',['lake','env','lean','-j1','-M7000','Check.lean'],kind),('finite-syntax-bytecode',['lake','env','lean','-j1','-M7000','--run','ExecutableCheck.lean'],'RAW_RESOURCE_SYNTAX_CHECK_PASS\n'),('trust0-replay',['lake','env','lean','-j1','-M7000',str(invocation)],replay)]
        stages=[]
        for label,command,log in commands:
            path=out/(label+'.log');path.write_text(log);stages.append(dict(stage=label,command=command,exit_code=0,log=path.name,sha256=a.sha(path),seconds=0))
        summary=dict(status='PASS',mathematical_source_head=scope['source_head'],source_inputs=len(inputs),endpoint_theorems=len(roots),model_definitions=len(defs),same_type_forged_proof_controls=len(controls),kernel_trust=0,fresh_owned_build=True,runtime_guard='D_BACKED_STORAGE_VERIFIED',fresh_packages=a.NEW,axioms=[],source_manifest_sha256=a.sha(out/'SOURCE_HASHES.json'),stages=stages,kernel_declarations=len(closure),audit_invocation_sha256=a.sha(invocation),synthetic_fixture_only=True)
        def flush():a.dump(out/'STAGES.json',stages);a.dump(out/'SUMMARY.json',summary)
        flush();e.verify_run(out,'D_BACKED_STORAGE_VERIFIED');checks.append('complete-synthetic-reader-positive')
        def mutation(name,change,restore):
            change();rejected(name,lambda:e.verify_run(out,'D_BACKED_STORAGE_VERIFIED'));restore()
        saved=copy.deepcopy(summary)
        mutation('wrong-scope-count',lambda:(summary.update(endpoint_theorems=0),flush()),lambda:(summary.update(saved),flush()))
        mutation('trust-one',lambda:(summary.update(kernel_trust=1),flush()),lambda:(summary.update(saved),flush()))
        mutation('not-fresh',lambda:(summary.update(fresh_owned_build=False),flush()),lambda:(summary.update(saved),flush()))
        mutation('wrong-guard',lambda:(summary.update(runtime_guard='GITHUB_HOSTED_LINUX_RUNNER_VERIFIED'),flush()),lambda:(summary.update(saved),flush()))
        cmd=stages[-1]['command'][:]
        mutation('extra-lean-flag',lambda:(stages[-1]['command'].insert(5,'--trust=1'),flush()),lambda:(stages[-1].update(command=cmd),flush()))
        path=out/'raw-resource-control-1-axioms.txt';mutation('unknown-control-axiom',lambda:path.write_text('sorryAx\n'),lambda:path.write_bytes(b'\n'))
        path=out/'raw-resource-control-1-type-dependencies.txt';mutation('missing-forgery-prerequisite',lambda:path.write_text('True\nFalse\n'),lambda:path.write_text('True\nTrue.intro\n'))
        path=out/'POST_AUDIT.json';bad=copy.deepcopy(snapshot);bad['source_inputs']={};mutation('post-source-drift',lambda:a.dump(path,bad),lambda:a.dump(path,snapshot))
        path=out/'trust0-replay.log'
        def altered_replay(text):path.write_text(text);stages[-1]['sha256']=a.sha(path);flush()
        mutation('same-type-rejection-omitted',lambda:altered_replay(replay.replace('CORRUPTED_PROOF_TYPE_MISMATCH_REJECTED '+controls[0]+'\n','',1)),lambda:altered_replay(replay))
        old=invocation.read_text();mutation('partial-audit-invocation',lambda:(invocation.write_text('import RawResourceAudit\n'),summary.update(audit_invocation_sha256=a.sha(invocation)),flush()),lambda:(invocation.write_text(old),summary.update(audit_invocation_sha256=a.sha(invocation)),flush()))
        e.verify_run(out,'D_BACKED_STORAGE_VERIFIED')
        # Test actual workflow binding on isolated files only; no installed workflow is touched.
        old_repo,old_root=a.REPO,a.ROOT;fake=base/'workflow-check';(fake/'.github/workflows').mkdir(parents=True);(fake/'audit').mkdir();a.REPO=fake;a.ROOT=fake/'audit'
        try:
            (a.ROOT/c.TEMPLATE).write_text('bound template\n');actual=a.REPO/c.WORKFLOW;actual.write_text('bound template\n');c.workflow_binding();checks.append('exact-workflow-positive')
            actual.write_text('changed\n');rejected('changed-actual-workflow',c.workflow_binding);actual.unlink();rejected('missing-actual-workflow',c.workflow_binding);actual.symlink_to(a.ROOT/c.TEMPLATE);rejected('symlink-actual-workflow',c.workflow_binding)
        finally:a.REPO,a.ROOT=old_repo,old_root
        checks+=artifact_selftest(out,base)
        # Explicit CI mode must never bypass the local WSL D guard.
        values={'GITHUB_ACTIONS':'true','CI':'true','RUNNER_OS':'Linux','RUNNER_ARCH':'X64','RUNNER_ENVIRONMENT':'github-hosted'};saved_env={k:os.environ.get(k)for k in values};os.environ.update(values)
        try:rejected('spoofed-hosted-context-on-WSL',hosted_context)
        finally:
            for k,v in saved_env.items():
                if v is None:os.environ.pop(k,None)
                else:os.environ[k]=v
        result=dict(status='SYNTHETIC_READER_SELFTEST_PASS_NOT_LEAN_VERIFICATION',positive_axiom_encodings=3,malformed_axiom_encodings=13,checks=checks,mathematical_or_kernel_verification_performed=False)
        report=a.ROOT/'verification/READER_SELFTEST.json';report.parent.mkdir(exist_ok=True);a.dump(report,result);print(json.dumps(result,indent=2))
    finally:
        target=base.resolve()
        if not target.is_relative_to(parent.resolve())or not target.name.startswith('raw-resource-reader-SYNTHETIC-'):raise RuntimeError('Unsafe owned fixture cleanup')
        shutil.rmtree(target)

if __name__=='__main__':main()
