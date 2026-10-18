#!/usr/bin/env python3
"""Real completed evidence plus exact frozen-producer serializer fixtures. No Lean runs."""
from pathlib import Path
import argparse,ast,copy,hashlib,json,os,shutil,sys
from types import SimpleNamespace
from verify_local_v2 import verify,a,ROOT,check_reader
from audit_runtime import configure
from evidence_v2 import verify_run as corrected_core
from evidence import verify_run as frozen_core


def writer_statement():
    source=a.ROOT/'reproduce.py';raw=source.read_text();tree=ast.parse(raw);found=[]
    for node in ast.walk(tree):
        if not isinstance(node,ast.Expr)or not isinstance(node.value,ast.Call)or not isinstance(node.value.func,ast.Name)or node.value.func.id!='dump'or not node.value.args:continue
        target=node.value.args[0]
        if isinstance(target,ast.BinOp)and isinstance(target.op,ast.Div)and isinstance(target.left,ast.Name)and target.left.id=='out'and isinstance(target.right,ast.Constant)and target.right.value=='EXECUTION.json':found.append(node)
    if len(found)!=1:raise RuntimeError('Frozen producer serializer is not unique')
    text=ast.get_source_segment(raw,found[0]);module=ast.Module(body=found,type_ignores=[])
    return compile(ast.fix_missing_locations(module),str(source),'exec'),hashlib.sha256(text.encode()).hexdigest()


def write_actual_format(out,github_actions,runtime,binary_inputs):
    # Executes only the exact statement extracted from the hash-bound producer,
    # with controlled fixture variables. It does not invoke its main(), CI guard
    # or any Lean command. No recorded literal is parsed/evaluated.
    code,digest=writer_statement()
    values=dict(out=out,args=SimpleNamespace(github_actions=github_actions),runtime=runtime,binary_inputs=binary_inputs,env=runtime['env'],ROOT=a.ROOT,readj=a.readj,dump=a.dump,sys=sys)
    exec(code,values)
    return digest


def main():
    parser=argparse.ArgumentParser();parser.add_argument('directory');args=parser.parse_args();a.check_execution_inputs(False);runtime=configure(False);check_reader()
    original=Path(args.directory).resolve();verify(original)
    fixture=a.ROOT/'verification'/('reader-local-v2-SYNTHETIC-'+str(os.getpid()))
    if fixture.exists():raise RuntimeError('Fixture already exists')
    shutil.copytree(original,fixture);checks=[]
    def rejected(label,action,expected=None):
        try:action()
        except (RuntimeError,ValueError,KeyError,FileNotFoundError)as error:
            if expected is not None and str(error)!=expected:raise RuntimeError('Wrong expected rejection '+label+': '+str(error))from error
            checks.append(label);return
        raise RuntimeError('Tamper accepted '+label)
    try:
        digest=write_actual_format(fixture,False,runtime,{})
        assert type(a.readj(fixture/'EXECUTION.json')['runtime']['actual_executables'])is str
        verify(fixture);checks.append('exact-producer-local-serializer-positive')
        rejected('original-local-reader-actual-format-failure',lambda:frozen_core(fixture,'D_BACKED_STORAGE_VERIFIED'),'Actual tool binary drift')
        saved={name:(fixture/name).read_bytes()for name in ['EXECUTION.json','PRE_AUDIT.json','POST_AUDIT.json','SOURCE_HASHES.json','SUMMARY.json']}
        def reset():
            for name,raw in saved.items():(fixture/name).write_bytes(raw)
        def local_case(label,change):
            reset();change();rejected(label,lambda:verify(fixture));reset()
        def mutate_record(value):
            obj=a.readj(fixture/'EXECUTION.json');obj['runtime']['actual_executables']=value;a.dump(fixture/'EXECUTION.json',obj)
        pre=a.readj(fixture/'PRE_AUDIT.json');record=str(pre['binaries']);lean=pre['binaries']['lean']
        local_case('local-wrong-json-type',lambda:mutate_record(pre['binaries']))
        local_case('local-wrong-key',lambda:mutate_record(record.replace("'lean':","'LEAN':",1)))
        local_case('local-trailing-whitespace',lambda:mutate_record(record+' '))
        local_case('local-wrong-recorded-path',lambda:mutate_record(record.replace(lean['path'],'/tmp/not-the-pinned-tool',1)))
        local_case('local-wrong-recorded-hash',lambda:mutate_record(record.replace(lean['sha256'],'0'*64,1)))
        def consistent(change):
            obj=copy.deepcopy(pre);change(obj['binaries'])
            for name in ['PRE_AUDIT.json','POST_AUDIT.json']:a.dump(fixture/name,obj)
            mutate_record(str(obj['binaries']))
        local_case('consistent-prepost-wrong-tool-path',lambda:consistent(lambda b:b['lean'].update(path='/mnt/lean-research-d/toolchains/not-the-current-tool')))
        local_case('consistent-prepost-wrong-tool-hash',lambda:consistent(lambda b:b['lean'].update(sha256='0'*64)))
        local_case('consistent-prepost-missing-tool-key',lambda:consistent(lambda b:b.pop('lake')))
        def source_drift():
            obj=a.readj(fixture/'SOURCE_HASHES.json');obj[next(iter(obj))]='0'*64;a.dump(fixture/'SOURCE_HASHES.json',obj)
        local_case('bound-source-record-drift',source_drift)
        # The hosted branch is tested through the SAME actual serialization
        # statement, with controlled hosted-shaped data. This is a synthetic
        # format test, not execution of the forbidden-local hosted guard or CI.
        policy=a.readj(a.ROOT/'CI_EXECUTION_POLICY.json')
        ci_root=Path('/home/runner/work/_temp/extraction-raw-resource-SYNTHETIC')
        portable={tool:dict(path=str(ci_root/'elan/toolchains/pinned/bin'/tool),sha256=value)for tool,value in policy['binary_sha256'].items()}
        ci_runtime=dict(env=runtime['env'],guard='GITHUB_HOSTED_LINUX_RUNNER_VERIFIED',output=ci_root/'evidence',lock=ci_root/'build.lock',memory_mb=11000,available_memory_mb=14000,available_disk_bytes=10000000000)
        write_actual_format(fixture,True,ci_runtime,portable)
        assert type(a.readj(fixture/'EXECUTION.json')['portable_binary_inputs'])is dict
        obj=a.readj(fixture/'PRE_AUDIT.json');obj.update(execution_inputs=policy,binaries=portable)
        for name in ['PRE_AUDIT.json','POST_AUDIT.json']:a.dump(fixture/name,obj)
        summary=a.readj(fixture/'SUMMARY.json');summary.update(runtime_guard='GITHUB_HOSTED_LINUX_RUNNER_VERIFIED',synthetic_fixture_only=True);a.dump(fixture/'SUMMARY.json',summary)
        for reader in [frozen_core,corrected_core]:reader(fixture,'GITHUB_HOSTED_LINUX_RUNNER_VERIFIED')
        checks.append('exact-producer-hosted-serializer-both-readers-positive')
        ci_saved=(fixture/'EXECUTION.json').read_bytes()
        def ci_case(label,value):
            obj=a.readj(fixture/'EXECUTION.json');obj['portable_binary_inputs']=value;a.dump(fixture/'EXECUTION.json',obj)
            for label_suffix,reader in [('original',frozen_core),('v2',corrected_core)]:rejected(label+'-'+label_suffix,lambda reader=reader:reader(fixture,'GITHUB_HOSTED_LINUX_RUNNER_VERIFIED'))
            (fixture/'EXECUTION.json').write_bytes(ci_saved)
        ci_case('hosted-wrong-object-type',str(portable))
        bad=copy.deepcopy(portable);bad.pop('lake');ci_case('hosted-missing-key',bad)
        bad=copy.deepcopy(portable);bad['lean']['path']='/tmp/wrong';ci_case('hosted-wrong-path',bad)
        bad=copy.deepcopy(portable);bad['lean']['sha256']='0'*64;ci_case('hosted-wrong-hash',bad)
        result=dict(status='REAL_PRODUCER_SERIALIZER_AND_TAMPER_SELFTEST_PASS_NOT_NEW_KERNEL_OR_CI',original_completed_run=original.name,producer_sha256=a.sha(a.ROOT/'reproduce.py'),exact_writer_statement_sha256=digest,reader_manifest_sha256=a.sha(ROOT/'READER_HASHES.json'),checks=checks,additional_Lean_or_kernel_execution=False,hosted_CI_execution=False)
        a.dump(a.ROOT/'verification/LOCAL_READER_V2_SELFTEST.json',result);print(json.dumps(result,indent=2))
    finally:
        target=fixture.resolve()
        if not target.is_relative_to((a.ROOT/'verification').resolve())or not target.name.startswith('reader-local-v2-SYNTHETIC-'):raise RuntimeError('Unsafe owned fixture cleanup')
        shutil.rmtree(target)

if __name__=='__main__':main()
