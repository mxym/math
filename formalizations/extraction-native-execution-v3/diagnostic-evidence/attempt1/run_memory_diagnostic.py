from pathlib import Path
import datetime,fcntl,os,resource,shutil,signal,subprocess,sys,time
ROOT=Path(__file__).resolve().parent
AUDIT=Path('/mnt/lean-research-d/worktrees/extraction-native-execution-audit-20261019/formalizations/extraction-native-execution-audit')
sys.path.insert(0,str(AUDIT))
import common as c,runtime

def snapshot(rt):
    c.binding()
    owned=c.readj(AUDIT/'verification/r2-local-failure-20261019/OWNED_OLEANS.json')
    assert set(owned)==c.expected_owned_outputs()and len(owned)==430
    for n,h in owned.items():assert c.sha(c.path_at(c.REPO,n))==h
    return {'r2_source_manifest_sha256':c.sha(AUDIT/'SOURCE_HASHES.json'),'r2_binding_sha256':c.sha(AUDIT/'BINDING.json'),'r2_failed_seal_manifest_sha256':c.sha(AUDIT/'verification/r2-local-failure-20261019/PARTIAL_EVIDENCE_HASHES.json'),'actual_owned_oleans':owned,'actual_executables':runtime.configure()['actual_executables'],'dependencies':runtime.dependencies(rt),'protected_old_files':c.protected_inputs()['files']}

def main():
    rt=runtime.configure();env=rt['env'];(ROOT/'build').mkdir(exist_ok=True)
    if not ROOT.resolve().is_relative_to(Path('/mnt/lean-research-d/tmp')):raise ValueError('Diagnostic outside guarded D temporary root')
    tools={}
    for name in ['lean','lake','leanc','clang','ld.lld']:
        p=Path(shutil.which(name,path=env['PATH'])).resolve()
        if not p.is_relative_to(Path('/mnt/lean-research-d/toolchains')):raise ValueError('Tool outside verified D toolchain')
        tools[name]={'path':str(p),'sha256':c.sha(p)}
    commands=[('compile-lean',[tools['lean']['path'],'-j1','-M4000','-o','build/Diagnostic.olean','-c','build/Diagnostic.c','Diagnostic.lean']),('compile-native',[tools['leanc']['path'],'-O2','-o','build/diagnostic','build/Diagnostic.c']),('data-only-run',[tools['lake']['path'],'env',str(ROOT/'build/diagnostic')])]
    binding={'schema':1,'diagnostic_source_sha256':c.sha(ROOT/'Diagnostic.lean'),'runner_sha256':c.sha(Path(__file__)),'tools':tools,'commands':commands,'lean_frontend_memory_arg':'-M4000','native_memory_bytes':4194304000,'native_c_compile_rlimit_as_bytes':4194304000,'native_run_cap_mechanism':'Lean.Internal.setMaxMemory(4000*1024*1024) before data-only import; no higher limit','no_kernel_replay':True,'import_module':'NativeExecutionAudit','import_load_extensions':False,'source_commit':'8b78ef1ea7c16af0bb98ae8fb6bb97ac3272ee78','r2_metadata':'954497290f84773484e765efd2f478643c67de9f','r2_failure_seal':'0b612254b13274ef4d2c89175ef3be0fc99e4130'}
    if (ROOT/'BINDING.json').exists():raise ValueError('Existing diagnostic must not be overwritten')
    c.dump(ROOT/'BINDING.json',binding);records=[]
    with open(rt['lock'],'a')as lock:
        fcntl.flock(lock,fcntl.LOCK_EX);before=snapshot(rt);c.dump(ROOT/'PRE_DIAGNOSTIC.json',before)
        for label,cmd in commands:
            start=time.monotonic();log=ROOT/(label+'.log')
            def limit_c():resource.setrlimit(resource.RLIMIT_AS,(4194304000,4194304000))
            with log.open('w')as f:
                proc=subprocess.Popen(cmd,cwd=AUDIT if label=='data-only-run'else ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limit_c if label=='compile-native'else None)
                try:code=proc.wait(timeout=600)
                except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait();code=124
            row={'stage':label,'command':cmd,'cwd':str(AUDIT if label=='data-only-run'else ROOT),'exit_code':code,'seconds':round(time.monotonic()-start,3),'log':log.name,'sha256':c.sha(log),'peak_child_rss_kib_cumulative':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}
            records.append(row);c.dump(ROOT/'STAGES.json',records);print(row,flush=True)
            if code:
                c.dump(ROOT/'FAILURE.json',{'stage':label,'exit_code':code,'no_kernel_replay':True,'binding_sha256':c.sha(ROOT/'BINDING.json')});raise ValueError('Diagnostic failed '+label)
            if label=='compile-native':c.dump(ROOT/'BINARY.json',{'path':'build/diagnostic','sha256':c.sha(ROOT/'build/diagnostic'),'bytes':(ROOT/'build/diagnostic').stat().st_size,'generated_c_sha256':c.sha(ROOT/'build/Diagnostic.c')})
        after=snapshot(rt);c.dump(ROOT/'POST_DIAGNOSTIC.json',after);assert before==after
        text=(ROOT/'data-only-run.log').read_text()
        assert text.count('DIAGNOSTIC_MAX_MEMORY_BYTES 4194304000')==1
        assert text.count('DATA_ONLY_THEOREM_PRESENT')==3 and text.count('DATA_ONLY_DEFINITION_PRESENT')==2
        assert text.count('DATA_ONLY_IMPORT_DIAGNOSTIC_COMPLETE_NOT_KERNEL_REPLAY')==1
        c.dump(ROOT/'REPORT.json',{'status':'DATA_ONLY_MEMORY_DIAGNOSTIC_PASS_NOT_KERNEL_REPLAY','binding_sha256':c.sha(ROOT/'BINDING.json'),'binary_sha256':c.sha(ROOT/'build/diagnostic'),'cap_bytes':4194304000,'pre_post_fresh430_tool_pins_and_old5537_equal':True,'theorem_presence_checks':3,'definition_presence_checks':2,'no_kernel_replay':True,'stages':records})
        c.dump(ROOT/'EVIDENCE_HASHES.json',c.file_manifest(ROOT));print('DATA_ONLY_MEMORY_DIAGNOSTIC_PASS_NOT_KERNEL_REPLAY',flush=True)

if __name__=='__main__':main()
