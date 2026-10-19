"""V3 native proof replay. Local r2 receipt reuse; hosted full fresh mathematics."""
from pathlib import Path
import argparse,datetime,fcntl,os,re,resource,shutil,signal,subprocess,time
import common as c
import runtime

def old430():
    receipt=c.readj(c.ROOT/'R2_FRESH_RECEIPT.json');owned=receipt['owned_oleans']
    if len(owned)!=430:raise ValueError('Wrong r2 receipt count')
    for n,h in owned.items():
        if c.sha(c.path_at(c.REPO,n))!=h:raise ValueError('Independent r2 olean drift '+n)
    return owned

def math_outputs():
    result={}
    for n in c.expected_owned_outputs():
        p=c.path_at(c.REPO,n)
        result[n]=c.sha(p)
    return result

def snapshot(rt,hosted):
    c.binding()
    return {'source_commit':c.scope()['source_commit'],'source_inputs':c.inventory()[0],'protected_inputs':c.protected_inputs()['files'],'actual_executables':runtime.configure(hosted)['actual_executables'],'dependencies':runtime.dependencies(rt),'sdk_inputs':rt['sdk_inputs'],'reused_r2_oleans':None if hosted else old430()}

def checkout(commit):
    if c.git('rev-parse','HEAD').decode().strip()!=commit:raise ValueError('Wrong event commit')
    for n in list(c.readj(c.ROOT/'SOURCE_HASHES.json'))+[c.PREFIX+'/SOURCE_HASHES.json',c.PREFIX+'/BINDING.json']:
        if c.path_at(c.REPO,n).read_bytes()!=c.git('show',commit+':'+n):raise ValueError('Event Git blob differs '+n)

def run(hosted=False):
    s,b=c.binding();rt=runtime.configure(hosted);runtime.dependencies(rt,True)
    if hosted:checkout(os.environ['GITHUB_SHA'])
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ');out=rt['output']/('native-execution-v3-'+stamp);out.mkdir(parents=True)
    for n in ['native','root-types','models']:(out/n).mkdir()
    records=[]
    def stage(label,command,limit=1800,c_limit=False):
        actual=[x.replace('@EVIDENCE@',str(out.resolve()))for x in command];actual[0]=rt['actual_executables'][actual[0]]['path']
        log=out/(label+'.log');start=time.monotonic()
        def limit_native_c():resource.setrlimit(resource.RLIMIT_AS,(4194304000,4194304000))
        with log.open('w')as f:
            proc=subprocess.Popen(actual,cwd=c.ROOT,env=rt['env'],stdout=f,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limit_native_c if c_limit else None)
            try:code=proc.wait(timeout=limit)
            except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait();code=124
        row={'stage':label,'command':command,'actual_command':actual,'exit_code':code,'seconds':round(time.monotonic()-start,3),'log':log.name,'sha256':c.sha(log),'peak_child_rss_kib_cumulative':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}
        records.append(row);c.dump(out/'STAGES.json',records);print(row,flush=True)
        if code:raise ValueError('Failed native v3 stage '+label+' '+str(log))
        return log.read_text()
    with open(rt['lock'],'a')as lock:
        fcntl.flock(lock,fcntl.LOCK_EX);before=snapshot(rt,hosted);c.dump(out/'PRE_AUDIT.json',before)
        if hosted:
            builds=[p/'.lake/build'for p in c.package_roots()]
            for p in builds:
                if p.is_symlink()or not p.resolve().is_relative_to(c.REPO.resolve())or p.parts[-2:]!=('.lake','build'):raise ValueError('Unsafe owned build directory')
            for p in builds:
                if p.exists():shutil.rmtree(p)
            stage('fresh-mathematics',['lake','build','ConcreteNativeExtraction.AssembledProgram'],3600)
        else:old430()
        math_before=math_outputs();c.dump(out/'MATHEMATICAL_OLEANS.json',math_before)
        stage('compile-driver',['lean','-j1','-M4000','-o','@EVIDENCE@/native/Driver.olean','-c','@EVIDENCE@/native/Driver.c','Driver.lean'],600)
        stage('link-driver',['leanc','-O2','-o','@EVIDENCE@/native/audit-driver','@EVIDENCE@/native/Driver.c'],600,True)
        binary=out/'native/audit-driver';c.dump(out/'NATIVE_BINARY.json',{'file':'native/audit-driver','sha256':c.sha(binary),'bytes':binary.stat().st_size,'c_sha256':c.sha(out/'native/Driver.c'),'source_sha256':c.sha(c.ROOT/'Driver.lean'),'memory_bytes':4194304000})
        base=['lake','env','@EVIDENCE@/native/audit-driver']
        stage('types',base+['types','@EVIDENCE@'],3600)
        c.dump(out/'MODEL_BODIES.json',[{'name':n,'file':f'models/{i}.expr','sha256':c.sha(out/'models'/f'{i}.expr')}for i,n in enumerate(s['models'],1)])
        c.dump(out/'ROOT_TYPES.json',[{'name':n,'file':f'root-types/{i}.expr','sha256':c.sha(out/'root-types'/f'{i}.expr')}for i,n in enumerate(s['theorems']+s['models'],1)])
        kernel=stage('positive',base+['positive','@EVIDENCE@'],7200)
        for i,n in enumerate(s['controls'],1):stage('control-'+str(i),base+['control',str(i),'@EVIDENCE@'],3600)
        after=snapshot(rt,hosted);c.dump(out/'POST_AUDIT.json',after)
        if before!=after or math_before!=math_outputs():raise ValueError('Source/tool/protected/olean drift')
        for n in ['SCOPE.json','BINDING.json','SOURCE_HASHES.json','IMPORT_CLOSURE_HASHES.json','PROTECTED_OLD_INPUTS.json','CI_POLICY.json','R2_FRESH_RECEIPT.json','Driver.lean']:shutil.copyfile(c.ROOT/n,out/n)
        if hosted:checkout(os.environ['GITHUB_SHA'])
        match=re.search(r'EMPTY_KERNEL_REPLAY_PASS ([0-9]+) declarations',kernel)
        if not match:raise ValueError('Missing positive replay marker')
        c.dump(out/'SUMMARY.json',{'status':'PASS','execution_recipe':'native-v3','source_commit':s['source_commit'],'source_manifest_sha256':b['source_manifest_sha256'],'kernel_trust':0,'memory_bytes':4194304000,'data_only_import_is_not_replay':True,'mode':'HOSTED_FRESH_MATHEMATICS'if hosted else'LOCAL_REUSED_INDEPENDENT_R2_FULL_FRESH','mathematical_imports':427,'mathematical_olean_count':len(math_before),'r2_reuse_count':0 if hosted else 430,'theorems':len(s['theorems']),'models':len(s['models']),'controls':len(s['controls']),'kernel_declarations':int(match[1]),'producer_output':str(out.resolve()),'native_binary_sha256':c.sha(binary)})
        if hosted:c.dump(out/'CI_CONTEXT.json',{'commit':os.environ['GITHUB_SHA'],'run_id':os.environ['GITHUB_RUN_ID'],'run_attempt':os.environ['GITHUB_RUN_ATTEMPT'],'repository':os.environ['GITHUB_REPOSITORY'],'workflow':'.github/workflows/extraction-native-execution-v3.yml'})
        c.dump(out/'EVIDENCE_HASHES.json',c.file_manifest(out))
        from evidence import verify
        print(verify(out),flush=True);c.dump(rt['output']/'LATEST.json',{'directory':out.name,'summary_sha256':c.sha(out/'SUMMARY.json')})
        print('NATIVE_V3_FULL_TRUST0_STRICT_CONTROLS_PASS '+str(out),flush=True)

def main():
    p=argparse.ArgumentParser();p.add_argument('--check-only',action='store_true');p.add_argument('--run',action='store_true');p.add_argument('--github-actions',action='store_true');a=p.parse_args()
    if a.check_only==a.run:raise ValueError('Choose check-only or run')
    if a.check_only:
        s,b=c.binding();print({'status':'V3_BINDING_CHECK_ONLY_PASS_NOT_KERNEL','inputs':len(c.inventory()[0]),'theorems':len(s['theorems']),'models':len(s['models']),'controls':len(s['controls']),'memory_bytes':4194304000});return
    run(a.github_actions)
if __name__=='__main__':main()
