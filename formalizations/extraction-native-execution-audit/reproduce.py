#!/usr/bin/env python3
"""New independent native execution scope. Never invokes or modifies old audits."""
from pathlib import Path
import argparse,datetime,fcntl,os,re,resource,shutil,signal,subprocess,time
import common as c
import runtime

def check_checkout(commit):
    if c.git('rev-parse','HEAD').decode().strip()!=commit:raise ValueError('Not exact CI event commit')
    for name in list(c.readj(c.ROOT/'SOURCE_HASHES.json'))+[c.PREFIX+'/SOURCE_HASHES.json',c.PREFIX+'/BINDING.json']:
        if c.path_at(c.REPO,name).read_bytes()!=c.git('show',commit+':'+name):raise ValueError('Bound input differs from actual event Git blob')

def run(hosted=False):
    s,b=c.binding();rt=runtime.configure(hosted);deps=runtime.dependencies(rt,True)
    if hosted:check_checkout(os.environ['GITHUB_SHA'])
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ');out=rt['output']/('native-execution-'+stamp);out.mkdir(parents=True)
    def snapshot():
        c.binding();return {'source_commit':s['source_commit'],'source_inputs':c.inventory()[0],'protected_inputs':c.protected_inputs()['files'],'actual_executables':runtime.configure(hosted)['actual_executables'],'dependencies':runtime.dependencies(rt)}
    before=snapshot();c.dump(out/'PRE_AUDIT.json',before)
    records=[]
    def stage(name,cmd,seconds):
        actual=[x.replace('@EVIDENCE@',str(out.resolve()))for x in cmd];log=out/(name+'.log');start=time.monotonic()
        with log.open('w')as f:
            proc=subprocess.Popen(actual,cwd=c.ROOT,env=rt['env'],stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            try:code=proc.wait(timeout=seconds)
            except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait();code=124
        row={'stage':name,'command':cmd,'exit_code':code,'seconds':round(time.monotonic()-start,3),'log':log.name,'sha256':c.sha(log),'peak_children_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}
        records.append(row);c.dump(out/'STAGES.json',records);print(row,flush=True)
        if code:raise ValueError('Stage failed '+name+' '+str(log))
        return log.read_text()
    with open(rt['lock'],'a')as handle:
        print('Waiting for exclusive build lock; every strict Lean process is -j1 -M4000',flush=True);fcntl.flock(handle,fcntl.LOCK_EX)
        builds=[p/'.lake/build'for p in c.package_roots()]
        for p in builds:
            if p.is_symlink()or not p.resolve().is_relative_to(c.REPO.resolve())or p.parts[-2:]!=('.lake','build'):raise ValueError('Unsafe fresh owned output '+str(p))
        for p in builds:
            if p.exists():shutil.rmtree(p)
        for name in ['Check','Audit']:
            (out/(name+'Invocation.lean')).write_text((c.ROOT/(name+'.lean')).read_text().replace('@EVIDENCE@',str(out.resolve())))
        (out/'models').mkdir()
        stage('toolchain',['lake','env','lean','--version'],90)
        stage('build',['lake','build','NativeExecutionAudit','NativeExecutionVerification'],3600)
        types=stage('types',['lake','env','lean','-j1','-M4000','@EVIDENCE@/CheckInvocation.lean'],900)
        c.dump(out/'AXIOM_REPORT.json',c.parse_axioms(types,s['theorems']+s['models']))
        c.dump(out/'MODEL_BODIES.json',[{'name':name,'file':f'models/{i}.expr','sha256':c.sha(out/'models'/f'{i}.expr')}for i,name in enumerate(s['models'],1)])
        kernel=stage('kernel',['lake','env','lean','-j1','-M4000','@EVIDENCE@/AuditInvocation.lean'],10800)
        match=re.search(r'EMPTY_KERNEL_REPLAY_PASS ([0-9]+) declarations',kernel)
        if not match:raise ValueError('Missing positive replay marker')
        owned={}
        for build in builds:
            for p in sorted(build.rglob('*.olean')):
                if p.is_symlink():raise ValueError('Borrowed owned olean')
                owned[p.relative_to(c.REPO).as_posix()]=c.sha(p)
        c.dump(out/'OWNED_OLEANS.json',owned)
        after=snapshot();c.dump(out/'POST_AUDIT.json',after)
        if before!=after:raise ValueError('Source/protected/tool/dependency drift')
        if hosted:check_checkout(os.environ['GITHUB_SHA'])
        for n in ['SCOPE.json','BINDING.json','SOURCE_HASHES.json','IMPORT_CLOSURE_HASHES.json','PROTECTED_OLD_INPUTS.json','CI_POLICY.json']:shutil.copyfile(c.ROOT/n,out/n)
        c.dump(out/'SUMMARY.json',{'status':'PASS','source_commit':s['source_commit'],'source_manifest_sha256':b['source_manifest_sha256'],'kernel_trust':0,'fresh_owned_build':True,'memory_mb':4000,'producer_output':str(out.resolve()),'fresh_packages':[p.relative_to(c.REPO).as_posix()for p in c.package_roots()],'kernel_declarations':int(match[1]),'guard':rt['guard']})
        if hosted:c.dump(out/'CI_CONTEXT.json',{'commit':os.environ['GITHUB_SHA'],'run_id':os.environ['GITHUB_RUN_ID'],'run_attempt':os.environ['GITHUB_RUN_ATTEMPT'],'repository':os.environ['GITHUB_REPOSITORY'],'workflow':'.github/workflows/extraction-native-execution.yml'})
        c.dump(out/'EVIDENCE_HASHES.json',c.file_manifest(out))
        from evidence import verify
        print(verify(out),flush=True)
        c.dump(rt['output']/'LATEST.json',{'directory':out.name,'summary_sha256':c.sha(out/'SUMMARY.json')})
        print('NATIVE_EXECUTION_FULL_FRESH_TRUST0_STRICT_CONTROLS_PASS '+str(out),flush=True)

def main():
    p=argparse.ArgumentParser();p.add_argument('--freeze-source',action='store_true');p.add_argument('--check-only',action='store_true');p.add_argument('--fresh',action='store_true');p.add_argument('--github-actions',action='store_true');a=p.parse_args()
    if sum([a.freeze_source,a.check_only,a.fresh])!=1:raise ValueError('Choose freeze-source, check-only or fresh')
    if a.freeze_source:
        if a.github_actions or (c.ROOT/'BINDING.json').exists():raise ValueError('CI cannot freeze; existing scopes immutable')
        s=c.scope();inputs,closure,_=c.inventory()
        if closure!=c.readj(c.ROOT/'IMPORT_CLOSURE_HASHES.json'):raise ValueError('Import closure drift')
        c.protected_inputs();c.dump(c.ROOT/'SOURCE_HASHES.json',inputs)
        c.dump(c.ROOT/'BINDING.json',{'schema':1,'source_commit':s['source_commit'],'source_manifest_sha256':c.sha(c.ROOT/'SOURCE_HASHES.json'),'protected_manifest_sha256':c.sha(c.ROOT/'PROTECTED_OLD_INPUTS.json')})
        c.binding();print('NATIVE_EXECUTION_SOURCE_BINDING_CREATED_NOT_KERNEL_VERIFICATION');return
    if a.check_only:
        s,b=c.binding();print({'status':'NATIVE_EXECUTION_CHECK_ONLY_PASS','source_commit':s['source_commit'],'inputs':len(c.inventory()[0]),'theorems':len(s['theorems']),'models':len(s['models']),'controls':len(s['controls']),'kernel_run':False});return
    run(a.github_actions)

if __name__=='__main__':main()
