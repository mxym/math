#!/usr/bin/env python3
"""Fresh-source quadratic-orders Main reproduction; official cache allowed only by exact reference.
This program does not execute the author's old cache-bound verifier.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,os,re,shutil,subprocess,sys,time
sys.dont_write_bytecode=True
from release_integrity import validated_snapshot,require,ReleaseIntegrityError
ROOT=Path(__file__).resolve().parents[1]
ALLOWED={'propext','Classical.choice','Quot.sound'}
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig')

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def zipped(path):return json.loads(gzip.decompress(path.read_bytes()))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean-bin',type=Path,required=True)
    ap.add_argument('--dependency-project',type=Path,required=True)
    ap.add_argument('--extra-cache',action='append',type=Path,default=[])
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--max-new-bytes',type=int,default=1610612736,help='Maximum allocated bytes in this new run (default 1.5 GiB)')
    ap.add_argument('--minimum-free-bytes',type=int,default=786432000,help='Minimum remaining filesystem bytes (default 750 MiB)')
    ap.add_argument('--preflight-only',action='store_true',help='Check exact source/pin/cache planning only; no proof claim')
    a=ap.parse_args();snapshot=validated_snapshot(ROOT)
    import source_inventory as si
    import output_integrity as oi
    require(a.max_new_bytes>0 and a.minimum_free_bytes>0,'positive resource limits required')
    require(not a.output.is_symlink(),'output must not be a symlink')
    out=a.output.resolve();require(not out.exists(),'output must be nonexistent')
    require(not out.is_relative_to(ROOT),'output must be outside sealed package')
    lean=(a.lean_bin/'lean').resolve();require(lean.is_file(),'exact Lean binary missing')
    tool=lean.parent.parent;pk=a.dependency_project.resolve()/'.lake/packages';project=ROOT/'project'
    env=os.environ.copy();env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','');env['GIT_OPTIONAL_LOCKS']='0'
    # Remove environmental module injections before a subprocess is launched.
    for key in ['LEAN_SRC_PATH','LEAN_SYSROOT','LD_PRELOAD','LD_LIBRARY_PATH','DYLD_INSERT_LIBRARIES','DYLD_LIBRARY_PATH']:
        env.pop(key,None)
    env['LEAN_PATH']=str(tool/'lib/lean')
    def resource_guard():
        if not out.exists():return
        allocated=0
        for base,ds,fs in os.walk(out,followlinks=False):
            here=Path(base);allocated+=here.lstat().st_blocks*512
            for name in fs:allocated+=(here/name).lstat().st_blocks*512
            for name in ds:
                p=here/name
                if p.is_symlink():allocated+=p.lstat().st_blocks*512
        require(allocated<=a.max_new_bytes,'new-run allocation cap reached: '+str(allocated))
        require(shutil.disk_usage(out).free>=a.minimum_free_bytes,'minimum free-disk reserve reached')
    def command(argv,cwd=project/'lean',environment=None):
        resource_guard()
        p=subprocess.Popen(list(map(str,argv)),cwd=cwd,env=environment or env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        try:
            while True:
                try:
                    text,_=p.communicate(timeout=10);resource_guard();return p.returncode,text
                except subprocess.TimeoutExpired:resource_guard()
        except BaseException:
            p.terminate()
            try:p.communicate(timeout=10)
            except subprocess.TimeoutExpired:p.kill();p.communicate()
            raise
    toolref=json.loads((ROOT/'provenance/TOOLCHAIN_FILES_SHA256.json').read_text())
    for n,h in toolref['files'].items():require((tool/n).is_file() and sha(tool/n)==h,'toolchain file mismatch: '+n)
    code,version=command([lean,'--version']);require(code==0 and 'version 4.34.1,' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version,'compiler revision mismatch')
    packages=json.loads((project/'lean/lake-manifest.json').read_text())['packages'];pins={p['name']:p['rev'] for p in packages};require(len(pins)==9,'nine package pins required')
    for p in packages:
        d=pk/p['name'];code,text=command(['git','rev-parse','HEAD'],d);require(code==0 and text.strip()==p['rev'],'package revision mismatch: '+p['name'])
        code,text=command(['git','remote','get-url','origin'],d);require(code==0 and text.strip().removesuffix('.git')==p['url'].removesuffix('.git'),'package origin mismatch: '+p['name'])
        code,text=command(['git','status','--porcelain','--untracked-files=no'],d);require(code==0 and not text.strip(),'dirty tracked package: '+p['name'])
        code,text=command(['git','ls-files','--others','--exclude-standard','*.lean'],d);require(code==0 and not text.strip(),'untracked Lean source: '+p['name'])
    cft=json.loads((ROOT/'provenance/CFT_MODULES.json').read_text());require(len(cft)==len(set(cft))==995,'CFT source set differs')
    owned=si.owned_sources(project);expected=json.loads((ROOT/'provenance/OWNED_SOURCES.json').read_text())
    require(len(owned)==134 and {n:{'source':p.relative_to(ROOT).as_posix(),'sha256':sha(p)} for n,p in owned.items()}==expected,'owned source set differs')
    for n,p in owned.items():require(not re.search(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|sorryAx|implemented_by|extern)\b|debug\.skipKernelTC',si.source_code(p.read_text())),'owned source proof escape: '+n)
    graph=si.closure(project,pk,tool/'src/lean',pins,cft);prior=zipped(ROOT/'provenance/SOURCE_CLOSURE.json.gz')
    require(graph==prior,'complete recursive source closure differs')
    require({n for n,r in graph.items() if r['package']=='cft'}==set(cft),'actual CFT closure differs')
    providers=dict(si.providers(project,pk,tool/'src/lean',pins));providers['lean']=tool/'src/lean'
    refs=zipped(ROOT/'provenance/EXTERNAL_ARTIFACTS_REFERENCE.json.gz')['modules']
    require(set(refs)=={n for n,r in graph.items() if r['package'] not in {'main','bridges','cft'}},'official artifact reference coverage differs')
    roots=[pk/n/'.lake/build/lib/lean' for n in pins]+[p.resolve() for p in a.extra_cache]
    selected={};missing={}
    for n,rec in graph.items():
        if rec['package'] in {'main','bridges','cft'}:continue
        rel=Path(n.replace('.','/'));ref=refs[n]
        require(ref['package']==rec['package'] and ref['source_sha256']==rec['sha256'],'official artifact/source linkage mismatch: '+n)
        candidates=[tool/'lib/lean'] if rec['package']=='lean' else roots
        for root in candidates:
            if not (root/rel.with_suffix('.olean')).is_file():continue
            hashes={s:sha(root/rel.with_suffix(s)) for s in SUFFIXES if (root/rel.with_suffix(s)).is_file()}
            if hashes==ref['artifacts'] and '.olean' in hashes:
                selected[n]={'root':root,'hashes':hashes};break
        if n not in selected:
            require(rec['package']!='lean','official toolchain artifact mismatch: '+n)
            missing[n]=rec
    out.mkdir(parents=True);logs=out/'logs';logs.mkdir();fresh=out/'fresh';fresh.mkdir();overlay=out/'official';overlay.mkdir();checks=out/'checks';checks.mkdir()
    plan={'status':'PREFLIGHT_PASS','proof_verified':False,'source_modules':len(graph),'owned_modules':134,'CFT_modules':995,'official_cached_modules':len(selected),'official_to_build':sorted(missing),'compiler':version.strip(),'package_pins':pins,'owned_or_CFT_objects_reused':False}
    save(out/'PREFLIGHT.json',plan)
    save(out/'RUNTIME_INPUTS.json',{'release_identity':oi.release_identity(ROOT),'toolchain':str(tool),'dependency_project':str(a.dependency_project.resolve()),'extra_official_cache_roots':[str(p.resolve()) for p in a.extra_cache],'resource_limits':{'max_new_bytes':a.max_new_bytes,'minimum_free_bytes':a.minimum_free_bytes},'resume':False,'fresh_output_directory':True})
    if a.preflight_only:
        require(validated_snapshot(ROOT)==snapshot,'package changed during preflight')
        print('QUADRATIC_ORDERS_MAIN_PREFLIGHT_PASS; no compilation or theorem replay performed');return
    # Only hash-bound official modules are placed on this sparse overlay. No
    # external directory containing old owned/CFT objects is placed on LEAN_PATH.
    for n,row in selected.items():
        rel=Path(n.replace('.','/'))
        for suffix,h in row['hashes'].items():
            source=row['root']/rel.with_suffix(suffix);destination=overlay/rel.with_suffix(suffix)
            require(sha(source)==h,'selected cache changed: '+n);destination.parent.mkdir(parents=True,exist_ok=True);destination.symlink_to(source.resolve())
    env['LEAN_PATH']=os.pathsep.join(map(str,[fresh,overlay]))
    save(out/'SELECTED_OFFICIAL.json',{n:{'root':str(row['root'].resolve()),'source_sha256':graph[n]['sha256'],'package':graph[n]['package'],'artifacts':row['hashes']} for n,row in selected.items()})
    ledger={};helper_ledger={};runs=[];result_bindings={}
    def bind_results(*names):
        for name in names:result_bindings['checks/'+name]=sha(checks/name)
        save(out/'RESULT_BINDINGS.json',result_bindings)
    def clean(text):
        replacements=[(ROOT,'${RELEASE}'),(out,'${OUTPUT}'),(pk,'${PACKAGES}'),(tool,'${TOOLCHAIN}')]+[(p.resolve(),'${EXTRA_CACHE_'+str(i)+'}') for i,p in enumerate(a.extra_cache)]
        for path,label in sorted(replacements,key=lambda x:-len(str(x[0]))):text=text.replace(str(path),label)
        return text
    def run(argv,key,cwd,negative=None,environment=None):
        started=time.monotonic();code,text=command(argv,cwd,environment);text=clean(text);log=logs/(key+'.log');log.write_text(text)
        row={'name':key,'command':[clean(str(x)) for x in argv],'cwd':clean(str(cwd)),'exit_code':code,'seconds':round(time.monotonic()-started,3),'log':'logs/'+log.name,'log_sha256':sha(log)};runs.append(row);save(out/'RUNS.json',runs)
        if negative:
            require(code!=0 and negative.lower() in text.lower(),'intended negative did not reject: '+key)
            require(not any(x in text.lower() for x in ['unknown module','unknown identifier','unexpected token','unknown constant']),'negative fixture setup failure: '+key)
        else:require(code==0 and not re.search(r'\berror\s*:',text),'Lean failed: '+key+'\n'+text)
        require('declaration uses \'sorry\'' not in text and 'sorryAx' not in text,'sorry-based build: '+key)
        return row
    for n in si.topo(graph):
        rec=graph[n];kind=rec['package']
        if n in selected:continue
        require(kind!='lean','toolchain source should not be rebuilt')
        source=providers[kind]/rec['relative_source'];destination=(fresh if kind in {'main','bridges','cft'} else overlay)/Path(n.replace('.','/')).with_suffix('.olean')
        require(sha(source)==rec['sha256'],'source changed before compilation: '+n)
        require(not destination.exists() and not destination.is_symlink(),'fresh output already exists: '+n)
        for dep in rec['imports']:
            if graph[dep]['package'] in {'main','bridges','cft'}:require(dep in ledger and (fresh/Path(dep.replace('.','/')).with_suffix('.olean')).is_file(),'owned/CFT dependency not freshly compiled: '+dep)
        destination.parent.mkdir(parents=True,exist_ok=True)
        args=[lean,'-DautoImplicit=false']
        if kind not in {'main','bridges','cft'}:args+=['-DmaxSynthPendingDepth=3']
        args+=['-o',destination,source]
        print('BUILD '+n,flush=True);row=run(args,n,providers[kind])
        require(destination.is_file() and not destination.is_symlink() and sha(source)==rec['sha256'],'fresh output/source identity failure: '+n)
        row.update({'module':n,'package':kind,'source_sha256':rec['sha256'],'output':destination.relative_to(out).as_posix(),'output_sha256':sha(destination),'artifacts':oi.artifact_hashes(destination)});ledger[n]=row;save(out/'BUILD_LEDGER.json',ledger)
    require(set(owned)|set(cft)<=set(ledger),'fresh owned/CFT inventory incomplete')
    save(out/'BUILD_PASS.json',{'status':'PASS','fresh_main_modules':129,'fresh_bridges':5,'fresh_CFT':995,'fresh_official':len(missing),'official_cache_read_only':True,'owned_or_CFT_objects_reused':False})
    # Create the immutable stock baseline before any mathematical import.
    checkargs=[lean,'-R',ROOT/'audit/checks']
    stockenv=env.copy();stockenv['LEAN_PATH']=os.pathsep.join(map(str,[checks,overlay]))
    for n in ['StockAxiomSnapshot','AuditCore','EmptyKernelReplay']:
        row=run([*checkargs,'-o',checks/(n+'.olean'),ROOT/'audit/checks'/(n+'.lean')],'compile-tool.'+n,checks,environment=stockenv)
        row.update({'module':n,'source_sha256':sha(ROOT/'audit/checks'/(n+'.lean')),'output':'checks/'+n+'.olean','output_sha256':sha(checks/(n+'.olean')),'artifacts':oi.artifact_hashes(checks/(n+'.olean'))});helper_ledger[n]=row;save(out/'HELPER_LEDGER.json',helper_ledger)
    run([*checkargs,ROOT/'audit/checks/StockStandardAxioms.lean'],'StockStandardAxioms',checks,environment=stockenv)
    bind_results('stock-standard-axioms.json')
    env['LEAN_PATH']=os.pathsep.join(map(str,[checks,fresh,overlay]))
    for n in ['CheckLiteralStandardAxioms','ClosedWeakSmoke','NonvacuitySmoke','CheckCombinedOwned','EmptyKernelMini']:
        run([*checkargs,ROOT/'audit/checks'/(n+'.lean')],n,checks)
        if n=='CheckLiteralStandardAxioms':bind_results('literal-standard-axioms.json')
        if n=='CheckCombinedOwned':bind_results('combined-owned-inventory.json','combined-owned-closure.json')
        if n=='EmptyKernelMini':bind_results('EmptyKernelMini.json','EmptyKernelMini.json.closure.json')
    for n in ['NegativePromoteWeakSupply','NegativeOnlyMaximalOrders','NegativeOnlyNcard','NegativeMissingSupply']:
        run([*checkargs,ROOT/'audit/checks'/(n+'.lean')],n,checks,negative='type mismatch')
    run([*checkargs,ROOT/'audit/checks/EmptyKernelMiniCorrupt.lean'],'EmptyKernelMiniCorrupt',checks,negative='(kernel) declaration type mismatch')
    bind_results('EmptyKernelMiniCorrupt.json','EmptyKernelMiniCorrupt.json.closure.json')
    combined=json.loads((checks/'combined-owned-inventory.json').read_text());certificate=json.loads((ROOT/'audit/independent/FINAL_MATH_RESULT.json').read_text());record=zipped(ROOT/'audit/independent/combined-owned-inventory.json.gz')
    require(combined['status']=='PASS' and combined['stock_axiom_types_equal'] and combined['literal_no_premise_Main'],'combined declaration checks incomplete')
    require(set(combined['owned_modules'])==set(owned),'combined module scope differs')
    for key in ['inventory','nonlogical_generated_roots']:
        got=combined[key];want=record[key]
        require((sorted(got,key=lambda r:r['name'])==sorted(want,key=lambda r:r['name']) if key=='inventory' else sorted(got)==sorted(want)),'combined '+key+' differs')
    require(len(combined['inventory'])==2952 and sum(r['safe_root'] for r in combined['inventory'])==2906 and combined['full_owned_closure_count']==126696,'combined inventory or stored closure counts differ')
    require(set(combined['axioms'])==ALLOWED,'combined axiom set differs')
    require(json.loads((checks/'combined-owned-closure.json').read_text())==zipped(ROOT/'audit/independent/combined-owned-closure.json.gz'),'combined declaration closure differs')
    # Verify every physically resolved module, not just its namespace.
    paths=combined['resolved_paths'];require(len(paths)==len({r['module'] for r in paths}),'duplicate module resolution')
    require({r['module'] for r in paths}==set(graph)|{'AuditCore','EmptyKernelReplay','StockAxiomSnapshot'},'loaded module coverage differs from exact source graph plus three audit helpers')
    for row in paths:
        n=row['module'];path=Path(row['path']).resolve()
        if n in ledger:
            require(path==(out/ledger[n]['output']).resolve() and sha(path)==ledger[n]['output_sha256'],'loaded fresh output mismatch: '+n)
        elif n in selected:
            expected_path=selected[n]['root']/Path(n.replace('.','/')).with_suffix('.olean')
            require(path==expected_path.resolve() and sha(path)==selected[n]['hashes']['.olean'],'loaded official output mismatch: '+n)
        else:require(n in {'AuditCore','EmptyKernelReplay','StockAxiomSnapshot'} and path==(checks/(n+'.olean')).resolve(),'unbound loaded module: '+n)
    run([*checkargs,ROOT/'audit/checks/ReplayLiteralMain.lean'],'ReplayLiteralMain',checks)
    bind_results('literal-main-empty-kernel.json','literal-main-empty-kernel.json.closure.json')
    result=json.loads((checks/'literal-main-empty-kernel.json').read_text());closure=json.loads((checks/'literal-main-empty-kernel.json.closure.json').read_text())
    require(result['status']=='PASS' and result['roots']==['Entry002.arithmeticSupply_mainTarget_proved'] and result['initial_destination_constants']==0 and result['trust_level']==0 and not result['corrupted_proof_control'],'literal Main empty-kernel replay failed')
    require(result['source_closure_constants']==125368 and len(closure)==len(set(closure))==125368 and set(result['axioms'])==ALLOWED,'literal Main closure/axioms differ')
    require(closure==zipped(ROOT/'audit/independent/literal-main-empty-kernel.json.closure.json.gz'),'literal Main exact declaration closure differs')
    for name in ['Entry002.arithmeticSupply_mainTarget_of_primeIdealPNT','Entry002.arithmeticSupply_principalSupply_of_primeIdealPNT','Entry002.NumberFieldPrimeIdealPNTTarget','Entry002.PrincipalSplitPrimeSupplyTarget']:require(name not in closure,'open stronger endpoint entered Main closure: '+name)
    for n,row in ledger.items():require(oi.artifact_hashes(out/row['output'])==row['artifacts'] and sha(providers[graph[n]['package']]/graph[n]['relative_source'])==row['source_sha256'],'build input/output changed: '+n)
    for n,row in selected.items():
        for suffix,h in row['hashes'].items():require(sha(row['root']/Path(n.replace('.','/')).with_suffix(suffix))==h,'official input changed: '+n)
    require(si.closure(project,pk,tool/'src/lean',pins,cft)==graph,'terminal input source closure differs')
    for n,h in toolref['files'].items():require((tool/n).is_file() and sha(tool/n)==h,'terminal toolchain file mismatch: '+n)
    save(out/'RUNS.json',runs)
    require(json.loads((out/'BUILD_LEDGER.json').read_text())==ledger and json.loads((out/'HELPER_LEDGER.json').read_text())==helper_ledger,'stored build/helper ledgers changed')
    require(json.loads((out/'PREFLIGHT.json').read_text())==plan,'stored preflight changed')
    require(json.loads((out/'SELECTED_OFFICIAL.json').read_text())=={n:{'root':str(row['root'].resolve()),'source_sha256':graph[n]['sha256'],'package':graph[n]['package'],'artifacts':row['hashes']} for n,row in selected.items()},'stored official selection changed')
    oi.verify_bindings(out,ROOT)
    resource_guard()
    require(validated_snapshot(ROOT)==snapshot,'release bytes changed during verification')
    save(out/'FINAL_VERIFICATION.json',{'status':'PASS','exact_root':certificate['exact_root'],'exact_type':certificate['exact_type'],'fresh_main_modules':129,'fresh_bridges':5,'fresh_CFT_modules':995,'fresh_official_modules':len(missing),'owned_inventory':2952,'safe_logical_roots':2906,'partial_generated_nonproof_roots':sorted(combined['nonlogical_generated_roots']),'nonpartial_stored_closure':126696,'literal_Main_kernel_closure':125368,'initial_destination_constants':0,'trust_level':0,'axioms':sorted(ALLOWED),'source_bytes_unchanged':True,'official_cache_read_only':True})
    output_manifest_sha=oi.seal_outputs(out,ROOT)
    resource_guard()
    print('OUTPUT_MANIFEST_SHA256='+output_manifest_sha,flush=True)
    print('QUADRATIC_ORDERS_MAIN_PUBLIC_REPLAY_PASS',flush=True)

if __name__=='__main__':
    try:main()
    except (ReleaseIntegrityError,OSError,ValueError,KeyError,RuntimeError) as error:print(str(error),file=sys.stderr);sys.exit(1)
