#!/usr/bin/env python3
"""Actual output-checker CLI controls using explicitly synthetic artifact fixtures.
No Lean compile or mathematical PASS is represented by these fixtures.
"""
from pathlib import Path
import argparse,json,subprocess,sys,tempfile
sys.dont_write_bytecode=True
from release_integrity import validated_snapshot,require,ReleaseIntegrityError
ROOT=Path(__file__).resolve().parents[1]
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();snap=validated_snapshot(ROOT);require(not a.output.resolve().is_relative_to(ROOT),'report outside release required')
    import output_integrity as oi
    cases=['baseline','missing_main_object','missing_log','owned_sidecar','helper_main','helper_sidecar','log','result_closure','extra_sidecar','omitted_manifest_path','duplicate_manifest_key','extra_run_file','wrong_release_identity','outer_rehashed_object','outer_rehashed_log','wrong_external_anchor','official_cache_content']
    rows=[]
    for case in cases:
        with tempfile.TemporaryDirectory(prefix='quadratic-output-control-') as td:
            w=Path(td);r=w/'run';r.mkdir();build={};helpers={};runs=[]
            def save(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
            for name,kind in [('Entry002','fresh'),('AuditCore','checks'),('EmptyKernelReplay','checks'),('StockAxiomSnapshot','checks')]:
                p=r/kind/(name+'.olean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(('SYNTHETIC '+name).encode());p.with_suffix('.olean.private').write_bytes(b'SYNTHETIC SIDECAR')
                log=r/'logs'/(name+'.log');log.parent.mkdir(exist_ok=True);log.write_text('Synthetic artifact-integrity fixture. No Lean execution.\n')
                row={'module':name,'output':p.relative_to(r).as_posix(),'output_sha256':oi.sha(p),'artifacts':oi.artifact_hashes(p),'source_sha256':oi.sha(ROOT/'audit/checks'/(name+'.lean')) if kind=='checks' else oi.sha(ROOT/'project/lean/Entry002.lean'),'log':log.relative_to(r).as_posix(),'log_sha256':oi.sha(log),'exit_code':0};(helpers if kind=='checks' else build)[name]=row;runs.append(row.copy())
            cache=w/'external/FakeOfficial.olean';cache.parent.mkdir();cache.write_bytes(b'SYNTHETIC OFFICIAL CACHE');link=r/'official/FakeOfficial.olean';link.parent.mkdir();link.symlink_to(cache)
            for name in oi.TERMINAL_RECORDS:save(r/name,{'fixture_only':True,'proof_verified':False})
            save(r/'BUILD_LEDGER.json',build);save(r/'HELPER_LEDGER.json',helpers);save(r/'RUNS.json',runs);save(r/'SELECTED_OFFICIAL.json',{'FakeOfficial':{'root':str(cache.parent),'source_sha256':'0'*64,'artifacts':{'.olean':oi.sha(cache)}}})
            results={n:oi.sha(r/n) for n in oi.TERMINAL_RECORDS if n.startswith('checks/')};save(r/'RESULT_BINDINGS.json',results);oi.seal_outputs(r,ROOT)
            obj=r/'fresh/Entry002.olean';log=r/'logs/Entry002.log';manifest=r/oi.MANIFEST
            if case=='missing_main_object':obj.unlink()
            if case=='missing_log':log.unlink()
            changes={'owned_sidecar':r/'fresh/Entry002.olean.private','helper_main':r/'checks/AuditCore.olean','helper_sidecar':r/'checks/AuditCore.olean.private','log':log,'result_closure':r/'checks/combined-owned-closure.json','outer_rehashed_object':obj,'outer_rehashed_log':log,'official_cache_content':cache}
            if case in changes:p=changes[case];p.write_bytes(p.read_bytes()+b'CHANGED')
            if case=='extra_sidecar':(r/'checks/AuditCore.olean.server').write_bytes(b'UNRECORDED SIDECAR')
            if case=='extra_run_file':(r/'unlisted.txt').write_text('unexpected')
            if case in ['omitted_manifest_path','wrong_release_identity','outer_rehashed_object','outer_rehashed_log','extra_sidecar']:
                m=json.loads(manifest.read_text())
                if case=='omitted_manifest_path':m['files'].pop('logs/Entry002.log')
                if case=='wrong_release_identity':m['release_identity']['SOURCE_MANIFEST.json']='0'*64
                if case in ['outer_rehashed_object','outer_rehashed_log','extra_sidecar']:m['files']=oi.snapshot(r)
                save(manifest,m)
            if case=='duplicate_manifest_key':manifest.write_text(manifest.read_text().replace('"format": 1,','"format": 1, "format": 1,',1))
            before={p.relative_to(r).as_posix():p.read_bytes() for p in r.rglob('*') if p.is_file() and not p.is_symlink()}
            for opt in [False,True]:
                command=[sys.executable,*(['-O'] if opt else []),'-B',str(ROOT/'scripts/verify_output.py'),'--output',str(r)]
                if case=='wrong_external_anchor':command+=['--expect-manifest-sha256','0'*64]
                p=subprocess.run(command,capture_output=True,text=True);text=p.stdout+p.stderr
                require((p.returncode==0 and 'RUN_OUTPUT_INTEGRITY_PASS' in text and '"proof_rechecked": false' in text) if case=='baseline' else (p.returncode!=0 and 'RELEASE_INTEGRITY:' in text),'production output control failed '+case+' '+text)
                after={p.relative_to(r).as_posix():p.read_bytes() for p in r.rglob('*') if p.is_file() and not p.is_symlink()};require(after==before,'read-only output verifier changed run artifacts')
                rows.append({'case':case,'optimized':opt,'passed':True,'fixture':'Synthetic artifact bindings only; no Lean or proof acceptance claim'})
    require(validated_snapshot(ROOT)==snap,'output controls changed release');a.output.write_text(json.dumps({'status':'PASS','normal_and_optimized':True,'real_production_cli':True,'proof_verification_performed':False,'cases':len(cases),'invocations':len(rows),'results':rows},indent=2)+'\n');print('OUTPUT_INTEGRITY_CONTROLS_PASS',len(rows))
if __name__=='__main__':
    try:main()
    except (ReleaseIntegrityError,OSError,ValueError,KeyError,RuntimeError) as e:print(str(e),file=sys.stderr);sys.exit(1)
