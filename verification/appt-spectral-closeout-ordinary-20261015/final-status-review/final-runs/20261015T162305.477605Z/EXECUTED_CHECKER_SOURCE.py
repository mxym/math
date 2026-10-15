"""Read-only final candidate verification; requires root's exact frozen SHA.

This program does not write a PASS or modify prepared sources. A separate final
report/binding step follows the complete human-readable metadata review.
"""
from pathlib import Path
import argparse,datetime,json,zipfile,subprocess
from review_helpers import *

args=argparse.ArgumentParser()
args.add_argument('--candidate-sha256',required=True)
arg=args.parse_args()
out=Path(__file__).resolve().parent;stage=out.with_name('spectral-closeout-publication')
root=Path('/home/mxym/math-appt-multiscale-20261013');public=stage/'public-sources'
now=datetime.datetime.now(datetime.timezone.utc)
run=out/'final-runs'/now.strftime('%Y%m%dT%H%M%S.%fZ');run.mkdir(parents=True)
result={'utc':now.isoformat(),'status':'IN_PROGRESS','metadata_review_only':True,'checks':[],'actual_failures':[]}
def save():
    (run/'VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
try:
    candidate_raw=(stage/'FINAL_CANDIDATE_INPUTS.json').read_bytes()
    assert sha(candidate_raw)==arg.candidate_sha256,('candidate SHA differs',sha(candidate_raw))
    candidate=json.loads(candidate_raw);(run/'FINAL_CANDIDATE_INPUTS.json').write_bytes(candidate_raw)
    assert candidate['status']=='PASS' and candidate['new_Lean'] is False and candidate['new_major_count']==0
    assert set(candidate['mathematical_scopes'])=={'S7','S8','S9','Rglob'}
    git=lambda *x:subprocess.check_output(['git','-C',str(root),*x])
    assert git('rev-parse','HEAD').decode().strip()==candidate['source_base']
    assert not git('status','--porcelain').strip()
    assert set(candidate['modified_indices'])=={'README.md','README.en.md','RESEARCH.md'}
    files={};lookup={}
    for rel,row in candidate['files'].items():
        p=stage/candidate['stage_file_lookup'][rel];b=p.read_bytes();exact_hash(b,row)
        files[rel]=row;lookup[rel]=p
        assert not rel.startswith(('formalizations/','.github/'))
        assert not any(x in p.parts for x in ['__pycache__','private-protection-evidence','pause-checkpoints'])
        assert not p.suffix in ['.pyc','.pdf','.html','.htm']
        assert p.name!='STATE.json'
        if p.suffix!='.zip':
            assert not any(token in b for token in [b'Message Type: NEW_TASK',b'<environment_context>',b'Sender: /root']),('raw conversation envelope in candidate',rel)
    result['checks'].append({'kind':'complete_candidate_literal_bytes','count':len(files),'candidate_sha256':sha(candidate_raw)})
    result['index_insertions']={}
    for rel,row in candidate['modified_indices'].items():
        old=(root/rel).read_bytes();new=lookup[rel].read_bytes()
        assert sha(old)==row['before_sha256'] and sha(new)==row['after_sha256']
        inserted=require_old_text_preserved(old.decode(),new.decode(),allow_phase_row_update=True)
        marker='appt-linear-phase-diagram-20261015/README.md'
        phase_before=[line for line in old.decode().splitlines() if marker in line][0]
        phase_after=[line for line in new.decode().splitlines() if marker in line][0]
        result['index_insertions'][rel]={'inserted':inserted,'phase_row_before':phase_before,'phase_row_after':phase_after}
        (run/(rel+'.before')).write_bytes(old)
        (run/(rel+'.after')).write_bytes(new)
    result['checks'].append({'kind':'all_old_URLs_classes_16_integrations_preserved','index_scope':'Exactly one identified existing phase row updated and two new rows inserted per index; every other old line literal'})
    prepared_raw=(stage/'PREPARED_SCOPES.json').read_bytes();prepared=json.loads(prepared_raw)
    (run/'PREPARED_SCOPES.json').write_bytes(prepared_raw)
    assert set(prepared)=={'S7','S8','S9','Rglob'}
    originals={
      'S7':out.with_name('independent-rectangular-bulk-rigidity-review-20261015'),
      'S8':out.with_name('independent-coexistence-orientation-review-20261015'),
      'S9':out.with_name('independent-diverging-physical-reduction-review-20261015'),
      'Rglob':out.with_name('independent-all-dimension-diverging-spectral-review-20261015')}
    result['scopes']={}
    for name,spec in prepared.items():
        src=public/spec['project']/spec['subdir'];review=public/'appt-spectral-closeout-ordinary-20261015'/name
        for rel,row in spec['source_files'].items():exact_hash((src/rel).read_bytes(),row)
        assert sha((src/'PAPER.md').read_bytes())==spec['paper_sha256']
        assert sha((src/'AUTHOR_V1_MANIFEST.json').read_bytes())==spec['manifest_sha256']
        ownermanifest=json.loads((src/'AUTHOR_V1_MANIFEST.json').read_bytes())
        ownerrows=ownermanifest['files']
        if isinstance(ownerrows,dict):ownerrows=[{'path':k,**(v if isinstance(v,dict) else {'sha256':v})} for k,v in ownerrows.items()]
        for row in ownerrows:exact_hash((src/row['path']).read_bytes(),row)
        for rel,row in spec['public_review_files'].items():
            b=(review/rel).read_bytes();exact_hash(b,row)
            prior=originals[name]/rel
            if name=='S8' and rel.startswith('decision-supplement/'):
                prior=originals[name].with_name(originals[name].name+'-decision-supplement')/rel.split('/',1)[1]
            assert b==prior.read_bytes(),(name,'original review copy differs',rel)
        for rel,row in spec['explicit_public_omissions'].items():
            assert not (review/rel).exists(),(name,'omitted evidence was public',rel)
            exact_hash((originals[name]/rel).read_bytes(),row)
        rmd=(review/'REVIEW.md').read_bytes();assert sha(rmd)==spec['review_md_sha256']
        bindname=spec.get('review_binding_filename','REPORT_BINDINGS.json')
        assert sha((review/bindname).read_bytes())==spec['review_binding_sha256']
        originalbindings=json.loads((originals[name]/bindname).read_bytes())['files']
        if isinstance(originalbindings,dict):originalbindings=[{'path':k,**(v if isinstance(v,dict) else {'sha256':v})} for k,v in originalbindings.items()]
        for row in originalbindings:exact_hash((originals[name]/row['path']).read_bytes(),row)
        assert (src/'INDEPENDENT_REVIEW.md').read_bytes()==rmd
        jsonpath=review/('decision-supplement/REVIEW.json' if name=='S8' else 'REVIEW.json')
        b=jsonpath.read_bytes();assert sha(b)==spec['review_json_sha256'];decision=json.loads(b)
        assert decision['status']==decision['decision']=='PASS'
        assert (src/'INDEPENDENT_REVIEW.json').read_bytes()==b
        if name=='S8':
            assert decision['transcription_only'] and not decision['new_mathematical_review']
            assert sha((review/'REVIEW.md').read_bytes())==decision['original_review']['sha256']
            assert (review/'REPORT_MANIFEST.json').exists()
            assert 'FINAL_INTEGRITY.json' in spec['explicit_public_omissions']
        if name=='S9':assert len([p for p in spec['explicit_public_omissions'] if p.startswith('pause-checkpoints/')])==3
        archives=[p for p in public.rglob('*.zip') if sha(p.read_bytes())==spec['archive_sha256']]
        if not archives:
            if name=='S8':archives=[Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-8-coexistence-orientation')/spec['owner_archive_filename']]
            else:archives=[originals[name]/'owner.zip']
        owner=archives[0];assert sha(owner.read_bytes())==spec['archive_sha256']
        with zipfile.ZipFile(owner) as z:
            candidates=[item.filename[:-len('PAPER.md')] for item in z.infolist() if item.filename.endswith('/PAPER.md') and sha(z.read(item))==spec['paper_sha256']]
            candidates=[prefix for prefix in candidates if set(z.namelist())=={prefix+rel for rel in spec['source_files']}]
            assert len(candidates)==1,(name,'owner paper prefix ambiguity',candidates)
            prefix=candidates[0]
            assert set(z.namelist())=={prefix+rel for rel in spec['source_files']},(name,'owner member set')
            for rel in spec['source_files']:assert z.read(prefix+rel)==(src/rel).read_bytes()
        result['scopes'][name]={'paper_sha256':spec['paper_sha256'],'owner_manifest_sha256':spec['manifest_sha256'],'owner_archive_sha256':spec['archive_sha256'],'source_count':len(spec['source_files']),'public_review_count':len(spec['public_review_files']),'explicit_omission_count':len(spec['explicit_public_omissions']),'review_md_sha256':sha(rmd),'review_json_sha256':sha(b),'binding_filename':bindname,'binding_sha256':spec['review_binding_sha256'],'scope':spec['scope']}
    checked=[];pending=[]
    allowed_pending={dest+'/FINAL_STATUS_BINDING.json' for dest in candidate['projects'].values()}
    for rel in candidate['canonical_documents']:
        text=lookup[rel].read_text()
        for target in links(text):
            local=local_target(rel,target)
            if local is None:continue
            dest,fragment=local
            if dest in allowed_pending:
                assert not fragment;pending.append({'source':rel,'target':dest});continue
            p=lookup.get(dest,root/dest)
            exists=p.exists() or any(k.startswith(dest.rstrip('/')+'/') for k in lookup)
            assert exists,('missing canonical target',rel,target,dest)
            if fragment and p.is_file() and p.suffix.lower()=='.md':require_anchor(p.read_text(),fragment)
            checked.append({'source':rel,'target':dest,'fragment':fragment})
    result['checks'].append({'kind':'canonical_paths_and_fragments','checked':len(checked),'permitted_pending_binding_links':len(pending)})
    result['canonical_links']=checked;result['pending_binding_links']=pending
    prior=json.loads((stage.parent/'entropy-spectrum-publication/TRANSPORT_BINDINGS.json').read_bytes())
    protected={rel:h for rel,h in prior['files'].items() if rel not in candidate['modified_indices']}
    for rel,h in protected.items():assert sha((root/rel).read_bytes())==h,('old protected source changed',rel)
    for ancestor in prior['parallel_ancestry']:
        subprocess.run(['git','-C',str(root),'merge-base','--is-ancestor',ancestor,candidate['source_base']],check=True,capture_output=True)
    result['checks'].append({'kind':'old_literal_protected_sources_and_parallel_main_ancestry','files':len(protected),'ancestry':prior['parallel_ancestry']})
    assert sha((stage/'FINAL_CANDIDATE_INPUTS.json').read_bytes())==arg.candidate_sha256
    assert (stage/'PREPARED_SCOPES.json').read_bytes()==prepared_raw
    result['status']='BYTE_AND_NAVIGATION_CHECKS_PASS_PENDING_WRITTEN_SCOPE_REVIEW'
    result['final_binding_signed']=False
except Exception as exc:
    result['status']='FAIL';result['actual_failures'].append({'type':type(exc).__name__,'message':str(exc)})
    save();raise
save()
print(json.dumps({'run':str(run),'status':result['status'],'bound_files':len(files),'scopes':list(result['scopes']),'canonical_links':len(checked),'final_binding_signed':False},indent=2))
