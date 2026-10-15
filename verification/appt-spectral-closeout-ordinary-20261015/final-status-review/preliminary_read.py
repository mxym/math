"""Read-only preliminary verification. Never signs the not-yet-frozen batch."""
from pathlib import Path
import datetime,hashlib,json,zipfile,subprocess

out=Path(__file__).resolve().parent
stage=out.with_name('spectral-closeout-publication')
public=stage/'public-sources'
sha=lambda b:hashlib.sha256(b).hexdigest()
now=datetime.datetime.now(datetime.timezone.utc)
tag=now.strftime('%Y%m%dT%H%M%S.%fZ')
snapshot=out/'preliminary-reads'/tag;snapshot.mkdir(parents=True)
raw=(stage/'PREPARED_SCOPES.json').read_bytes();prepared=json.loads(raw)
(snapshot/'PREPARED_SCOPES.json').write_bytes(raw)
log={'utc':now.isoformat(),'status':'WAITING_FOR_COMPLETE_CANDIDATE','not_a_final_pass':True,'prepared_scopes_sha256':sha(raw),'prepared_scopes':list(prepared),'candidate_exists':(stage/'FINAL_CANDIDATE_INPUTS.json').exists(),'reads':[],'checks':[],'findings':[],'actual_failures':[]}
for name in ['TASK_SCOPE.json','preflight.py','integrate.py','commit.py','transport.py','push.py','sync_origin.py','PIPELINE_ADAPTATION.json']:
    data=(stage/name).read_bytes();(snapshot/name).write_bytes(data)
    log['reads'].append({'path':str(stage/name),'sha256':sha(data),'bytes':len(data),'scope':'Full source text read before this preliminary run; not executed'})
originals={
 'S7':out.with_name('independent-rectangular-bulk-rigidity-review-20261015'),
 'S8':out.with_name('independent-coexistence-orientation-review-20261015'),
 'S9':out.with_name('independent-diverging-physical-reduction-review-20261015')}
owner_dirs={'S7':'phase-7-rectangular-bulk-rigidity','S8':'phase-8-coexistence-orientation','S9':'phase-9-diverging-physical-reduction'}
for scope,spec in prepared.items():
    if scope not in originals:continue
    src=public/spec['project']/spec['subdir']
    review=public/'appt-spectral-closeout-ordinary-20261015'/scope
    for rel,row in spec['source_files'].items():
        b=(src/rel).read_bytes();assert sha(b)==row['sha256'] and len(b)==row['bytes'],(scope,'source',rel)
    for rel,row in spec['public_review_files'].items():
        b=(review/rel).read_bytes();assert sha(b)==row['sha256'] and len(b)==row['bytes'],(scope,'review',rel)
        if rel.startswith('decision-supplement/'):
            prior=originals[scope].with_name(originals[scope].name+'-decision-supplement')/rel.split('/',1)[1]
        else:prior=originals[scope]/rel
        assert prior.read_bytes()==b,(scope,'not literal original copy',rel)
        if rel.endswith('.json'):json.loads(b)
    for rel,row in spec['explicit_public_omissions'].items():
        assert not (review/rel).exists(),(scope,'omission public',rel)
        b=(originals[scope]/rel).read_bytes();assert sha(b)==row['sha256'] and len(b)==row['bytes']
    paper=(src/'PAPER.md').read_bytes();manifest=(src/'AUTHOR_V1_MANIFEST.json').read_bytes()
    assert sha(paper)==spec['paper_sha256'] and sha(manifest)==spec['manifest_sha256']
    owner=Path('/mnt/d/math/tmp/breadth-tcs-20261015')/owner_dirs[scope]/spec['owner_archive_filename']
    assert sha(owner.read_bytes())==spec['archive_sha256']
    with zipfile.ZipFile(owner) as z:
        for item in z.infolist():
            if item.is_dir():continue
            prefix='worktree/research/breadth-tcs-20261015/'+owner_dirs[scope]+'/'
            assert item.filename.startswith(prefix),item.filename
            rel=item.filename[len(prefix):]
            assert z.read(item)==(src/rel).read_bytes(),(scope,'owner archive byte mismatch',rel)
        count=len(z.namelist())
    rmd=(review/'REVIEW.md').read_bytes();assert sha(rmd)==spec['review_md_sha256']
    bindname=spec.get('review_binding_filename','REPORT_BINDINGS.json')
    assert sha((review/bindname).read_bytes())==spec['review_binding_sha256']
    rjson=review/('decision-supplement/REVIEW.json' if scope=='S8' else 'REVIEW.json')
    assert sha(rjson.read_bytes())==spec['review_json_sha256']
    decision=json.loads(rjson.read_bytes());assert decision['status']==decision['decision']=='PASS'
    log['reads'].append({'path':str(review/'REVIEW.md'),'sha256':sha(rmd),'bytes':len(rmd),'scope':'Entire written report read; no new mathematical reassessment'})
    log['checks'].append({'scope':scope,'source_files':len(spec['source_files']),'literal_public_review_files':len(spec['public_review_files']),'explicit_omissions':len(spec['explicit_public_omissions']),'all_owner_archive_members_compared':count,'paper_sha256':sha(paper),'ordinary_mathematical_status':'PASS in exact original report','final_metadata_status':'not yet signed'})
    if scope=='S8' and 'FINAL_INTEGRITY.json' in spec['public_review_files']:
        log['findings'].append({'scope':'S8','kind':'preparation privacy classification','path':'FINAL_INTEGRITY.json','action':'Root notified: retain original unchanged privately and disclose omission from public copy; carries pure HN0 operational protection','not_a_math_failure':True})
root=Path('/home/mxym/math-appt-multiscale-20261013')
log['root_head']=subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD']).decode().strip()
log['root_status']=subprocess.check_output(['git','-C',str(root),'status','--porcelain']).decode()
log['base_indices']={}
for rel in ['README.md','README.en.md','RESEARCH.md']:
    b=(root/rel).read_bytes();log['base_indices'][rel]={'sha256':sha(b),'bytes':len(b),'lines':len(b.decode().splitlines())}
(snapshot/'PRELIMINARY_READ_LOG.json').write_text(json.dumps(log,indent=2)+'\n')
print(json.dumps({'status':log['status'],'checked':log['checks'],'candidate_exists':log['candidate_exists'],'read_log':str(snapshot/'PRELIMINARY_READ_LOG.json'),'root_head':log['root_head'],'base_index_sizes':log['base_indices'],'findings':log['findings']},indent=2))
