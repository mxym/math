from pathlib import Path
import datetime,hashlib,json

R=Path(__file__).resolve().parent;S=R/'candidate-snapshot'
STAGE=Path('/mnt/d/math/tmp/research-resume-20261015/entropy-spectrum-publication')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
dump=lambda p,x:p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
utc=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
capture=json.loads((R/'CANDIDATE_CAPTURE.json').read_text())
mf=json.loads((S/'FINAL_CANDIDATE_INPUTS.json').read_text())
success=json.loads((R/'runs/20261015T150526.205159Z/RESULT.json').read_text())
failed=json.loads((R/'runs/20261015T150422.448708Z/RESULT.json').read_text())
assert success['status']=='PASS' and failed['status']=='FAIL'
targets=[STAGE/'public-sources'/name/'FINAL_STATUS_BINDING.json' for name in [
 'appt-all-dimension-entropy-profile-20261015','appt-growing-order-rigidity-20261015',
 'appt-zero-order-losses-20261015','appt-entropy-spectrum-ordinary-20261015']]
assert all(not p.exists() for p in targets)
current={p.relative_to(STAGE).as_posix():{'sha256':sha(p),'bytes':p.stat().st_size}
         for p in sorted(STAGE.rglob('*')) if p.is_file()}
assert current==capture['files'],'Candidate stage changed after private capture'
dump(R/'STAGE_IMMUTABILITY_READBACK.json',{'status':'PASS','utc':utc(),'files_read_back':len(current),
 'captured_stage_files_unchanged':True,'no_new_binding_written_yet':True})

first=R/'runs/20261015T150422.448708Z'
(first/'ACTUAL_TOOL_STDERR.txt').write_text('''Traceback (most recent call last):
  File "/mnt/d/math/tmp/research-resume-20261015/independent-entropy-spectrum-final-binding-review-20261015/independent_metadata_checks.py", line 230, in <module>
    if __name__=='__main__':main()
  File "/mnt/d/math/tmp/research-resume-20261015/independent-entropy-spectrum-final-binding-review-20261015/independent_metadata_checks.py", line 222, in main
    try:perform(folder,result);result['status']='PASS'
  File "/mnt/d/math/tmp/research-resume-20261015/independent-entropy-spectrum-final-binding-review-20261015/independent_metadata_checks.py", line 60, in perform
    assert actual_files==set(x['source_files']),scope
AssertionError: X
''')
dump(R/'METADATA_FAILURE_HISTORY.json',{'status':'PRESERVED_ACTUAL_FAILURES','recorded_utc':utc(),
 'initial_read_path_failure':json.loads((R/'INITIAL_PATH_LOOKUP_FAILURE.json').read_text()),
 'initial_metadata_run':{'run':'runs/20261015T150422.448708Z','status':'FAIL','returncode':1,'tool_chunk_id':'f9e126',
                         'source_sha256':failed['source_sha256'],'actual_failure':failed['actual_failure'],
                         'diagnosis':'Reviewer omitted legitimate independent report copies in X/S5/S6 author destinations; corrected checker limits extras to those two files and verifies exact original bytes'},
 'subsequent_run':{'run':'runs/20261015T150526.205159Z','status':'PASS','source_sha256':success['source_sha256']},
 'candidate_revision_needed_or_made':False,'mathematical_controls_rerun':False})

read={'status':'COMPLETE_FOR_DECLARED_METADATA_SCOPE','utc':utc(),
 'canonical_documents':mf['canonical_documents'],
 'full_wrapper_texts':['Three new mathematics READMEs','Three STATUS files','Two-scope REVIEW index','Common evidence README','Complete attempt catalog README'],
 'root_indices':'Complete actual change blocks/supplied diffs read; all remaining bytes compared to immutable base and all current links parsed; no new audit of every old linked mathematics',
 'source_preparation':'Full record read; all owner and review byte mappings independently checked',
 'large_manifests':'Every hash/size/projection mapping algorithmically checked; not claimed as new full mathematical reads of 499 files',
 'UC0':'Full final status, clock and preservation record read; closure scalar status metadata inspected; four exact immutable Git blobs compared; subsidiary proofs not reviewed',
 'prior_mathematics':'Only four exact earlier source-bound independent decisions, with their original actual read limits; no reexecution',
 'current_navigation':success['navigation'],
 'third_party_raw_text':'One explicit X private omission retained privately; public-safe hash/URL/readscope ledger checked; no redistribution or external availability query'}
dump(R/'READ_LEDGER.json',read)
review={'status':'PASS','decision':'PASS','utc':utc(),
 'review_type':'Independent internal AI-agent final source/status/README/index/navigation binding; no new mathematical audit',
 'source_base':mf['source_base'],'input_manifest_sha256':sha(S/'FINAL_CANDIDATE_INPUTS.json'),
 'prior_mathematical_scopes_exact':mf['mathematical_scopes'],
 'mathematical_reports_reexecuted':False,'candidate_source_finding':[],
 'scope_preservation':{
  'X':'One total-D threshold all integer2<=m<=n and extendedalpha; fixed/growing/oscillatingm; SC theorem statement/context external input only; no effective threshold/finite optimizer/full spectral theorem',
  'S5':'m->infinity,alpha->infinity,o(m),alln>=m; weightedSUM of objectives; W2 only retained positive bulk weight; actual peak/middleJ/conventions retained',
  'S6':'Every fixed finiteC,alpha<=Cm eventually,alpha/m oscillation allowed,chi->infinity; momenth versus entropyh/chi and total tail retained',
  'Zloss':'m->infinity,alln>=m,every shrinking positive-alpha interval and zero-boundary oscillation; subtract8/three nonnegative losses; separate alpha0 rank indicator; no full empirical-law claim',
  'S7_and_later':'Excluded from this batch and final binding'},
 'owner_source_tree_checks':success['mathematical_scopes_source_bytes_only'],
 'public_review_projection':success['literal_public_review_projection'],
 'explicit_private_omission':success['private_omission'],
 'four_indices':success['four_indices'],'original_url_occurrences_preserved':True,
 'old_catalog_binding':success['old_catalog_binding_unchanged_and_not_destination'],
 'UC0':success['UC0'],'navigation':success['navigation'],
 'independent_metadata_execution':{'first_run':'20261015T150422.448708Z','first_status':'FAIL',
                                    'pass_run':'20261015T150526.205159Z','pass_source_sha256':success['source_sha256'],
                                    'all_actual_failures_preserved':'METADATA_FAILURE_HISTORY.json plus original run source/result/trace',
                                    'candidate_modified_to_pass':False},
 'new_binding_installation':'Only three mathematics candidate roots and common verification root; old catalog binding excluded',
 'future_transport_layout_or_commit_certified':False,'new_Lean_or_audit_scope':False,
 'author_mathematical_code_or_preflight_executed':False,'git_mutations':False,'network':False,
 'root_or_old_review_modified':False,'subagents_spawned':False,'submission_or_external_messages':False}
dump(R/'FINAL_STATUS_REVIEW.json',review)

# Report hashes precede binding creation, so no cyclic binding hash is claimed.
metadata_evidence=[]
for p in sorted(R.rglob('*')):
    if not p.is_file() or S in p.parents or (R/'base-index-copies') in p.parents:continue
    if p.name in ['FINAL_STATUS_BINDING.json','FINAL_BINDING_INSTALLATION.json']:continue
    metadata_evidence.append({'path':p.relative_to(R).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size})
binding={'status':'PASS','decision':'PASS','utc':utc(),
 'kind':'Final metadata/source/status/index binding of four previously independently reviewed ordinary mathematical scopes',
 'source_base':mf['source_base'],'prior_mathematical_scopes':mf['mathematical_scopes'],
 'current_review_outputs':{n:{'sha256':sha(R/n),'bytes':(R/n).stat().st_size}
                           for n in ['FINAL_STATUS_REVIEW.md','FINAL_STATUS_REVIEW.json','READ_LEDGER.json','METADATA_FAILURE_HISTORY.json']},
 'candidate_manifest_sha256':sha(S/'FINAL_CANDIDATE_INPUTS.json'),
 'prepared_repository_inputs':mf['files'],'repository_to_stage_mapping':mf['stage_file_lookup'],
 'additional_stage_artifact_binding':{k:v for k,v in capture['files'].items() if k not in set(mf['stage_file_lookup'].values())},
 'four_index_hashes':success['four_indices'],'public_evidence_projection':success['literal_public_review_projection'],
 'explicit_private_omission':success['private_omission'],'UC0_status_clock_only':success['UC0'],
 'navigation':success['navigation'],'metadata_review_evidence_files':metadata_evidence,
 'literal_owner_math_unchanged':True,'all_original_reviews_and_failures_preserved':True,
 'scope_limits':['No new mathematical coverage or rerun','No S7/S8/S9 or whole spectral-axis synthesis',
                 'UC0 only source/status/clock, subsidiary mathematics author-only and Frankl unresolved',
                 'No new Lean/Lake/kernel or old audit expansion','No complete external Song--Chen proof audit',
                 'No worldwide priority/external human peer-review certificate','No future copy/commit/layout/transport certification'],
 'self_reference_exclusions':['This FINAL_STATUS_BINDING.json and its identical four candidate copies',
                              'Subsequent FINAL_BINDING_INSTALLATION.json receipt',
                              'Any later copied contents under verification/appt-entropy-spectrum-ordinary-20261015/final-status-review/'],
 'authorized_binding_destinations':[str(p) for p in targets],
 'old_catalog_binding_unchanged':success['old_catalog_binding_unchanged_and_not_destination']}
raw=(json.dumps(binding,indent=2,ensure_ascii=False)+'\n').encode()
own=R/'FINAL_STATUS_BINDING.json'
with own.open('xb') as f:f.write(raw)
for p in targets:
    with p.open('xb') as f:f.write(raw)
assert all(p.read_bytes()==raw for p in [own]+targets)
for rel,x in current.items():
    p=STAGE/rel;assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],rel
dump(R/'FINAL_BINDING_INSTALLATION.json',{'status':'PASS','utc':utc(),'binding_sha256':sha(own),
 'identical_copies':[str(p) for p in [own]+targets],
 'original509_stage_files_unchanged':True,
 'no_old_catalog_binding_or_root_worktree_written':True,
 'scope':'Current private-stage installation/readback only; not future transport'})
print(json.dumps({'status':'PASS','binding_sha256':sha(own),'binding_bytes':len(raw),'identical_copies':len(targets)+1,
 'reports':{n:sha(R/n) for n in ['FINAL_STATUS_REVIEW.md','FINAL_STATUS_REVIEW.json']},
 'original_stage_files_read_back_unchanged':len(current)},indent=2))
