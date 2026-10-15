"""Freeze the completed metadata decision, then install only four allowed bindings."""
from pathlib import Path
import datetime,hashlib,json,traceback,subprocess
from review_helpers import exact_hash,sha,local_target,links,require_anchor

out=Path(__file__).resolve().parent;stage=out.with_name('spectral-closeout-publication')
public=stage/'public-sources';root=Path('/home/mxym/math-appt-multiscale-20261013')
run=out/'final-runs/20261015T162305.477605Z'
candidate_sha='8589b1bdff22dac67e0419b578bbfde7a3c0319fe63d63b1d62bd994d1779c66'
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
def bind(p):
    b=p.read_bytes();return {'path':str(p.relative_to(out)) if p.is_relative_to(out) else str(p),'bytes':len(b),'sha256':sha(b)}
def write(name,obj):
    p=out/name;assert not p.exists(),name
    p.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
def check_candidate(candidate):
    assert sha((stage/'FINAL_CANDIDATE_INPUTS.json').read_bytes())==candidate_sha
    for rel,row in candidate['files'].items():exact_hash((stage/candidate['stage_file_lookup'][rel]).read_bytes(),row)

try:
    raw=(stage/'FINAL_CANDIDATE_INPUTS.json').read_bytes()
    assert sha(raw)==candidate_sha and len(raw)==193516
    candidate=json.loads(raw);check_candidate(candidate)
    prepared=json.loads((stage/'PREPARED_SCOPES.json').read_bytes())
    verification=json.loads((run/'VERIFICATION.json').read_bytes())
    assert verification['status']=='BYTE_AND_NAVIGATION_CHECKS_PASS_PENDING_WRITTEN_SCOPE_REVIEW' and not verification['actual_failures']
    assert len(candidate['files'])==383 and len(candidate['canonical_documents'])==10
    (run/'EXECUTED_CHECKER_SOURCE.py').write_bytes((out/'verify_complete_candidate.py').read_bytes())
    if not (run/'EXECUTED_HELPER_SOURCE.py').exists():(run/'EXECUTED_HELPER_SOURCE.py').write_bytes((out/'review_helpers.py').read_bytes())
    scope_projects={'appt-rectangular-bulk-rigidity-20261015':['S7'],'appt-coexistence-orientation-20261015':['S8'],'appt-diverging-spectral-reduction-20261015':['S9','Rglob']}
    for name,scopes in scope_projects.items():
        assert json.loads((public/name/'OWNER_SOURCE_BINDINGS.json').read_bytes())=={s:prepared[s] for s in scopes}
        index=json.loads((public/name/'REVIEW.json').read_bytes())
        assert index['status']==index['decision']=='PASS' and not index['new_Lean'] and index['new_major_count']==0
        assert index['scopes']=={s:{f:prepared[s][f] for f in ['paper_sha256','review_md_sha256','review_json_sha256','scope']} for s in scopes}
    for name,spec in prepared.items():
        assert json.loads((public/'appt-spectral-closeout-ordinary-20261015'/('PUBLIC_EVIDENCE_'+name+'.json')).read_bytes())==spec
    protect=sorted((out/'private-protection-evidence').glob('PROTECTION-*.json'))
    first=json.loads(protect[0].read_bytes());last=json.loads(protect[-1].read_bytes())
    assert first['Gaussian']==last['Gaussian'] and first['HN0_clock_sha256']==last['HN0_clock_sha256']
    assert first['formalizations_tree_oid']==last['formalizations_tree_oid']
    assert first['root_head']==last['root_head']==candidate['source_base'] and not last['root_status']
    assert not (out/'preliminary-reads').exists()
    negatives=json.loads((out/'HELPER_NEGATIVE_CONTROLS.json').read_bytes())
    assert len(negatives['actual_expected_assertion_failures'])==8 and negatives['unexpected_failures']==[]
    read_entries=[]
    for scope,spec in prepared.items():
        p=public/'appt-spectral-closeout-ordinary-20261015'/scope/'REVIEW.md'
        read_entries.append({'kind':'complete_original_mathematical_report','scope':scope,**bind(p),'semantic_scope':'Entire written report read; source scope, exclusions, attribution and failure provenance checked; no new mathematical audit'})
    for rel in candidate['canonical_documents']:
        p=stage/candidate['stage_file_lookup'][rel]
        read_entries.append({'kind':'current_canonical_document',**bind(p),'semantic_scope':'Current wrapper/status text read in full; for main indices all bytes compared and all changed rows/old exploration classes read'})
    guards=[stage/n for n in ['TASK_SCOPE.json','preflight.py','integrate.py','commit.py','transport.py','push.py','sync_origin.py','PIPELINE_ADAPTATION.json']]
    guards += [stage.parent/n for n in ['append_reviewed_spectral_closeout_scope.py','filter_spectral_closeout_private_operations.py','attach_spectral_closeout_final_review.py','prepare_spectral_closeout_pipeline.py','build_spectral_closeout_documents.py']]
    for p in guards:read_entries.append({'kind':'operational_guard_source',**bind(p),'semantic_scope':'Entire source read only; no mutating guard executed; raw snapshots remain private'})
    write('READING_LEDGER.json',{'utc':now,'scope':'Final metadata reading only','entries':read_entries,'complete_manifest_reads':['All 383 candidate inputs read and hash/size checked','All original owner/review manifest entries checked against actual files','All public copies and explicit private omissions checked'],'private_operational_materials':'Raw task/guard snapshots and full protection records under private-protection-evidence are explicitly excluded from public attachment','no_author_producer_or_mathematical_control_executed':True})
    runs=[]
    for p in sorted((out/'final-runs').glob('*/VERIFICATION.json')):
        item=json.loads(p.read_bytes())
        runs.append({'result':bind(p),'status':item['status'],'actual_failures':item['actual_failures'],'execution':'Actual independent read-only metadata checker execution, not a mathematical proof run'})
    write('RUN_LEDGER.json',{'utc':now,'metadata_runs':runs,'final_run_executed_source':bind(run/'EXECUTED_CHECKER_SOURCE.py'),'final_run_helper':bind(run/'EXECUTED_HELPER_SOURCE.py'),'negative_controls':bind(out/'HELPER_NEGATIVE_CONTROLS.json'),'prior_negative_run_preserved':bind(out/'helper-runs/INITIAL_HELPER_NEGATIVE_CONTROLS.json'),'expected_negative_assertion_failures':8,'unexpected_metadata_failures':[],'separate_original_math_failure_records':'Rglob two real reviewer capture failures and every original author/reviewer expected failure retained with original bytes; not rerun or reassigned here','protection_checks':'Read-only checks preserved privately; no full STATE or Gaussian source byte copied'})
    status={'status':'PASS','decision':'PASS','utc':now,'kind':'Final literal source/scope/status/index metadata review, separate from mathematical reviews','candidate':{'sha256':candidate_sha,'bytes':len(raw),'bound_inputs':383,'source_base':candidate['source_base']},'mathematical_scopes':verification['scopes'],'current_status_authority':'New FINAL_STATUS_BINDING.json for this exact candidate','historical_status_interpretation':{'prepared_pending_fields':'OWNER_SOURCE_BINDINGS and PUBLIC_EVIDENCE final_public_metadata_binding=pending are source-preparation snapshots at candidate freeze time, not the post-install current decision','old_pending_author_banners':'Retained historical state; source-specific later independent mathematical reports apply','S9_pause_INCOMPLETE':'Original private checkpoint preserved; not rewritten','S8_machine_json':'Separate frozen transcription of original written PASS and REPORT_MANIFEST; not a new mathematical review','other_manuscript_scopes':'No S5/S6/S7/S8/S9/Rglob scope is revoked or broadened by a historical pending phrase'},'index_changes':'Exactly one existing phase row updated and two new rows inserted per index; all other old lines and all old link occurrences preserved','old_exploration_classes':6,'previous_protected_public_files':4449,'parallel_main_ancestry_preserved':True,'canonical_documents':10,'existing_local_paths_and_fragments_checked':460,'root_path_count':452,'additional_self_fragments':8,'binding_links_closed_on_installation':7,'public_review_counts':{'S7':46,'S8':86,'S9':46,'Rglob':73},'explicit_omission_counts':{'S7':0,'S8':3,'S9':3,'Rglob':0},'mathematical_reaudit':False,'new_Lean':False,'new_audit_roots':0,'external_human_peer_review':False,'new_major_count':0,'privacy':'No Gaussian source bytes/full private STATE/raw third-party retrieval/conversation instructions published; private operational evidence explicitly excluded','Gaussian_dirty_files_hash_status_matched':27,'broader_research':'paused, clocks unchanged','expected_metadata_negative_assertions':8,'unexpected_metadata_failures':[],'installation':'Actual four-copy equality and final unchanged-candidate checks are recorded separately in INSTALLATION_RECEIPT.json','read_ledger':bind(out/'READING_LEDGER.json'),'run_ledger':bind(out/'RUN_LEDGER.json'),'report_md':bind(out/'FINAL_STATUS_REVIEW.md')}
    write('FINAL_STATUS_REVIEW.json',status)
    binding={'schema_version':1,'status':'PASS','decision':'PASS','utc':now,'kind':'Current final source/status/navigation binding; not new mathematics, Lean, human review or priority certification','source_base':candidate['source_base'],'candidate_sha256':candidate_sha,'candidate_bytes':len(raw),'candidate_inputs':383,'projects':candidate['projects'],'mathematical_scopes':verification['scopes'],'review_report':{'path':'final-status-review/FINAL_STATUS_REVIEW.md','sha256':sha((out/'FINAL_STATUS_REVIEW.md').read_bytes())},'review_decision':{'path':'final-status-review/FINAL_STATUS_REVIEW.json','sha256':sha((out/'FINAL_STATUS_REVIEW.json').read_bytes())},'authoritative_current_status':'PASS for the exact candidate. Historical preparation pending fields and author pending banners remain unchanged as snapshots, not current decisions.','historical_snapshot_fields':['OWNER_SOURCE_BINDINGS.*.final_public_metadata_binding','PUBLIC_EVIDENCE_*.final_public_metadata_binding'],'historical_pause_checkpoint':'S9 original INCOMPLETE pause record stays private and unchanged; later complete original review PASS is independently bound.','S8_decision_format':'Original REVIEW.md and REPORT_MANIFEST plus separate decision-supplement machine transcription, not an additional mathematical review.','scope_limits':{'S7':'m grows; fixed finite A, all 0<alpha<=A and alpha*n/m diverges','S8':'All positive c and nonnegative r scalar slices; actual-matrix transfer only original fixed-positive-c finite-r S window with all actual losses','S9':'m and finite real alpha both diverge; not the fixed-dimension extension','Rglob_physical':'Every dimension pair including fixed D, finite real alpha diverges','Rglob_benchmark':'Joint D and finite real alpha diverge, uniformly all dimension splits; infinite-order entropy is a separate endpoint'},'index_preservation':{'indices':candidate['modified_indices'],'one_identified_phase_row_updated_per_index':True,'two_new_rows_per_index':True,'all_other_old_lines_literal':True,'all_old_URL_occurrences_preserved':True,'old_six_classes_and_prior_integrations_retained':True},'canonical_navigation':{'documents':candidate['canonical_documents'],'existing_path_fragment_occurrences':460,'only_pending_then_closed_by_this_binding':7},'public_evidence':{'files_literal_to_originals':True,'review_files':{'S7':46,'S8':86,'S9':46,'Rglob':73},'explicit_omissions':{s:prepared[s]['explicit_public_omissions'] for s in prepared},'private_operational_evidence_excluded':True,'original_reports_and_failure_records_unchanged':True},'preservation':{'previous_public_files_hash_matched':4449,'parallel_main_ancestry_retained':True,'Gaussian_dirty_file_hash_status_matches':27,'Gaussian_source_or_full_STATE_published':False,'Lean_tree_unchanged':True,'broader_research_remains_paused':True},'new_Lean':False,'new_audit_roots':0,'new_major_count':0,'commit_push_submission_release_or_DOI_by_reviewer':False}
    write('FINAL_STATUS_BINDING.json',binding)
    data=(out/'FINAL_STATUS_BINDING.json').read_bytes();binding_hash=sha(data)
    before={str(p.relative_to(public)) for p in public.rglob('*') if p.is_file()}
    installs=[]
    for name,dest in candidate['projects'].items():
        target=public/name/'FINAL_STATUS_BINDING.json'
        assert not target.exists(),target
        assert target.parent.resolve().is_relative_to(public.resolve())
        target.write_bytes(data);assert target.read_bytes()==data
        installs.append({'path':str(target),'repo_path':dest+'/FINAL_STATUS_BINDING.json','sha256':binding_hash,'bytes':len(data)})
    after={str(p.relative_to(public)) for p in public.rglob('*') if p.is_file()}
    assert after-before=={name+'/FINAL_STATUS_BINDING.json' for name in candidate['projects']} and not before-after
    check_candidate(candidate)
    for item in verification['pending_binding_links']:
        assert item['target'].endswith('/FINAL_STATUS_BINDING.json')
        matching=[p for p in installs if p['repo_path']==item['target']]
        assert len(matching)==1 and Path(matching[0]['path']).read_bytes()==data
    assert subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD']).decode().strip()==candidate['source_base']
    assert not subprocess.check_output(['git','-C',str(root),'status','--porcelain']).strip()
    write('INSTALLATION_RECEIPT.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','binding_sha256':binding_hash,'binding_bytes':len(data),'exactly_four_allowed_public_additions':installs,'all_383_original_candidate_inputs_rechecked_unchanged':True,'all_seven_previously_pending_binding_links_closed':True,'main_unchanged':True,'no_other_stage_public_write':True,'live_jobs':[]})
    rows=[]
    for p in sorted(out.rglob('*')):
        if p.is_file() and p.name!='METADATA_REVIEW_MANIFEST.json':
            entry=bind(p)
            entry['public_copy_excluded']='private-protection-evidence' in p.parts or '__pycache__' in p.parts or p.suffix=='.pyc'
            if entry['public_copy_excluded']:entry['reason']='Pure private operational protection/task snapshots or generated cache; originals preserved'
            rows.append(entry)
    write('METADATA_REVIEW_MANIFEST.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','self_excluded':True,'files':rows,'private_omissions_explicit':True,'current_binding_sha256':binding_hash})
    print(json.dumps({'status':'PASS','final_report':bind(out/'FINAL_STATUS_REVIEW.md'),'final_decision':bind(out/'FINAL_STATUS_REVIEW.json'),'binding':bind(out/'FINAL_STATUS_BINDING.json'),'manifest':bind(out/'METADATA_REVIEW_MANIFEST.json'),'installed_identical_public_bindings':4,'candidate_inputs_unchanged':383,'main_unchanged':True,'live_jobs':[],'stopped':True},indent=2))
except Exception as exc:
    failure={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FAIL','type':type(exc).__name__,'message':str(exc),'traceback':traceback.format_exc()}
    p=out/('FINALIZATION_FAILURE-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')+'.json')
    p.write_text(json.dumps(failure,indent=2)+'\n')
    raise
