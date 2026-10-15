"""Issue the authorized four identical final metadata bindings, private-only
except for the three explicitly authorized candidate root JSON destinations.
No mathematical controls, author scripts, Lean or Git mutations are run.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
BASE=Path(__file__).resolve().parent
V2=BASE/'revised-four-index-v2'
STAGE=Path('/mnt/d/math/tmp/research-resume-20261015/scalar-phase-publication')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def record(p):return {'path':str(p.relative_to(BASE)),'sha256':sha(p),'bytes':p.stat().st_size}
utc=datetime.now(timezone.utc).isoformat()
M=json.loads((V2/'input-records/FINAL_CANDIDATE_INPUTS.json').read_text())
assert M['source_base']=='49f572d05df426fe9cfc36126dfea6accc6d5407' and len(M['files'])==239
assert (V2/'input-records/FINAL_CANDIDATE_INPUTS.json').read_bytes()==(STAGE/'FINAL_CANDIDATE_INPUTS.json').read_bytes()
for key,h in M['files'].items():
    if '/' not in key:current=STAGE/'index-candidates'/key
    else:
        name=next(n for n,prefix in M['new_projects'].items() if key.startswith(prefix+'/'))
        current=STAGE/'public-sources'/name/Path(key).relative_to(M['new_projects'][name])
    assert sha(current)==h and current.read_bytes()==(V2/'snapshot'/key).read_bytes(),key
for name in ['PREPARED_CANDIDATES.json','PARALLEL_BASE_BINDINGS.json','index-candidates/INDEX_BINDINGS.json']:
    assert (V2/'input-records'/name).read_bytes()==(STAGE/name).read_bytes()
index=json.loads((V2/'input-records/index-candidates/INDEX_BINDINGS.json').read_text())
assert len(index)==4
run_records=[]
for prefix in ['runs','revised-four-index-v2/runs']:
    for result in sorted((BASE/prefix).glob('*/RESULT.json')):
        data=json.loads(result.read_text())
        assert data['status'] in ['PASS','FAIL']
        assert sha(result.parent/'executed_script.py')==data['executed_script_sha256']
        rr={'result':record(result),'executed_script':record(result.parent/'executed_script.py'),
            'status':data['status'],'kind':data.get('kind'),'scope_groups':list(data['groups'])}
        for name in ['BASE_BLOB_READBACK.json','CANONICAL_LINKS.json','EXACT_SOLVED_DIFF.diff']:
            p=result.parent/name
            if p.exists():rr.setdefault('additional_records',[]).append(record(p))
        run_records.append(rr)
assert len(run_records)==6
assert [x['status'] for x in run_records]==['FAIL','PASS','PASS','PASS','PASS','PASS']
final_runs=[x for x in run_records if x['result']['path'].startswith('revised-four-index-v2/')]
assert len(final_runs)==3 and all(x['status']=='PASS' for x in final_runs)
geom='research/appt-linear-phase-geometry-20261015/'
math=[]
for scope,source,title in [
 ('pole-onset','PAPER.md','T v2 global pole onset and small-c coexistence; original sufficient c>=10'),
 ('ge-one','PURE_ENVELOPE_GE_ONE.md','D1 every real c>=1, every r>=0 exact scalar envelope and all ties'),
 ('bulk-onset','PAPER.md','B1--B19 all-c bulk threshold, small-c analytic coexistence and iterated physical consequences')]:
    d=geom+scope+'/'
    math.append({'scope':title,'prior_mathematical_decision':'PASS, separately completed full internal AI-agent read',
         'source':{'path':d+source,'sha256':M['files'][d+source]},
         'review_md':{'path':d+'REVIEW.md','sha256':M['files'][d+'REVIEW.md']},
         'review_json':{'path':d+'REVIEW.json','sha256':M['files'][d+'REVIEW.json']},
         'new_mathematical_rereview_or_control_execution_in_this_task':False})
assert [x['source']['sha256'] for x in math]==[
 '83c2240adfbca39009ff446504cc477f47684a0e5de1db52439862053bbcad79',
 'ad1a5aabca9d3fcf2e960cbf43bcf7cfbdfd232cc58b86bbaf355229656016a9',
 '3e1f67ee40b28af0b9de3a643488524fdb38f508d663f63e2ec82f7bc4322804']
review={
 'status':'PASS','decision':'PASS','utc':utc,
 'reviewer':'/root/critical_entropy_review_resume_20261015, separate internal AI agent',
 'kind':'final source/status/README/four-index review only; attempts catalog is metadata-only',
 'source_base':M['source_base'],'candidate_files':239,
 'full_project_READMEs_STATUS_catalog_and_all_changed_index_text_read':True,
 'existing_mathematical_reports':math,'combined_review_literal':{
      'md_sha256':M['files'][geom+'REVIEW.md'],'json_sha256':M['files'][geom+'REVIEW.json']},
 'actual_byte_checks':{'author_and_credited_files':64,'complete_independent_evidence_files':138,
      'current_manifest_files':239,'original_claim_rows_merged':16,
      'old_written_rows_literal_per_README':36,'canonical_file_directory_destinations':632,
      'new_heading_anchors':17,'old_proof_license_archive_footers_literal':True,
      'SOLVED_PROBLEMS_changed_lines_only':[1,3]},
 'four_indices':index,
 'catalog_disposition':{'source_status_decision':'PASS','mathematical_decision':'NOT A MATHEMATICAL REVIEW',
      'full_FEI_NPT_depolarizing_threshold_Quantum_PCP_not_promoted_to_solved':True,
      'SIC_existing_full_claim_collision_not_independently_certified':True,
      'three_owned_stage_summary_blobs_exact':True,'complete_raw_research_publication_claimed':False,
      'external_raw_PDF_in_payload':False},
 'scope_preservation':{
      'all_positive_c_thresholds_retained':True,'small_c_epsilon_non_effective':True,
      'full_scalar_argmax_and_zero_width_ties_retained':True,'c10_review_not_relabelled_c1':True,
      'fixed_c_then_c_to_zero_physical_limits_retained':True,
      'all_global_unitaries_original_density_domain_and_all_integer_n_ge_m_retained':True,
      'full_actual_spread_and_peak_losses_retained':True,'width_two_excluded_from_interior_peak_expansion':True,
      'integer_rank_and_trace_normalization_preserved':True,'no_intermediate_c_complete_diagram_claim':True,
      'old_V_all_order_value_credited':True},
 'old_candidate_and_real_history':{
      'three_index_232_file_snapshot_preserved':True,
      'frozen_record':record(BASE/'frozen-three-index-v1/FROZEN_INPUTS_AND_HISTORY.json'),
      'initial_inventory_checker_failure_preserved':True,
      'failure_cause':'reviewer incorrectly excluded historical FINAL_STATUS_BINDING basenames; fixed only the exact current project-root exclusion',
      'parent_reported_real_inbound_anchor_defect_preserved_and_repaired':True,
      'initial_451_link_scope_not_called_whole_repository_anchor_audit':True,
      'v2_initial_630_destination_PASS_not_relabelled_632':'two nested label brackets were separately included by the later actual 632-target execution',
      'historical_merge_map_after_hashes_match_intermediate_layout_before_new_APPT_row':True,
      'historical_pending_records_are_not_current_disposition':True},
 'parallel_base_byte_binding_only':{
      'manifest':record(V2/'input-records/PARALLEL_BASE_BINDINGS.json'),
      'native_committed_blobs_hashed':2120,'upstream_changed_paths':77,'ancestor_relation_verified':True,
      'single_prior_bound_coverage_change_path':'formalizations/appt-high-dimensional-review/ENTROPY_STABILITY_COVERAGE.md',
      'upstream_Lean_CI_kernel_semantics_certified':False,
      'dirty_Gaussian_preservation_provenance':'parent receipt only, not a new independent worktree audit'},
 'actual_metadata_executions':run_records,
 'no_new_mathematical_controls_or_author_program_execution':True,'no_Lean_Lake_kernel_execution':True,
 'no_git_mutation_fetch_push_or_submission':True,'no_author_math_or_root_worktree_edits':True,
 'not_external_human_peer_review_or_priority_certificate':True,'new_major_result_count':0,
 'no_future_copy_transport_layout_plot_or_publication_guarantee':True,
 'report_md_sha256':sha(BASE/'FINAL_STATUS_REVIEW.md'),
 'binding_and_report_self_reference_exclusions_explicit':True}
write(BASE/'FINAL_STATUS_REVIEW.json',review)

root_binding_paths=[prefix+'/FINAL_STATUS_BINDING.json' for prefix in M['new_projects'].values()]
binding={
 'status':'PASS','decision':'PASS','utc':utc,
 'kind':'exact final ordinary source/status/navigation binding; not a new mathematical theorem review',
 'reviewer':review['reviewer'],'source_base':M['source_base'],
 'source_base_role':'current index/integration base; frozen author theorem dependencies retain their original c4e commit bindings',
 'projects':M['new_projects'],'current_candidate_file_count':239,'files':M['files'],
 'input_records':[record(V2/'input-records'/name) for name in [
      'FINAL_CANDIDATE_INPUTS.json','PREPARED_CANDIDATES.json','PARALLEL_BASE_BINDINGS.json','index-candidates/INDEX_BINDINGS.json']],
 'four_index_bindings':index,'three_separate_mathematical_reads':math,
 'combined_report':{'md_sha256':M['files'][geom+'REVIEW.md'],'json_sha256':M['files'][geom+'REVIEW.json'],
     'role':'literal index of three actual separate reads, not automatic coverage or a new proof'},
 'metadata_read_scope':{'three_project_READMEs_and_geometry_STATUS_full_read':True,
     'all_changed_index_text_and_16_source_scope_mappings_read':True,
     'catalog_and_three_owned_stage_summaries_full_read_as_metadata':True,
     'old_claimed_independent_headings_removed_and_all_rows_merged':True,
     '36_old_written_rows_each_and_copyright_original_audit_footers_literal':True,
     'actual_632_canonical_target_checks_and_17_new_anchor_checks':True,
     'SOLVED_PROBLEMS_only_title_and_navigation_changed':True},
 'catalog_approval_kind':'source/status metadata only; no full mathematical REVIEW or promotion to solved',
 'exact_source_and_scope_policy':review['scope_preservation'],
 'actual_metadata_execution_records':run_records,
 'history_preservation':review['old_candidate_and_real_history'],
 'parallel_upstream_provenance_only':review['parallel_base_byte_binding_only'],
 'explicit_exclusions':{
     'current_self_binding_exact_paths':root_binding_paths+['private-output/FINAL_STATUS_BINDING.json'],
     'final_new_review_reports_and_separate_hash_record':['FINAL_STATUS_REVIEW.md','FINAL_STATUS_REVIEW.json','REPORT_SHA256.json'],
     'later_self_review_copy_subtree':'verification/appt-linear-phase-ordinary-20261015/final-status-review/**',
     'nested_historical_BINDING_files_are_excluded':False,
     'exclusion_reason':'avoid self-reference and future-copy circularity; this does not guarantee any later evidence transport or layout',
     'operational_pipeline_scripts': 'not executed or approved by this binding; historical scripts in the input manifest are bound as bytes only',
     'new_mathematical_review_formal_audit_external_human_review_priority_or_major_count':True,
     'external_URL_liveness_fulltext_priority_or_full_repository_historical_inbound_anchor_audit':True},
 'new_Lean_executions':0,'new_audit_roots':0,'new_major_count':0,
 'future_transport_commit_push_publication_CI_layout_or_figure_certification':False,
 'same_bytes_required_at_all_four_authorized_destinations':True}
payload=(json.dumps(binding,indent=2,ensure_ascii=False)+'\n').encode()
destinations=[BASE/'FINAL_STATUS_BINDING.json']+[STAGE/'public-sources'/name/'FINAL_STATUS_BINDING.json' for name in M['new_projects']]
assert all(not p.exists() for p in destinations),'Do not overwrite an existing final binding'
for p in destinations:p.write_bytes(payload)
assert all(p.read_bytes()==payload for p in destinations)
report_hashes={'status':'PASS','decision':'PASS','source_base':M['source_base'],
   'final_binding_sha256':hashlib.sha256(payload).hexdigest(),
   'final_binding_bytes':len(payload),'binding_destinations':[str(p) for p in destinations],
   'reports':[record(BASE/'FINAL_STATUS_REVIEW.md'),record(BASE/'FINAL_STATUS_REVIEW.json')],
   'self_hash_record_excluded_from_binding':True,'binding_copies_byte_identical':True}
write(BASE/'REPORT_SHA256.json',report_hashes)
print(json.dumps(report_hashes,indent=2,ensure_ascii=False))
