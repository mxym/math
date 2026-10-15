"""Write authorized P final metadata binding, without mathematics or plotting."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

HERE=Path(__file__).resolve().parent
PUB=HERE.parent/'growing-order-publication'
CANDIDATE=PUB/'public-sources'/'appt-growing-renyi-order-20261015'
INDEX=PUB/'index-candidates'

def info(path):
    data=path.read_bytes()
    item={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
    if path.suffix!='.png':item['lines']=len(data.splitlines())
    return item

manifest=json.loads((HERE/'INPUT_MANIFEST.json').read_text())
for relative,record in manifest['files'].items():
    assert info(HERE/relative)['sha256']==record['sha256'],relative
for path in CANDIDATE.rglob('*'):
    if path.is_file() and path.name!='FINAL_STATUS_BINDING.json':
        assert path.read_bytes()==(HERE/'snapshot/candidate'/path.relative_to(CANDIDATE)).read_bytes()
for path in INDEX.iterdir():
    if path.is_file():assert path.read_bytes()==(HERE/'snapshot/index'/path.name).read_bytes()
assert info(CANDIDATE/'README.md')['sha256']=='203f2f8f552aa2aaa88d40d6ffb05e78d51155e6f3e7e371415d7849bcbb4859'
checks=json.loads((HERE/'BYTE_CHECKS.json').read_text())
assert checks['decision']=='PASS' and checks['inverse_exact'] and checks['complete_forward_diff_exact']
assert not checks['mathematical_changes']
assert checks['literal_reports_maps_scripts_history_retained']
assert checks['source_versions_and_author_runs_retained_exactly']
assert checks['figure']['file_hashes_match']
top={p.name:info(p) for p in CANDIDATE.iterdir() if p.is_file() and p.name!='FINAL_STATUS_BINDING.json'}
record={
    'status':'PASS','decision':'PASS',
    'kind':'independent final P source-status README figure-caption and three-index byte binding',
    'reviewer':'internal AI agent /root/critical_entropy_review_resume_20261015',
    'bound_utc':datetime.now(timezone.utc).isoformat(),
    'new_mathematical_review':False,'mathematical_or_author_controls_rerun':False,
    'new_Lean_or_old_audit_expansion':False,'external_human_peer_review':False,
    'author_PAPER_mathematics_changed_for_metadata':False,
    'source_relation':{
        'reviewed_sha256':checks['reviewed_sha256'],'final_sha256':checks['final_sha256'],
        'status_diff_sha256':checks['status_diff_sha256'],'hunks':checks['status_hunks'],
        'inverse_recovers_exact_reviewed_bytes':True,'complete_forward_diff_exact':True,
        'new_mathematical_claims_or_quantifiers':False},
    'candidate_top_level_files':top,
    'literal_mathematical_REVIEW_md_json_preserved':True,
    'source_versions_and_all_three_author_control_runs_preserved':True,
    'original_false_fixed_D_P2_corollary_newly_certified':False,
    'README_scope':{
        'original_all_global_unitary_APPT':True,
        'uniform_formula_requires_D_and_alpha_both_to_infinity':True,
        'all_m_fixed_growing_oscillating_and_alpha_above_D':True,
        'quantitative_rate':'O(D^-1/2+log(alpha)/alpha), absolute',
        'finite_bounds_every_integer_2_le_m_le_n_and_every_real_alpha_ge_2':True,
        'finite_upper_error':'2m/(D-m)+(2log(alpha-1)+log48+2)/(alpha-1)',
        'exact_trace_one_lower_states_and_projection_rank_distinguished_from_full_density_rank':True,
        'fixed_m_c_zero_requires_D_and_alpha_growth_and_has_limit_logq':True,
        'm_growing_c_zero_allows_arbitrary_positive_order':True,
        'original_fixed_D_error_and_first_finite_PASS_failure_to_detect_it_disclosed':True,
        'range_correction_and_later_upper_strengthening_separately_identified':True,
        'no_exact_finite_extrema_relative_zero_accuracy_or_new_major_count':True},
    'metadata_history':{
        'versions':checks['README_versions'],
        'reviewer_initial_snapshot':info(HERE/'initial-snapshot/README.md'),
        'reviewer_middle_snapshot':info(HERE/'history/metadata-v2/README.md'),
        'full_v1_to_v2_diff':info(HERE/'history/README-v1-to-v2.diff'),
        'full_v2_to_final_diff':info(HERE/'history/README-v2-to-final.diff'),
        'resolved_findings':['raw lower operators explicitly normalized',
            'history distinguishes P2 range correction from later P0/P1 strengthening',
            'intermediate wording assigned rank k to full density; final explicitly assigns k to projection P and rank D to densities',
            'fixed-m c=0 convention explicitly retains alpha->infinity'],
        'unresolved_findings':[],'mathematical_PAPER_changes':False},
    'figure':{
        'script':info(CANDIDATE/'figure.py'),'provenance':info(CANDIDATE/'figures/PROVENANCE.json'),
        'PNG':info(CANDIDATE/'figures/growing-order-transition.png'),
        'recorded_PNG_hash_matches_actual_bytes':True,
        'formula_parameters_and_caption_read_and_consistent':True,
        'scope':'P2 limiting curves only, fixed m=2,3,5 and m->infinity, 900 c samples in [.08,6]',
        'D_and_alpha_grow_required_on_plot_caption':True,
        'plot_executed_by_reviewer':False,'PNG_visually_inspected_by_reviewer':False,
        'finite_quantum_extrema_or_code_to_render_execution_certified':False},
    'index_relations':checks['index_relations'],
    'index_ADDED_ROWS':info(INDEX/'ADDED_ROWS.md'),'index_author_BINDINGS':info(INDEX/'INDEX_BINDINGS.json'),
    'literature_screen':{'file':info(CANDIDATE/'LITERATURE_SCREEN.md'),
        'full_local_text_read':True,'scope':'bounded author abstract/metadata/query context, no priority certificate',
        'queries_replayed_or_external_papers_newly_read':False,
        'original_search_outcomes_independently_verified':False},
    'independent_final_report':info(HERE/'FINAL_STATUS_REVIEW.md'),
    'input_manifest':info(HERE/'INPUT_MANIFEST.json'),'exact_byte_checks':info(HERE/'BYTE_CHECKS.json'),
    'future_evidence_layout_verified':False,
    'planned_evidence_reference_only':'verification/appt-growing-order-ordinary-20261015/README.md',
    'future_links_copy_completeness_git_readback_or_transport_certified':False,
    'no_fetch_commit_push_submission_or_release_by_this_task':True
}
payload=(json.dumps(record,indent=2)+'\n').encode()
own=HERE/'FINAL_STATUS_BINDING.json';candidate=CANDIDATE/'FINAL_STATUS_BINDING.json'
own.write_bytes(payload);candidate.write_bytes(payload)
assert own.read_bytes()==candidate.read_bytes()==payload
result={'decision':'PASS','scope':'P final metadata, plot scope and three indices only',
    'binding':info(own),'report':info(HERE/'FINAL_STATUS_REVIEW.md'),
    'candidate_binding_identical':True,'controls_or_plot_rerun':False,
    'future_evidence_layout_verified':False}
(HERE/'FINAL_STATUS_REVIEW.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
