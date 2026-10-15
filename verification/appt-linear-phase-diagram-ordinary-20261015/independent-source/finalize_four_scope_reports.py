from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
BASE=Path(__file__).resolve().parent
G=BASE/'global-mixed'
SRC=G/'owner-zip-snapshot/worktree/research/breadth-tcs-20261015/phase-4-depth-appt'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rec(p):return {'path':str(p.relative_to(BASE)),'sha256':sha(p),'bytes':p.stat().st_size}
def write(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
utc=datetime.now(timezone.utc).isoformat()
owner=json.loads((G/'INPUT_OWNER_ZIP.json').read_text());assert len(owner['files'])==42
assert sha(G/'global-mixed-owner-dirty-20261015T124715Z.zip')==owner['owner_archive_sha256']
for x in owner['files']:assert sha(G/'owner-zip-snapshot'/x['path'])==x['sha256']
three=json.loads((BASE/'THREE_SCOPE_REPORT_BINDINGS.json').read_text())
assert three['status']==three['decision']=='PASS'
for scope in three['reports']:
 for key in ['review_md','review_json']:
  assert sha(BASE/scope[key]['path'])==scope[key]['sha256']
for key in ['combined_md','combined_json']:assert sha(BASE/three[key]['path'])==three[key]['sha256']
expected={
 'GLOBAL_MIXED_PHASE.md':'5712392f1e74b9c1d1999bacb42cf21f0d0fac3c3cd963954774972dd487c4cb',
 'global_mixed_turn_certificate.py':'f7934ad3a2c0581754f443fb51d58dbf58cb27da0aaa03be589baffe375bfdce',
 'GLOBAL_MIXED_TURN_CERTIFICATE.json':'4570686e01edda036ea7c3eafbff6fe1719730eb9d72a3059a2e9f269f1f0cbb',
 'replay_global_turn_certificate.py':'7a95738b0fab0c3b1ca43f953e6b6505357b21b23c42ce936d1c20ae63e2e87c',
 'critical_exact_intervals.py':'78ab0341d6079ceedb7be01abc9eba8608d50df0ad2136fa53b554a547c6ce1c'}
for name,h in expected.items():assert sha(SRC/name)==h
runs=[]
for p in sorted((G/'runs').glob('*/RESULT.json')):
 d=json.loads(p.read_text());assert d['status']=='PASS'
 child=d.get('expected_actual_child_failures',0)
 runs.append({'result':rec(p),'kind':d['kind'],'status':d['status'],'expected_real_child_failures':child})
assert len(runs)==3
replay=json.loads((G/'runs/20261015T130646.989405Z/RESULT.json').read_text())
ind=json.loads((G/'runs/20261015T131155.884755Z/RESULT.json').read_text())
bad=json.loads((G/'runs/20261015T131258.239438Z/RESULT.json').read_text())
assert replay['original_certificate_bytes_and_UTC_unchanged'] and bad['expected_actual_child_failures']==4
assert ind['groups']['symbolic_regular_charts']['exact_symbolic_identities']==10
report={'status':'PASS','decision':'PASS','utc':utc,
 'reviewer':'/root/critical_entropy_review_resume_20261015, separate internal AI agent',
 'scope':'fourth scope: full scalar all-c/all-r phase diagram, unique nondegenerate mixed phase, global analytic coexistence boundaries, original fixed-c physical transfer',
 'kind':'complete ordinary mathematical/code read, actual private authored replay and new independent auxiliary controls',
 'source':rec(SRC/'GLOBAL_MIXED_PHASE.md'),'source_lines':485,'report':rec(G/'REVIEW.md'),
 'owner_archive':{'path':'global-mixed/global-mixed-owner-dirty-20261015T124715Z.zip','sha256':owner['owner_archive_sha256']},
 'owner_manifest':rec(SRC/'GLOBAL_MIXED_V1_MANIFEST.json'),'input_manifest':rec(G/'INPUT_OWNER_ZIP.json'),
 'exact_engine_certificate_inputs':[rec(SRC/name) for name in expected if name!='GLOBAL_MIXED_PHASE.md'],
 'prior_three_scopes_separately_completed':three['reports'],'prior_report_bytes_unchanged':True,
 'old_C1_PASS_not_automatically_extended':True,'whole_new_manuscript_engine_replayer_read':True,
 'mathematical_gates':[
   'conditional h optimum with explicit lower clamp, one switching k_a and matching strictly negative derivative there',
   'all stationary roots are h-interior by exact R_stat/C=s/(s+a_prime)<1',
   'exact R_stat derivative sign M, regular T right layer and middle M/delta charts',
   'removable E_p derivative series at K=0 with positive A and rigorously bounded degree64 tails',
   '74 whole-box leaves, strict six-stage signs and all seven cap exclusions',
   'cap-intersection over-encloses admissible points while explicit v remains; no dropped near-zero K or width region',
   'exact two simple turns on every 0<K<=13/25 imply at most one interior local maximum at every r',
   'turn-level horizontal stationary points are monotone contacts rather than extra extrema',
   'strict middle-root Schur complement yields negative-definite scalar Hessian',
   'positive attained U minimum and continuous compact Q maximum give exact threshold criteria and all ties',
   'unique analytic thresholds patch over 0<c<c_star and link to separately reviewed critical triple point',
   'original actual complex all-global-unitary APPT nearoptimizers retain full argmax distance, J and actual peak loss'],
 'actual_replay':{'run':runs[0]['result']['path'],'kind':'unmodified authored code executed by reviewer in private scratch, not new independent interval engine',
    'generator_executed':False,'total_leaves':74,'stage_leaf_counts':[35,1,28,5,1,4],
    'middle_cap_exclusions':7,'certificate_bytes_and_original_UTC_unchanged':True},
 'independent_auxiliary':{'run':'global-mixed/runs/20261015T131155.884755Z',
    'author_modules_imported':False,'symbolic_identities':10,'exact_prefix_coefficient_checks':390,
    'independent_rational_cell_or_segment_count':201,'exact_cap_product_minima':['135/256','147/256','147/256','135/256','75/128','9/16','9/16'],
    'cell_checks_are_partition_proof_not_function_sign_sampling':True,
    'expected_assertion_counterexamples':4,'printed_beta_one_at_tiny_K_is_rounding_only':True},
 'actual_adversarial_replay_failures':{'run':'global-mixed/runs/20261015T131258.239438Z','count':4,
    'cases':['equal-area gap/overlap','false outside-cap box','omitted zero/near-zero K','forged strict turn derivative'],
    'all_nonzero_exits_and_AssertionError_tracebacks_retained':True,'original_source_changed':False},
 'actual_executions':runs,'unexpected_execution_failures':[],'unresolved_mathematical_findings':[],
 'author_source_corrections_required':False,
 'physical_scope':{'all_original_complex_PSD_trace_one_APPT':True,'every_global_unitary':True,
    'm_to_infinity_and_all_integer_n_ge_m':True,'alpha_gt_one_alpha_over_m_fixed_c_positive':True,
    'finite_peak_ratio_r_ge_zero':True,'complete_scalar_argmax_losses_J_and_actual_peak_retained':True,
    'all_integer_rank_attainment_from_credited_S':True,'one_two_three_body_laws_in_corresponding_phases':True,
    'uniform_simultaneous_c_m_to_zero_physical_claim':False,'unconditional_side_phase_selection_at_vanishing_gap':False,
    'width_two_interior_peak_expansion':False,'finite_exact_spectra_or_eigenbasis_uniqueness':False},
 'no_Lean_or_kernel_execution':True,'no_root_or_author_writes':True,'no_subagent_commit_push_submission':True,
 'external_human_review_priority_or_new_major_certificate':False,'future_status_index_transport_binding':'separate task'}
write(G/'REVIEW.json',report)
summary={'scope':report['scope'],'source_sha256':expected['GLOBAL_MIXED_PHASE.md'],'decision':'PASS',
 'review_md':rec(G/'REVIEW.md'),'review_json':rec(G/'REVIEW.json')}
all_scopes=three['reports']+[summary]
combined={'status':'PASS','decision':'PASS','utc':utc,
 'kind':'index of four exact separately completed internal AI-agent ordinary mathematical reads',
 'scopes':all_scopes,'earlier_three_reports_and_three_scope_combined_records_unchanged':True,
 'prior_PENDING_phrases_role':'historical disposition before fourth full read; current fourth decision is given by global-mixed/REVIEW',
 'overall_completed_scalar_scope':'all real c>0,r>=0 scalar phase and full argmax, no mixed-c islands, unique nondegenerate mixed branch, two analytic coexistence curves and unique triple point',
 'physical_scope':'original all-global-unitary APPT fixed-positive-c finite-r linear-order window with full J/actual peak loss; complete corresponding body-law alternatives and ties',
 'not_claimed':['new all-order optimized entropy value closure','all-order or finite-dimensional spectral classification',
    'new simultaneous c_m->0 physical uniformity','unconditional one-sided selection at vanishing phase gap',
    'Lean verification','external human peer review','priority certification','new major count','future publication layout or transport'],
 'old_C1_PASS_not_extended_without_review':True,'both_original_certificates_and_their_UTC_preserved':True,
 'actual_authored_replays':2,'new_independent_auxiliary_program_runs':2,'actual_expected_negative_replay_children':8,
 'unexpected_execution_failures':[],'unresolved_mathematical_findings':[],
 'final_metadata_README_index_binding':'not done by these mathematical decisions; requires separate precise final candidates'}
write(BASE/'COMBINED_REVIEW_FOUR.json',combined)
md='# Four separate independent ordinary mathematical reads\n\nDecision: **PASS for all four exact scopes below.** Every new manuscript received its own full mathematical read. Earlier C1 or three-scope PASS was not automatically extended.\n\n'
for x in all_scopes:
 md+=f"- **{x['scope']}**. Source SHA-256 `{x['source_sha256']}`. Decision PASS. Full report `{x['review_md']['path']}` SHA `{x['review_md']['sha256']}`; structured report `{x['review_json']['path']}` SHA `{x['review_json']['sha256']}`.\n"
md+='\nThe fourth read closes the earlier reports\' explicitly pending global mixed-branch question. Those original reports and COMBINED_REVIEW_THREE remain unchanged as historical scope records. The current mathematical disposition is this four-scope index and the four linked exact-source reports.\n\nThe combined result classifies the full scalar argmax for every real c>0,r>=0: one strict mixed-c interval, one nondegenerate mixed phase, exactly two analytic coexistence curves, and a unique interior triple point with certified 0.2595<c_star<0.26. The actual-matrix transfer retains the original fixed-positive-c finite-r linear-order window, all-global-unitary complex APPT, full scalar-argmax distance, J and actual peak losses and all ties/attainment. It is not a new all-order value closure or finite exact optimizer theorem. No simultaneous c_m->0 physical uniformity or unqualified side selection at a shrinking gap is asserted.\n\nBoth immutable owner ZIPs and both exact certificates/UTC are preserved. Actual unchanged authored-code replays, new independent symbolic/coverage controls and eight real private negative replay failures are recorded distinctly. No new independent interval engine or Lean kernel verification is claimed. There were no unexpected execution failures or required mathematical source corrections. No root/author source, old published review, existing formal audit, repository publication or external communication was changed by this reviewer.\n\nExternal human peer review, historical priority, new major-result counts and future metadata/README/index/transport correctness are outside these decisions. Final publication-source binding remains a separate task.\n'
(BASE/'COMBINED_REVIEW_FOUR.md').write_text(md)
write(BASE/'FOUR_SCOPE_REPORT_BINDINGS.json',{'status':'PASS','decision':'PASS','utc':utc,'scopes':all_scopes,
 'combined_md':rec(BASE/'COMBINED_REVIEW_FOUR.md'),'combined_json':rec(BASE/'COMBINED_REVIEW_FOUR.json'),
 'three_scope_bindings_unchanged':rec(BASE/'THREE_SCOPE_REPORT_BINDINGS.json')})
print(json.dumps({'status':'PASS','global_report':summary,'combined_md':rec(BASE/'COMBINED_REVIEW_FOUR.md'),
 'combined_json':rec(BASE/'COMBINED_REVIEW_FOUR.json')},indent=2))
