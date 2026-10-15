from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
BASE=Path(__file__).resolve().parent
SRC=BASE/'owner-zip-snapshot/worktree/research/breadth-tcs-20261015/phase-4-depth-appt'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rec(p):return {'path':str(p.relative_to(BASE)),'sha256':sha(p),'bytes':p.stat().st_size}
def write(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
utc=datetime.now(timezone.utc).isoformat()
owner=json.loads((BASE/'INPUT_OWNER_ZIP.json').read_text())
assert len(owner['files'])==31
for x in owner['files']:assert sha(BASE/'owner-zip-snapshot'/x['path'])==x['sha256']
assert sha(BASE/'critical-unique-dirty-20261015T122003Z.zip')==owner['owner_archive_sha256']
runs=[]
for p in sorted((BASE/'runs').glob('*/RESULT.json')):
 d=json.loads(p.read_text());assert d['status']=='PASS'
 runs.append({'result':rec(p),'kind':d['kind'],'status':d['status'],
     'actual_expected_failures':d.get('expected_real_replayer_failures',0)})
assert len(runs)==3
shared={'status':'PASS','decision':'PASS','utc':utc,
 'reviewer':'/root/critical_entropy_review_resume_20261015, separate internal AI agent',
 'review_kind':'complete ordinary mathematical read of the exact new source; no automatic prior-scope extension',
 'owner_archive':{'path':'critical-unique-dirty-20261015T122003Z.zip','sha256':owner['owner_archive_sha256']},
 'input_manifest':rec(BASE/'INPUT_OWNER_ZIP.json'),'credited_dependencies':rec(BASE/'DEPENDENCY_BINDINGS.json'),
 'unresolved_findings':[],'new_source_corrections_required':False,'original_author_bytes_unchanged':True,
 'Lean_or_kernel_execution':False,'external_human_peer_review':False,'priority_certificate':False,
 'new_major_result_count':0,'author_or_root_files_written':False,'subagents_spawned':False,
 'future_publication_or_layout_guarantee':False,
 'physical_transfer':{'original_complex_PSD_trace_one_densities':True,'PPT_after_every_global_unitary':True,
    'all_integer_n_ge_m_with_m_growing':True,'alpha_gt_one_and_alpha_over_m_fixed_positive_limit':True,
    'finite_critical_3poweralpha_over_D_limit':True,'full_argmax_distance_J_and_actual_peak_loss_retained':True,
    'integer_rank_realizations_from_credited_S':True,'body_law_alone_substitutes_for_positive_r_losses':False,
    'width_two_uses_interior_peak_expansion':False,'new_simultaneous_small_c_physical_uniformity':False}}
configs=[
 ('last-boundary','LAST_MIXED_BOUNDARY.md','6e4f77e2bbecbc5e71f426925d444e8e1a9b69d2ffebcbef88badc1f4e87f0a0',
  'LAST: every positive finite boundary of strict mixed-c set; uniform interior compactness and at least three actual body laws',
  ['crossing equivalence and complete pure value at every boundary','explicit full interval 0<c<=1/10 witness',
   'uniform small-L exclusion retaining h factor, exponential L=2 exclusion, then uniform h-face exclusion',
   'interior coexistence from global-maximizer subsequences at every finite positive boundary',
   'strict 1/10<c_dagger<1 without a no-islands premise','actual at-least-three attainable body laws with full S losses'],
  ['no-islands not proved by this source alone','number or nondegeneracy of interior ties not proved by this source alone']),
 ('no-islands','NO_ISLANDS.md','f7509ff124d76f12855a55705f317c51133c8e1a93fcadc7f230bebd91b8ad16',
  'NO_ISLANDS: one strict mixed-c interval, analytic per-width crossing and finitely many last-boundary widths',
  ['strict h convexity with exact lower clamp and v>0 gate','all-positive-t curvature identity and strict AM-GM bound',
   'conditional elasticity ODE barrier with polynomial proof and correct large-w constant barrier',
   'one admissibility interval per width via strict v concavity','normalized g increment and H_K positive on entire admissible domain',
   'unique analytic K_x crossing and union of initial intervals gives exactly 0<c<c_star',
   'full all-r pure argmax above c_star and finite interior tie set at threshold','full original-matrix S transfer retained'],
  ['unique/nondegenerate last width requires separate critical scope','global uniqueness at every mixed c,r remains separate']),
 ('critical-uniqueness','CRITICAL_UNIQUENESS_CERTIFICATE.md','be76b90de9277fab91c1f676f8de7619c2d58a5b79cf65cf06839d7ce8e7637e',
  'CRITICAL: rigorously bracketed unique nondegenerate last interior phase and full local analytic coexistence diagram',
  ['complete integer interval-engine proof read including signed outward rounding, exp/log tails and all domains',
   'analytic x tails plus 73 exact leaves including 45 full-K stationary exclusion strips',
   'actual unchanged author replayer run in private scratch; generator not run; original certificate UTC unchanged',
   'certified strict 519/2000<c_star<13/50 and core strict convexity/endpoint derivative signs',
   'unique last width, Schur-complement Hessian, global local-three-branch compactness with endpoint exclusions',
   'analytic coexistence curves, correct first derivatives and linear window closing',
   'exactly three attainable actual body laws at triple point with full losses and no forced side selection'],
  ['global uniqueness of mixed optimizer at arbitrary c<c_star,r not covered','no finite-dimensional exact APPT theorem'])]
summaries=[]
for folder,name,expected,title,gates,limits in configs:
 assert sha(SRC/name)==expected
 d=dict(shared);d.update({'scope':title,'source':rec(SRC/name),'source_lines':len((SRC/name).read_text().splitlines()),
      'full_manuscript_read':True,'report':rec(BASE/folder/'REVIEW.md'),'proof_gates':gates,
      'scope_limits':limits,'actual_supporting_executions':runs,
      'existing_C1_review_is_only_dependency':True,'fourth_GLOBAL_scope':'PENDING, not covered by this report'})
 if folder=='critical-uniqueness':
  d.update({'full_interval_engine_and_replayer_read':True,'certificate_data_complete_exact_replay':True,
     'critical_inputs':[rec(SRC/x) for x in ['critical_exact_intervals.py','CRITICAL_EXACT_INTERVAL_CERTIFICATE.json','replay_critical_certificate.py']],
     'leaf_counts':{'upper':27,'outside_left':32,'outside_right':13,'core':1},
     'new_independent_interval_engine_claim':False,'authored_replayer_execution_not_misrepresented_as_own_code':True,
     'actual_private_tamper_child_failures':4,'unexpected_execution_failures':[]})
 write(BASE/folder/'REVIEW.json',d)
 summaries.append({'scope':title,'source_sha256':expected,'decision':'PASS',
      'review_md':rec(BASE/folder/'REVIEW.md'),'review_json':rec(BASE/folder/'REVIEW.json')})
combined={'status':'PASS','decision':'PASS','kind':'index of the three separately completed new ordinary mathematical reads',
 'utc':utc,'scopes':summaries,'existing_C1_PASS_not_extended':True,
 'original_source_UTC_and_all_actual_countercontrol_failures_preserved':True,
 'fourth_global_mixed_scope':'PENDING; separate owner archive, full source/engine read and decision required',
 'formal_or_human_peer_review_or_priority_certification':False,'future_metadata_binding_separate':True}
write(BASE/'COMBINED_REVIEW_THREE.json',combined)
md='# Three separately completed independent mathematical reads\n\nDecision: **PASS for each exact scope below.** This is an index of completed internal AI-agent ordinary reads, not a new proof or an extension of old C1 coverage.\n\n'
for x in summaries:
 md+=f"- **{x['scope']}**. Source SHA-256 `{x['source_sha256']}`; decision PASS. Full report `{x['review_md']['path']}` SHA `{x['review_md']['sha256']}`; structured report `{x['review_json']['path']}` SHA `{x['review_json']['sha256']}`.\n"
md+='\nThe original owner ZIP, unmodified certificate and UTC, actual private author-code replay, new independently written symbolic/structural controls and four real expected tamper failures are retained. These execution types are distinguished in every report. Full quantum transfers retain original complex all-global-unitary APPT, full argmax, J and actual peak losses and the original fixed-c physical limit. No Lean, external human review, priority, major count or future publication/transport is certified.\n\n**Fourth GLOBAL_MIXED_PHASE scope remains PENDING.** Its newly frozen owner archive will be reviewed separately. None of these three decisions proves uniqueness of every mixed optimizer at arbitrary c,r. Final status/README/index binding is also a separate future task.\n'
(BASE/'COMBINED_REVIEW_THREE.md').write_text(md)
write(BASE/'THREE_SCOPE_REPORT_BINDINGS.json',{'status':'PASS','decision':'PASS','utc':utc,'reports':summaries,
 'combined_md':rec(BASE/'COMBINED_REVIEW_THREE.md'),'combined_json':rec(BASE/'COMBINED_REVIEW_THREE.json')})
print(json.dumps({'status':'PASS','reports':summaries,'combined':rec(BASE/'COMBINED_REVIEW_THREE.md')},indent=2))
