from pathlib import Path
from datetime import datetime,timezone
import hashlib,json

BASE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
utc=datetime.now(timezone.utc).isoformat()

ge=BASE/'ge-one-review';bulk=BASE/'bulk-onset-review'
ge_source='ad1a5aabca9d3fcf2e960cbf43bcf7cfbdfd232cc58b86bbaf355229656016a9'
bulk_source='3e1f67ee40b28af0b9de3a643488524fdb38f508d663f63e2ec82f7bc4322804'
assert sha(ge/'PURE_ENVELOPE_GE_ONE.md')==ge_source
assert sha(Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-4-depth-appt/PURE_ENVELOPE_GE_ONE.md'))==ge_source
assert sha(Path('/home/mxym/math-breadth-tcs-20261015/research/breadth-tcs-20261015/phase-4-depth-appt/PURE_ENVELOPE_GE_ONE.md'))==ge_source
assert sha(bulk/'PAPER_V1.md')==bulk_source
assert sha(bulk/'snapshot/PAPER.md')==bulk_source
assert sha(Path('/mnt/d/math/tmp/research-resume-20261015/scalar-bulk-onset-20261015/PAPER.md'))==bulk_source
assert sha(BASE/'REVIEW_V2.md')=='302bfa967e5e8871066700cbb799598a3486a8bfc7f923f9d239de4b9af5952d'
assert sha(BASE/'REVIEW_V2.json')=='5c9276d00f19e1c7fe3253a6ec840833625f95edc19a5a66b1e23d34bc184b21'
assert (BASE/'REVIEW.md').read_bytes()==(BASE/'REVIEW_V2.md').read_bytes()
assert (BASE/'REVIEW.json').read_bytes()==(BASE/'REVIEW_V2.json').read_bytes()

def runs(folder):
 out=[]
 for result in sorted((folder/'runs').glob('*/RESULT.json')):
  r=json.loads(result.read_text());assert r['status']=='PASS'
  assert sha(result.parent/'executed_script.py')==r['executed_script_sha256']
  out.append({'path':str(result.relative_to(BASE)), 'status':r['status'],
             'result_sha256':sha(result),'script_sha256':r['executed_script_sha256'],
             'groups':r['groups'],'python':r['python'],'sympy':r['sympy'],
             'mpmath':r['mpmath'],'decimal_precision':r['decimal_precision']})
 return out

common={'status':'PASS','decision':'PASS','reviewed_utc':utc,
  'reviewer':'/root/critical_entropy_review_resume_20261015, separate internal AI agent',
  'review_kind':'full ordinary mathematical read of the new exact source, with separately written independent diagnostics',
  'external_human_peer_review':False,'Lean_verification':False,'priority_certificate':False,
  'new_major_problem_count':False,'new_Lean_audit_roots':0,'author_code_executed_or_imported':False,
  'source_or_root_modified':False,'subagents_spawned':False,'repository_mutations':False,
  'global_proof_from_finite_diagnostics':False,'independent_unexpected_failures':[],
  'future_metadata_figures_transport_layout_guarantee':False}

g=dict(common)
g.update({'scope':'D1: exact pure envelope and full argmax for every real c>=1 and r>=0',
  'source':{'path':'PURE_ENVELOPE_GE_ONE.md','sha256':ge_source,'bytes':6535,
            'full_text_read':True,'wsl_and_windows_mirrors_byte_compared':True},
  'input_manifest':{'path':'INPUT.json','sha256':sha(ge/'INPUT.json')},
  'report':{'path':'REVIEW.md','sha256':sha(ge/'REVIEW.md')},
  'dependencies':{'prior_full_reads_reused_after_exact_byte_comparison':True,
      'immutable_commit':'c4e0d9e713ba349d376469231789bb7b36915b7d',
      'actual_used_theorems':['L1 value and continuity','L20 conditional exact mixing elimination','L21 unique pure bulk','S all-actual near-optimizer criterion'],
      'V_already_complete_all_order_value_credited':True,
      'old_T_c10_PASS_automatically_extended':False},
  'mathematical_gates':[
      's>1/2 proved for every t>0 by H(0)=Hprime(0)=0 and Hsecond=t exp(t)>0',
      'g convex as maximum of fixed Bernoulli log MGFs, explicit differentiability yields tangent inequality',
      'putative global interior maximum at bare crossing forces h interior, so L20 formula and local stationarity apply',
      'exact a derivative and strict u(s+aprime)>K/2+(K-u)(4K+u)/(6u)>K/2 exclude K>=2 including K=2',
      'compactness excludes all interior ties, not only stationary candidates of a selected family',
      'affinity in r proves all branches and exact equality cases including redundant zero-width face',
      'actual quantum transfer retains complex density matrices and every global unitary, all n>=m and finite critical r',
      'at limiting c=1 approaches from either side allowed; both S physical losses retained'],
  'independent_runs':runs(ge),
  'findings':[],
  'literature_scope':'no new full-text collision or priority audit; prior bounded official abstract/version screen remains with its original limits',
  'not_claimed':['sharp c threshold','connectedness of mixed c set','intermediate-c phase diagram','exact finite-dimensional quantum optimizers','all-order spectral rigidity','body law replacing positive-r physical losses','width-2 interior peak expansion']})
write(ge/'REVIEW.json',g)

a_run=bulk/'snapshot/control-runs/20261015T113652.131637Z/RESULT.json'
a=json.loads(a_run.read_text())
bb=dict(common)
bb.update({'scope':'B1--B19: all-c positive attained lower threshold; sufficiently small-c unique analytic onset; exact coefficients, r interval and iterated physical consequences',
  'source':{'path':'PAPER_V1.md','original_path':'snapshot/PAPER.md','sha256':bulk_source,'bytes':11627,'full_text_read':True},
  'theorem_map':{'path':'snapshot/THEOREM_MAP.md','sha256':sha(bulk/'snapshot/THEOREM_MAP.md'),'full_text_read':True},
  'input_manifest':{'path':'INPUT.json','sha256':sha(bulk/'INPUT.json'),'captured_files':26},
  'dependency_byte_comparison':{'path':'DEPENDENCY_BYTE_COMPARISON.json','sha256':sha(bulk/'DEPENDENCY_BYTE_COMPARISON.json'),'count':11},
  'report':{'path':'REVIEW.md','sha256':sha(bulk/'REVIEW.md')},
  'dependencies':{'prior_full_reads_reused_after_exact_byte_comparison':True,
       'immutable_repository_commit':'c4e0d9e713ba349d376469231789bb7b36915b7d',
       'actual_used_theorems':['L1 value and compact continuity','pure-bulk calculation','T v2 T2 all-c pole threshold','S full all-actual criterion and integer realization'],
       'companion_T_v2_sha256':'83c2240adfbca39009ff446504cc477f47684a0e5de1db52439862053bbcad79',
       'new_c1_extension_used_as_dependency':False,'V_already_complete_value_scope_credited':True},
  'mathematical_gates':[
       'U positive for all c>0; endpoint delta exp(C/delta) divergence locally uniform in c yields attained continuous threshold',
       'exact F-b=P(r-U) retains every threshold minimizer and every boundary tie',
       'strict h convexity gives max(0,hU); logarithmic B6 only on hU>0 branch',
       'all global small-c minimizers first satisfy 2-L=O(c), then rescaled t cannot tend to zero by t exp(2/(3t))/8',
       'analytic Phi extension and fixed compact localization precede unique implicit-function branch',
       'all B7 coefficients recomputed, including tprime=16/9 and quartic threshold correction -28e/9',
       'positive Hessian via Schur complement proves unique local mixed branch and active slope jump',
       'weighted U-Q identity proves a single r mixed interval without claiming connected c set',
       'all actual near-optimizers retain distance to both phases, spread loss J and actual peak loss',
       'body laws are W1 subsequential consequences, peak correction only for interior mixed width, fixed-c limit precedes c->0'],
  'independent_runs':runs(bulk),
  'author_evidence_read_only':{'path':str(a_run.relative_to(BASE)),'status':a['status'],
       'result_sha256':sha(a_run),'input_hashes':a['input_sha256'],
       'full_checker_and_result_read':True,'reviewer_executed':False,'counts_are_not_global_proof':True},
  'findings':[],
  'literature_scope':'PRIMARY_SCOPE is unchanged bounded screen with original date and abstract-only limits; no fresh full-text audit or priority certificate',
  'not_claimed':['explicit sufficiently-small-c cutoff','unique thresholds for every c','no c islands','complete intermediate-c phase diagram','new all-order value closure','simultaneous c_m->0 physical uniformity','exact finite extrema','all-order spectral rigidity']})
write(bulk/'REVIEW.json',bb)

for folder in [ge,bulk]:
 runrecords=runs(folder)
 history='''# Independent control history

The newly written program in this scope does not import or execute author code.
There is one actual execution, with no unexpected failure. Its executed script,
complete result, caught AssertionError countercontrols and exact source hashes
are retained in the run directory. These finite diagnostics support the full
ordinary mathematical read; they do not prove the global quantified theorem.

'''
 for rec in runrecords:
  history+=f"- `{rec['path']}`: {rec['status']}; result SHA-256 `{rec['result_sha256']}`; script SHA-256 `{rec['script_sha256']}`.\n"
 (folder/'CONTROL_HISTORY.md').write_text(history)

records=[
 {'scope':'T v2 pole onset, small-c pole geometry, original c>=10 sufficient pure envelope and fixed-c physical transfer',
  'source_sha256':'83c2240adfbca39009ff446504cc477f47684a0e5de1db52439862053bbcad79',
  'decision':'PASS','report':'REVIEW_V2.md','report_sha256':sha(BASE/'REVIEW_V2.md'),
  'json':'REVIEW_V2.json','json_sha256':sha(BASE/'REVIEW_V2.json'),
  'new_c1_or_bulk_scope_automatically_covered':False},
 {'scope':g['scope'],'source_sha256':ge_source,'decision':'PASS','report':'ge-one-review/REVIEW.md',
  'report_sha256':sha(ge/'REVIEW.md'),'json':'ge-one-review/REVIEW.json','json_sha256':sha(ge/'REVIEW.json'),
  'independent_control_scope':'new c>=1 program, not the old c>=10 program'},
 {'scope':bb['scope'],'source_sha256':bulk_source,'decision':'PASS','report':'bulk-onset-review/REVIEW.md',
  'report_sha256':sha(bulk/'REVIEW.md'),'json':'bulk-onset-review/REVIEW.json','json_sha256':sha(bulk/'REVIEW.json'),
  'independent_control_scope':'new B1--B19 program, not either pure-envelope program'}]
combined=dict(common)
combined.update({'kind':'index of three actual separately completed mathematical reads, not an additional mathematical theorem',
 'scopes':records,'original_T_frozen':'completed-v2/FROZEN_V2.json',
 'original_T_report_bytes_unchanged':True,
 'historical_findings_preserved':[
   'T v1 E_alpha max-moment definition was false for 0<alpha<1; fixed explicitly to alpha>1 in v2, original source/finding kept',
   'T author 100-digit precision diagnostic failed on exponentially small normalization loss; original FAIL and later 1100-digit diagnostic PASS both retained'],
 'new_scope_findings':[],
 'ordinary_disposition_only':True,'publication_metadata_binding_pending':True,
 'additional_future_mathematics_covered':False,
 'global_scope_limits':['no intermediate-c boundary uniqueness or no-c-islands claim','no new all-order value closure or all-order spectral rigidity','no exact finite-dimensional optimizer theorem','no simultaneous c_m->0 physical uniformity','no Lean, human review, priority or major-count certificate','no guarantee of later publication/plot/evidence layout']})
write(BASE/'COMBINED_REVIEW.json',combined)

md='''# Index of three separate independent mathematical reads

Decision: **PASS for each of the three exact scopes below.** This file only
indexes completed internal AI-agent ordinary mathematical reads. It adds no new
mathematical result and does not extend any one report into the other scopes.

'''
for i,r in enumerate(records,1):
 md+=f"{i}. **{r['scope']}**. Source SHA-256 `{r['source_sha256']}`. Decision PASS. Full report: `{r['report']}` (SHA-256 `{r['report_sha256']}`); structured record: `{r['json']}` (SHA-256 `{r['json_sha256']}`).\n\n"
md+='''The original T v2 source, reports, input captures and actual control history
were frozen separately before either follow-up. Their report bytes are
unchanged. The c>=1 proof received its own full read and new program; the old
c>=10 diagnostics were not relabeled as c>=1 validation. The lower-bulk proof
received a separate full read, all-coefficient derivation and new program. Its
dependency on T is the previously read all-c pole threshold, not the new c>=1
argument.

The old T v1 definition-domain finding and the author's real 100-digit precision
failure remain preserved with original source/script/result versions. The two
new mathematical reads found no further correction. Their sole independent runs
passed, and their expected wrong-variant AssertionErrors are recorded rather
than represented as author or theorem failures. No author checker was imported
or executed by the reviewer.

The scalar results retain complete argmax/tie sets. The original complex
trace-one all-global-unitary APPT consequences retain the full S spread and
actual peak losses. The lower-bulk physical c->0 conclusions are iterated after
the fixed-c dimension limit; width 2 is excluded from the interior peak
expansion. A single mixed interval in r is not a proof that the mixed set in c
is connected. The intermediate-c phase boundary and its uniqueness remain open.
The already complete all-order value theorem V is credited, not claimed anew.

This is not Lean verification, external human peer review, a priority
certificate, a new major-problem count, an exact finite-optimizer theorem, or a
full all-order rigidity theorem. No author/root mathematics, old formal audit,
repository state or publication was changed. Final metadata/README/index byte
binding is a separate pending task. No future figure, transport or evidence
layout is certified here.
'''
(BASE/'COMBINED_REVIEW.md').write_text(md)
write(BASE/'NEW_SCOPE_REPORT_BINDINGS.json',{'status':'PASS','decision':'PASS','utc':utc,'files':[
 {'path':str(p.relative_to(BASE)),'sha256':sha(p),'bytes':p.stat().st_size}
 for p in [ge/'REVIEW.md',ge/'REVIEW.json',bulk/'REVIEW.md',bulk/'REVIEW.json',BASE/'COMBINED_REVIEW.md',BASE/'COMBINED_REVIEW.json']],
 'original_T_reports_unchanged':True,'only_private_review_outputs_written':True})
print(json.dumps({'status':'PASS','files':json.loads((BASE/'NEW_SCOPE_REPORT_BINDINGS.json').read_text())['files']},indent=2))
