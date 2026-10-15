"""Machine-readable transcription of a frozen completed review; no new review."""
from pathlib import Path
import datetime,hashlib,json,zipfile

dest=Path(__file__).resolve().parent
original=dest.with_name('independent-coexistence-orientation-review-20261015')
archive=original.with_suffix('.zip')
sha=lambda b:hashlib.sha256(b).hexdigest()
def binding(p):
    data=p.read_bytes()
    return {'path':str(p),'bytes':len(data),'sha256':sha(data)}
def write(name,obj):
    p=dest/name
    assert not p.exists(),str(p)
    p.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')

expected={
    'REVIEW.md':'219f403a25c5ff7b7c5a748ec1ded57b8a06c6177c81d4163b5285c4c43d0f3d',
    'REPORT_MANIFEST.json':'5854509212405f520793ecaa20a98ab6cfd1f2a5ddfb4279a354e2c547f71b49',
}
for name,h in expected.items():assert sha((original/name).read_bytes())==h
assert sha(archive.read_bytes())=='33df359a0ad39622045c4e3ef56eb9e48bffa55f14a306014dcbc6d15eaa5a09'
manifest=json.loads((original/'REPORT_MANIFEST.json').read_bytes())
for row in manifest['files']:
    data=(original/row['path']).read_bytes()
    assert len(data)==row['bytes'] and sha(data)==row['sha256'],row['path']
with zipfile.ZipFile(archive) as z:
    assert len(z.namelist())==85
    for name in z.namelist():assert z.read(name)==(original/name).read_bytes(),name
    original_entries=sorted(z.namelist())
assert sorted(str(p.relative_to(original)) for p in original.rglob('*') if p.is_file())==original_entries
paper=original/'frozen-author/PAPER.md'
owner_manifest=original/'frozen-author/AUTHOR_V1_MANIFEST.json'
assert sha(paper.read_bytes())=='9fdb0649010809711223abd1f30778652ae9bde0cd1d768b66336c3ed22e5cb1'
assert len(paper.read_bytes())==14455
assert sha(owner_manifest.read_bytes())=='be554dd0e2ae2ce1d9bf41e55e1a59a729757711c0256ec1ec6ea0b580eabf83'
controls=json.loads((original/'INDEPENDENT_CONTROLS.json').read_bytes())
runs=json.loads((original/'RUN_LOG.json').read_bytes())
assert len(controls['negative'])==9 and all(v['rejected'] for v in controls['negative'])
assert controls['unexpected_failures']==[] and runs['all_pass']
assert all(v['returncode']==0 for v in runs['runs'])
clock=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015/phase-5-haldane/CLOCK.json')
assert sha(clock.read_bytes())=='d3aab86688c0a69e4cdcaa71f825e1c301017233d9a072adb7c47480af4c6b56'
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
owner_zip={'path':'D:\\math\\tmp\\breadth-tcs-20261015\\phase-8-coexistence-orientation\\orientation-owner-20261015T140115Z.zip','sha256':'d3d1a625705c380dea45c5154dcd35b742e9291f178884ecc3837cf343b06996','verified_in_original_review':True}
review={
 'schema_version':1,'created_utc':now,'status':'PASS','decision':'PASS',
 'scope_id':'S8 coexistence orientation and every fixed-r scalar slice',
 'record_kind':'Machine-readable transcription of the frozen completed ordinary review; not a new mathematical review',
 'transcription_only':True,'new_mathematical_review':False,'controls_rerun_this_supplement':False,
 'original_review_conclusion':'PASS for the exact frozen manuscript and its stated scope. No mathematical correction to the author manuscript is requested.',
 'reviewer':{'agent':'/root/breadth_quantum_resume_20261015','type':'Internal OpenAI AI ordinary mathematical/code reviewer','different_from_author_agent':True},
 'paper':dict(binding(paper),source_owner_agent='/root/breadth_tcs_resume_20261015',source_worktree='/home/mxym/math-breadth-tcs-20261015/research/breadth-tcs-20261015/phase-8-coexistence-orientation',author='Yongxian Zhang',affiliation='South China University of Technology'),
 'source_owner_manifest':binding(owner_manifest),'source_owner_archive':owner_zip,
 'original_review':binding(original/'REVIEW.md'),'original_report_manifest':binding(original/'REPORT_MANIFEST.json'),
 'original_review_archive':binding(archive),
 'precise_domain':{
  'scalar':{'parameters':'Every real c>0 and r>=0','optimization':'Full compact (L,h) in [0,2] x [0,1]','P_at_L_2':0,'pole_class':'{0} x [0,1], one phase class with redundant h','critical_parameter':'519/2000 < c_star < 13/50','coexistence':'Real analytic r_B,r_P on (0,c_star), with analytic local continuations at the triple point'},
  'physical_transfer':{'original_objects':'Complex PSD trace-one density matrices on C^m tensor C^n, PPT after every global unitary','dimensions':'Integers 2<=m<=n with m tending to infinity','orders':'Real alpha>1','limiting_window':'alpha/m -> c in (0,infinity), 3^alpha/(mn) -> finite r in [0,infinity)','credited_inputs':'Exact frozen L value theorem and S actual-spectrum nearoptimizer theorem','criterion':'Relative first-nonzero entropy-deficit nearoptimality iff distance to FULL scalar argmax ->0, actual J ->0, and actual peak loss Pi ->0','peak_correction_scope':'Only r>0 and limiting l<2; at l=2 only the vanishing peak-moment conclusion is invoked'}
 },
 'reviewed_claims':[
  'r_B prime(c)>0 and r_P prime(c)>0 for every 0<c<c_star, and both finite strictly positive at the triple point',
  'r_B(0+)=r_P(0+)=0 and r_B(c_star)=r_P(c_star)=r_star',
  'At the triple point 0<r_P prime<r_0 prime<r_B prime',
  'For 0<r<r_star, unique analytic inverse thresholds c_P<c_0<c_B<c_star and the full pole / pole+interior / interior / interior+bulk / bulk slice over every c>0',
  'At r=r_star exactly the pole/triple/bulk slice; at r>r_star one pure pole/bulk crossing above c_star; at r=0 only the unique bulk point',
  'Horizontal mixed-width closing coefficient 1/r_P prime(c_star)-1/r_B prime(c_star)>0, with the stated quadratic remainder',
  'Actual S transfer retains all full argmax classes, actual losses, attainment and alternating subsequences in the original finite window'
 ],
 'key_derivative_conventions':[
  'M_c is the stationary-value derivative at fixed r',
  'a_k holds c, equivalently K=2c, fixed',
  'f_c at fixed k,r and f_c at fixed L,r differ by 2x f_k away from stationarity',
  'M_r is original P, not the derivative of log M',
  'Total differentiation along coexistence occurs after the fixed-r envelope partials'
 ],
 'actual_original_controls':{
  'evidence':binding(original/'INDEPENDENT_CONTROLS.json'),
  'positive_groups':controls['positive'],
  'exact_critical_certificate_leaves_replayed':73,'exact_global_certificate_leaves_replayed':74,
  'author_no_islands_finite_samples_read':92,
  'real_expected_negative_controls':controls['negative'],'expected_negative_count':9,
  'unexpected_failures':controls['unexpected_failures'],'unexpected_failure_count':0,
  'all_five_original_recorded_runs_returned_zero':True,'run_log':binding(original/'RUN_LOG.json'),
  'numerical_checks_are_falsification_only':True,
  'display_issue':'Initial combined display truncated the end of GLOBAL_MIXED_PHASE; the entire missing end was actually reread before the original decision'
 },
 'limits':[
  'This S8 review does not grant review status to S5, S6, S7 or other manuscripts',
  'No extension of physical transfer to c->0, c->infinity, r->infinity, finite m or exact finite-dimensional optimizers',
  'No replacement of the full S criterion by phase names or body laws alone',
  'Old scalar geometry and L/S are credited in their exact original scopes; no recursive expansion of historical Lean audits',
  'Internal AI ordinary review, not external human peer review, Lean verification, priority certification or a new-major result'
 ],
 'other_manuscript_status_clarification':{
  'original_phrase':'other pending S5/S6/S7',
  'meaning':'A scope exclusion for S8; not a withdrawal, reassessment or current status assertion for those manuscripts',
  'root_reported_context':'S5 and S6 were separately reviewed and published in main 5fbb3854; S7 has a separate independent PASS awaiting integration',
  'context_source':'Root message received during this supplementation',
  'independent_status_recheck_in_this_supplement':False,
  'other_scope_changed_or_revoked':False,
  'original_frozen_wording_preserved':True
 },
 'preservation':{'original_85_files_zip_and_manifest_unchanged':True,'original_archive_all_85_members_read_back_again':True,'all_writes_limited_to_new_supplement_directory':True,'HN0_status':'paused','HN0_effective_seconds':3965.905531,'HN0_clock_sha256':sha(clock.read_bytes()),'new_research_or_lean_or_push':False,'live_jobs':[]}
}
write('REVIEW.json',review)
write('REPORT_BINDINGS.json',{
 'schema_version':1,'created_utc':now,'purpose':'Supplementary machine-decision bindings; original frozen report and manifest remain untouched',
 'decision':'PASS','new_mathematical_review':False,
 'supplement_review_json':binding(dest/'REVIEW.json'),
 'original_review_md':binding(original/'REVIEW.md'),'original_report_manifest':binding(original/'REPORT_MANIFEST.json'),
 'original_review_archive':binding(archive),'paper':binding(paper),'source_owner_manifest':binding(owner_manifest),'source_owner_archive':owner_zip,
 'original_input_binding':binding(original/'INPUT_BINDING.json'),'original_dependency_binding':binding(original/'DEPENDENCY_BINDING.json'),
 'original_controls':binding(original/'INDEPENDENT_CONTROLS.json'),'original_run_log':binding(original/'RUN_LOG.json')})
rows=[binding(p) for p in sorted(dest.iterdir()) if p.is_file()]
for row in rows:row['path']=Path(row['path']).name
write('SUPPLEMENT_MANIFEST.json',{'schema_version':1,'created_utc':now,'self_excluded':True,'status':'PASS','transcription_only':True,'original_frozen_materials_unchanged':True,'files':rows})
for row in json.loads((dest/'SUPPLEMENT_MANIFEST.json').read_bytes())['files']:
    b=(dest/row['path']).read_bytes();assert sha(b)==row['sha256'] and len(b)==row['bytes']
print(json.dumps({'directory':str(dest),'files':[binding(dest/name) for name in ['REVIEW.json','REPORT_BINDINGS.json','SUPPLEMENT_MANIFEST.json']],'original_85_items_zip_manifest_unchanged':True,'HN0':'paused 3965.905531 seconds','stopped':True},indent=2))
