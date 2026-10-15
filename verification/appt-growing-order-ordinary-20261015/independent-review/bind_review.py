"""Bind final P ordinary review and retained executions, without rerunning any."""
from pathlib import Path
from datetime import datetime, timezone
import difflib, hashlib, json

HERE=Path(__file__).resolve().parent
AUTHOR=HERE.parent/'growing-renyi-order'

def entry(path):
    data=path.read_bytes()
    return {'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'lines':len(data.splitlines())}

manifest=json.loads((HERE/'INPUT_MANIFEST.json').read_text())
for relative,item in manifest['files'].items():
    assert entry(HERE/relative)['sha256']==item['sha256'],relative
for name in ['PAPER.md','THEOREM_MAP.md','REVIEW_HISTORY.md','checks.py']:
    assert (AUTHOR/name).read_bytes()==(HERE/'snapshot/P-v3'/name).read_bytes(),name
for name in ['PAPER.md','THEOREM_MAP.md','checks.py']:
    assert (AUTHOR/'author-versions/before-fixed-dimension-quantifier-fix'/name).read_bytes()==(HERE/'author-versions/before-fixed-dimension-quantifier-fix'/name).read_bytes()
for name in ['PAPER.md','THEOREM_MAP.md','REVIEW_HISTORY.md','checks.py']:
    assert (AUTHOR/'author-versions/before-sharper-upper-rate'/name).read_bytes()==(HERE/'snapshot/P-v2'/name).read_bytes()
original=(HERE/'snapshot/P/PAPER.md').read_text()
v2=(HERE/'snapshot/P-v2/PAPER.md').read_text()
final=(HERE/'snapshot/P-v3/PAPER.md').read_text()
assert original.split('## 5.',1)[0]==v2.split('## 5.',1)[0]
assert v2.split('**P2.**',1)[1]==final.split('**P2.**',1)[1]
assert entry(HERE/'snapshot/P-v3/PAPER.md')['sha256']=='3d038944ad35c16fb1c3c99db4fcc096f3a12e543016048a002c035712516e06'
assert (HERE/'snapshot/dependencies/SHARP_ASYMPTOTIC.md').read_bytes()==(HERE/'snapshot/dependencies/preprint-copy-SHARP_ASYMPTOTIC.md').read_bytes()

runs=[]
for name in ['20261015T091232.667475Z','20261015T091753.210538Z']:
    folder=HERE/'runs'/name
    result=json.loads((folder/'RESULT.json').read_text())
    assert result['status']=='PASS'
    assert result['script_sha256']==entry(folder/'independent_checks.py')['sha256']
    assert result['input_manifest_sha256']==entry(folder/'INPUT_MANIFEST.json')['sha256']
    exact=result['groups']['exact_graph_and_rank_controls']
    actual=result['groups']['finite_actual_states']
    assert exact['rational_decreasing_row_graphs']==65
    assert exact['all_integer_ranks_for_uniform_Schmidt_test']==1488
    assert actual['dimension_order_cases']==96 and actual['state_comparisons']==576
    assert actual['alpha_above_D_cases']==25 and actual['m2_exact_zero_head_cases']==144
    assert len(result['expected_rejections'])==6
    assert all(x['status']=='REJECTED' for x in result['expected_rejections'])
    runs.append({'run':name,'status':'PASS','result':entry(folder/'RESULT.json'),
                 'executed_script':entry(folder/'independent_checks.py'),
                 'expected_rejections':result['expected_rejections']})
old=(HERE/'runs'/runs[0]['run']/'independent_checks.py').read_text()
new=(HERE/'runs'/runs[1]['run']/'independent_checks.py').read_text()
assert old.replace('2 * mp.exp(-mp.sqrt(a)) + 2 / mp.sqrt(a) + mp.log(48) / a',
                   '(2 * mp.log(a) + mp.log(48) + 2) / a')==new
assert new==(HERE/'independent_checks.py').read_text()
diff=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),
    fromfile=runs[0]['run'],tofile=runs[1]['run']))
(HERE/'history/independent-checker-upper-strengthening.diff').write_text(diff)

author_runs=[]
for folder in sorted((HERE/'author-evidence').iterdir()):
    data=json.loads((folder/'RESULT.json').read_text());assert data['status']=='PASS'
    for name,digest in data['source_sha256'].items():assert entry(folder/name)['sha256']==digest
    author_runs.append({'run':folder.name,'status':'PASS','result':entry(folder/'RESULT.json'),
        'executed_by_reviewer':False,'finite_cases':data['groups']['finite_actual_states']['cases'],
        'original_P2_error_detected_by_this_run':folder.name!='20261015T090459.816232Z'})

versions={}
for version,label,names in [('P','original range error',['PAPER.md','THEOREM_MAP.md']),
                           ('P-v2','corrected P2, weaker upper',['PAPER.md','THEOREM_MAP.md','REVIEW_HISTORY.md','checks.py']),
                           ('P-v3','final corrected and strengthened',['PAPER.md','THEOREM_MAP.md','REVIEW_HISTORY.md','checks.py'])]:
    versions[version]={'meaning':label,'files':{name:entry(HERE/'snapshot'/version/name) for name in names}}
record={
    'decision':'PASS',
    'scope':'corrected and strengthened final P0-P2 only, not original false fixed-D P2 range',
    'reviewer':'internal AI agent /root/critical_entropy_review_resume_20261015',
    'reviewed_utc':datetime.now(timezone.utc).isoformat(),
    'blind_review':False,'external_human_peer_review':False,'formal_verification':False,
    'new_Lean':False,'old_audit_expanded':False,'author_sources_edited_by_reviewer':False,
    'automatic_coverage_from_L_M_or_previous_reviews':False,
    'final_math_sources':versions['P-v3']['files'],
    'all_source_versions':versions,
    'actual_read':{
        'original_P':'full 188-line manuscript and 29-line map',
        'corrected_v2':'full 190-line manuscript, 30-line map, 24-line history and 93-line checker',
        'final_v3':'full 192-line manuscript, 31-line map, 32-line history and 93-line checker',
        'SHARP':'full 259-line source, especially finite Sections2-4 and all-rank/finite purity Section8',
        'C':'previous same-reviewer full frozen read; current Section4 finite physical inequalities reread and separated from later cubic estimates',
        'author_runs':'all three parsed/copied/hash-checked, result summaries inspected; no author execution',
        'literature':'no new exhaustive search or priority investigation'},
    'resolved_mathematical_findings':[{
        'original_source_sha256':versions['P']['files']['PAPER.md']['sha256'],
        'finding':'fixed-m c=infinity corollary omitted D->infinity and was literally false at fixed D',
        'counterexample':'m=n=2: actual max lambda_1=1/2 by maximally entangled test and normalized I+2vv* attainment, so E_alpha->log2 not log3',
        'correction':'fixed-m branch explicitly requires D=mn->infinity, including c=infinity; source and map changed and originals retained',
        'not_an_unchanged_target_or_status_edit':True,
        'initial_author_PASS_failed_to_detect_it':True}],
    'unresolved_mathematical_findings':[],
    'author_strengthening':{
        'separate_from_range_fix':True,'cutoff':'epsilon=1/(alpha-1)',
        'upper_error':'2m/(D-m)+(2log(alpha-1)+log48+2)/(alpha-1)',
        'uniform_absolute_rate':'O(D^-1/2+log(alpha)/alpha)',
        'full_updated_read_and_actual_independent_rerun':True,
        'previous_corrected_source_preserved':True},
    'theorem_scope':{
        'P0':'EVERY integer 2<=m<=n and EVERY real alpha>=2; explicit T-L<=actual E<=T+U with no hidden cutoff',
        'P1':'D->infinity AND alpha->infinity, uniform across fixed/growing/oscillating m and arbitrary order-dimension relations; absolute rate, not relative equivalent',
        'P2_m_growing_positive_c':'m->infinity, alpha/logD->c in (0,infinity], limit max(0,log3-1/c)',
        'P2_m_growing_zero_c':'m->infinity and alpha/logD->0 for arbitrary positive alpha, even tiny/bounded/oscillating, by order monotonicity',
        'P2_fixed_m':'D->infinity AND alpha->infinity with alpha/logD->c in [0,infinity], bulk logq retained and no bounded-order extension',
        'original_domain':'actual complex trace-one PSD matrices PPT after every global unitary',
        'physical_inputs':'exact finite graph head-square bound8, b>0, m=2 p1=0, D-dependent mean; actual spike and arbitrary integer-rank projections',
        'alpha_greater_D':'rank=max(1,floor(D/alpha)), never fractional below one'},
    'not_claimed':['exact finite entropy or every equality spectrum','sharp next terms',
        'relative accuracy at vanishing leading value','fixed-order small-deficit asymptotic',
        'absolute separability','new Lean','external human review','new major-conjecture count',
        'finite diagnostics as exhaustive full-feasible-set certificate','priority certificate'],
    'dependencies':{name:entry(HERE/'snapshot/dependencies'/name) for name in ['C-PAPER.md','SHARP_ASYMPTOTIC.md','preprint-copy-SHARP_ASYMPTOTIC.md']},
    'ordinary_report':entry(HERE/'REVIEW.md'),
    'control_history':entry(HERE/'CONTROL_HISTORY.md'),
    'input_manifest':entry(HERE/'INPUT_MANIFEST.json'),
    'independent_runs':runs,
    'unexpected_independent_mathematical_checker_failures':0,
    'snapshot_setup_failure':{'count':1,'cause':'unique SHARP path assertion found two byte-identical research/preprint copies',
        'trace':entry(HERE/'history/capture-setup-failure.txt'),
        'initial_helper':entry(HERE/'history/capture-initial-two-path-assumption.py'),
        'not_a_mathematical_checker_failure':True},
    'author_runs':author_runs,
    'final_publication_metadata_binding':'pending; this record binds mathematical source only'
}
(HERE/'REVIEW.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'decision':'PASS','final_PAPER':record['final_math_sources']['PAPER.md'],
    'report':entry(HERE/'REVIEW.md'),'record':entry(HERE/'REVIEW.json'),
    'mathematical_finding_resolved':1,'final_independent_run':runs[-1]['run'],
    'author_source_unchanged':True}))
