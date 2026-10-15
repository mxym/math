from pathlib import Path
from datetime import datetime,timezone
import hashlib,json

R=Path(__file__).resolve().parent
S=R/'owner-snapshot/all-dimension-diverging-spectral-reduction-20261015'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=datetime.now(timezone.utc).isoformat()
assert sha(S/'PAPER.md')=='75f5d9226c447c8acb4c6e609ac805e57a399a2a0dbfbaf8a3047bd5c22748e9'
assert sha(S/'AUTHOR_V1_MANIFEST.json')=='44a14627b4e90cdd959b60c68019a2a878289662eb03dd0cf6058cadb1b64cc9'
assert sha(R/'owner.zip')=='06b892c0fc87cbd74ecfddcf2538d4e98d1687ab1117c1756610516c6e40cb2c'
owner=json.loads((S/'AUTHOR_V1_MANIFEST.json').read_text())['files']
for name,digest in owner.items():assert sha(S/name)==digest
assert {p.relative_to(S).as_posix() for p in S.rglob('*') if p.is_file()}==set(owner)|{'AUTHOR_V1_MANIFEST.json'}
run=R/'reviewer-runs/20261015T161243.469602Z'
result=json.loads((run/'RESULT.json').read_text())
assert result['status']=='PASS' and len(result['rejected_variants'])==7
assert result['script_sha256']==sha(R/'reviewer_checks.py')==sha(run/'CHECKER_SOURCE.py')
assert len(list((R/'reviewer-runs').glob('*/RESULT.json')))==1
old=json.loads((R/'CREDITED_SOURCE_VERIFICATION.json').read_text())
assert old['status']=='PASS' and len(old['files'])==15
for row in old['files']:assert sha(S/row['path'])==row['sha256']
fresh=['PAPER.md','MATHEMATICAL_NOTES.md','THEOREM_MAP.md','README.md','RESEARCH_LOG.md',
       'PRIMARY_SCOPE.json','CREDITED_INPUTS.json','requirements.txt','checks.py']
ledger={'status':'COMPLETED_ORDINARY_READING','utc':now,
        'fresh_complete_sources':[{'path':p,'sha256':sha(S/p),'lines':len((S/p).read_text().splitlines())} for p in fresh],
        'credited_input_reading':[],
        'historical_author_controls':[],
        'scope_warning':'Ordinary complete Rglob review; exact-source old readings reused only in the specified scope. No Lean/kernel or complete new external paper proof audit.'}
for row in old['files']:
    name=row['path']
    if name.endswith('appt-all-order-exact-20261014/PAPER.md'):
        mode='Fresh full 387-line Rglob reading; literal equality to older scientific input also checked. Use is A5 with one eventual fixed-m threshold valid at every order.'
    elif name.endswith('appt-all-order-exact-20261014/REVIEW.md') or name.endswith('appt-all-order-exact-20261014/THEOREM_MAP.md'):
        mode='Fresh complete historical ordinary record/map reading.'
    elif name.endswith('/ALL_ORDER_REVIEW.json'):
        mode='Fresh complete historical ordinary review JSON reading.'
    elif name=='credited-X/PAPER.md':
        mode='Prior complete independent X-v2 mathematical reading reused after exact-byte check; lines95-277 freshly reread, including entire qubit section. External Song--Chen theorem statement/context is an explicitly inherited ordinary input, not a new complete external proof audit.'
    elif name=='credited-X/PRIMARY_SCOPE.json':
        mode='Fresh complete scope ledger reading and exact equality to prior X source.'
    elif name.startswith('credited-X/'):
        mode='Literal equality to prior X-v2 read/bound input; no claim to freshly reread every metadata field here.'
    elif name.startswith('credited-author-S9/'):
        mode='Complete S9 reading just completed in the separately frozen S9 review; literal equality checked here. Reproduced Rglob core was independently read and checked, not certified by automatic extension of S9 PASS.'
    else:
        mode='Prior complete scientific reading reused after exact-byte check (S5/S9); no fresh complete reread claimed in Rglob.'
    ledger['credited_input_reading'].append(dict(row,read_scope=mode))
for d in sorted((S/'control-runs').iterdir()):
    j=json.loads((d/'RESULT.json').read_text())
    for name,digest in j['source_hashes'].items():assert sha(d/name)==digest
    traces=sorted(d.glob('*.expected-trace.txt'))
    assert len(traces)==6 and all('AssertionError' in p.read_text() for p in traces)
    ledger['historical_author_controls'].append({'path':d.relative_to(S).as_posix(),
        'stored_utc':j['utc'],'status':j['status'],'result_sha256':sha(d/'RESULT.json'),
        'source_hashes':j['source_hashes'],'all_result_rows_parsed':True,
        'all_printed_numeric_details_independently_recomputed':False,
        'actual_expected_traces_read':6,'checker_executed_by_this_reviewer':False,
        'script_reading':'Current full213-line checker plus complete first-to-second diff; first source not claimed freshly reread as a separate whole.'})
review={'status':'PASS','decision':'PASS','scope':'Rglob source-bound independent ordinary mathematical review',
        'utc_completed':now,'paper_sha256':sha(S/'PAPER.md'),'paper_bytes':(S/'PAPER.md').stat().st_size,
        'owner_zip_sha256':sha(R/'owner.zip'),'manifest_sha256':sha(S/'AUTHOR_V1_MANIFEST.json'),
        'review_md_sha256':sha(R/'REVIEW.md'),
        'accepted_scopes':{
          'Lemma1':'Universal omitted square mass and existence of non-effective universal strict omitted-coordinate gap over every 2<=m<=n; qubit second peak retained.',
          'Theorem2':'All original complex all-global-unitary APPT densities, every dimension pair including fixed D, finite real alpha after one universal threshold; uniform relative moment-excess and relative log reductions.',
          'Theorem3':'Joint D->infinity and finite real alpha->infinity, uniformly all dimension splits; growing-m G/V bridge plus separately proved fixed-m sharp moment bridge; exact compact external-input qubit benchmark for D>=6.',
          'tests18_19':'Both directions at their distinct objectives under joint D/alpha divergence; actual mean and chord functional retained.',
          'endpoint20':'Separate exact infinite-order entropy ratio at every dimension pair, no infinite-power substitution.'},
        'input_theorems':'G/V/A ordinary source ranges, FAST identity and X qubit mapping; external Song--Chen Theorem10 is explicitly assumed in its previously read statement/context scope, not independently reproved here.',
        'source_findings':[],'author_files_changed':False,'author_code_executed':False,
        'own_controls':{'script_sha256':result['script_sha256'],'run':run.relative_to(R).as_posix(),
          'result_sha256':sha(run/'RESULT.json'),'symbolic':len(result['symbolic_controls']),
          'exact_integer_spectra':len(result['exact_spectrum_controls']),
          'qubit_family_boundary_checks':result['qubit_family_boundary_checks'],
          'stable_real_order_cases':len(result['real_order_controls']),
          'fixed_m_scalar_split_triples':len(result['fixed_m_scalar_split_controls']),
          'width_samples_each':13,'integer_lattice_cases':len(result['integer_lattice_controls']),
          'high_order_peak_band_cases':len(result['peak_band_controls']),
          'expected_actual_assertion_failures':len(result['rejected_variants']),
          'unexpected_mathematical_failures':0,'limitations':result['limitations']},
        'real_reviewer_capture_failures':[
          {'directory':'capture-failures/first-duplicate-paper-assumption','actual_tool_chunk':'019b65','cause':'Reviewer assumed exactly one same-hash PAPER despite legitimate canonical and two run copies.'},
          {'directory':'capture-failures/second-manifest-schema-assumption','actual_tool_chunk':'3d06d6','cause':'Reviewer assumed list rows although manifest files is a path-to-hash dictionary.'}],
        'not_covered':['S8','further mathematical scopes','full all-order body-law geometry','effective universal rho or smallest thresholds','new Lean/kernel/audit work','external human peer review','priority or major-count certification','future publication metadata/layout/transport'],
        'stopping_boundary':'The assigned S9 and Rglob mathematical reviews are complete; no further research is started.'}
readback={'status':'PASS','utc':now,'owner_files':len(owner)+1,
          'files':[{ 'path':name,'bytes':(S/name).stat().st_size,'sha256':sha(S/name)} for name in sorted(set(owner)|{'AUTHOR_V1_MANIFEST.json'})],
          'scope':'Final literal source readback after complete ordinary review and independent controls; no author mutation.'}
for name,data in [('READING_LEDGER.json',ledger),('REVIEW.json',review),('FINAL_SOURCE_READBACK.json',readback)]:
    with (R/name).open('x',encoding='utf-8') as f:f.write(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
files=[]
for p in sorted(R.rglob('*')):
    if not p.is_file() or p.name=='REPORT_BINDINGS.json' or '__pycache__' in p.parts or p.suffix=='.pyc':continue
    rel=p.relative_to(R).as_posix()
    category='frozen_owner_source_and_history' if rel.startswith('owner-snapshot/') or rel=='owner.zip' else (
             'independent_control_and_actual_run' if rel.startswith('reviewer-runs/') or rel=='reviewer_checks.py' else
             'real_reviewer_capture_failure_to_preserve' if rel.startswith('capture-failures/') else
             'independent_review_and_capture_evidence')
    files.append({'path':rel,'bytes':p.stat().st_size,'sha256':sha(p),'category':category})
binding={'status':'PASS','decision':'PASS','scope':'Rglob private source, actual-reading, actual-control, real-failure and report binding',
         'utc':datetime.now(timezone.utc).isoformat(),'files':files,'self_reference_exclusions':['REPORT_BINDINGS.json'],
         'limits':'No future publication layout/transport or new scope guarantee. No newly copied external raw primary text/tool excerpt. The two real reviewer capture failures and all seven actual wrong-variant tracebacks are preserved.',
         'no_author_root_git_or_lean_mutation':True}
with (R/'REPORT_BINDINGS.json').open('x',encoding='utf-8') as f:f.write(json.dumps(binding,ensure_ascii=False,indent=2)+'\n')
for row in files:
    p=R/row['path'];assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
print(json.dumps({'status':'PASS','files_bound':len(files),'directory':str(R),
                  'outputs':{p.name:{'bytes':p.stat().st_size,'sha256':sha(p)} for p in [R/'REVIEW.md',R/'REVIEW.json',R/'READING_LEDGER.json',R/'REPORT_BINDINGS.json']}},indent=2))
