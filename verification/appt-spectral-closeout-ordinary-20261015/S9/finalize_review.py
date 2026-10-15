from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

R=Path(__file__).resolve().parent
S=R/'owner-snapshot/worktree/research/breadth-tcs-20261015/phase-9-diverging-physical-reduction'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=datetime.now(timezone.utc).isoformat()
old=json.loads((R/'INPUT_VERIFICATION.json').read_text())
assert sha(S/'PAPER.md')=='812ba384981a4ed6ae1ae62d93723fc0505609b7ecf7997c452331947ffcb078'
assert sha(S/'AUTHOR_V1_MANIFEST.json')==old['manifest_sha256']
assert sha(R/'owner.zip')==old['owner_zip_sha256']
for row in old['files']:
    p=S/row['path'];assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
run=R/'reviewer-runs/20261015T160112.905104Z'
result=json.loads((run/'RESULT.json').read_text())
assert result['status']=='PASS' and len(result['rejected_variants'])==7
assert result['script_sha256']==sha(R/'reviewer_checks.py')==sha(run/'CHECKER_SOURCE.py')
assert len(list((R/'reviewer-runs').glob('*/RESULT.json')))==1
fresh=['PAPER.md','COVERAGE_AND_LIMITS.md','THEOREM_MAP.md','README.md','TARGET.json',
       'PRIMARY_SCREEN.json','ATTEMPT_LEDGER.json','SOURCE_INPUTS.json','AUTHOR_V1_MANIFEST.json',
       'author_reduction_controls.py','freeze_reduction_scope.py','initialize_reduction_scope.py']
ledger={'status':'COMPLETED_ORDINARY_READING','utc':now,
        'fresh_complete_reads':[{'path':p,'sha256':sha(S/p)} for p in fresh],
        'credited_inputs':[],
        'author_results':{'path':'AUTHOR_EXACT_CONTROLS.json','sha256':sha(S/'AUTHOR_EXACT_CONTROLS.json'),
                          'rows_fully_parsed':47,'diagnostic_fields_inspected':True,
                          'all_long_exact_numerator_strings_recomputed':False,'author_checker_executed':False},
        'pause_history':'The old INCOMPLETE pause checkpoint is preserved unchanged; the new decision is based on the later completed review and executed controls.'}
for row in old['credited_source_reading']:
    name=row['path']
    if name.endswith('/ALL_ORDER_VARIATIONAL.md'):
        scope='Complete reread before pause and again on resumption; prior complete reading also byte-equal.'
    elif name=='credited-inputs/research/appt-growing-renyi/PAPER.md':
        scope='Prior complete scientific reading reused after exact-byte check; lines 1-280 (through G22 and start of lower construction) reread on resumption.'
    elif name.endswith('/FAST_ORDER_VALUE.md'):
        scope='New complete scientific reading during S9 before pause.'
    elif name.startswith('credited-inputs/phase4/'):
        scope='Earlier independent GLOBAL complete reading reused after exact-byte check; first 141 lines reread in S9. Separate moving-tie illustration only, not core dependency.'
    else:
        scope='Earlier S5 complete scientific reading reused only after literal equality; no claim of a fresh full reread in S9.'
    ledger['credited_inputs'].append({'path':name,'bytes':row['bytes'],'sha256':row['sha256'],
                                     'read_scope':scope,'prior_full_read_copy':row['prior_full_read_copy']})
review={'status':'PASS','decision':'PASS','utc_completed':now,
        'scope':'S9 independent ordinary mathematical review only',
        'paper_sha256':sha(S/'PAPER.md'),'paper_bytes':(S/'PAPER.md').stat().st_size,
        'owner_zip_sha256':sha(R/'owner.zip'),'manifest_sha256':sha(S/'AUTHOR_V1_MANIFEST.json'),
        'report_md_sha256':sha(R/'REVIEW.md'),
        'accepted':['Theorem A uniform all-actual-state centered exceptional reduction at sharp excess and relative log scales',
                    'Theorem B credited V relative-excess bridge and both necessary-and-sufficient functional criteria',
                    'Separate actual integer-rank moving-tie counterexample under credited mature GLOBAL/L results'],
        'domain':{'dimensions':'integer 2<=m<=n, m->infinity','orders':'real alpha->infinity; arbitrary alpha/m, alpha/D and oscillations',
                  'states':'every original complex PSD trace-one density APPT after every global unitary',
                  'finite_bounds':'after common universal m/alpha thresholds, uniform in n and states'},
        'not_covered':['Rglob or any fixed-m/fixed-D extension','bounded or zero orders','S8','new value optimization or full all-positive geometric assembly','Lean/kernel/audit expansion','external human peer review','priority or major-count claims','future publication layout or transport'],
        'read_ledger':'READING_LEDGER.json','author_source_changed':False,'author_code_executed':False,
        'controls':{'independently_written':True,'author_helpers_imported_or_copied':False,
                    'run':run.relative_to(R).as_posix(),'result_sha256':sha(run/'RESULT.json'),
                    'script_sha256':result['script_sha256'],'symbolic':len(result['symbolic_controls']),
                    'exact_integer_compressed_spectra':len(result['exact_compressed_spectra']),
                    'real_order_cases':len(result['stable_real_order_controls']),
                    'actual_vanishing_chord_path_cases':len(result['vanishing_chord_loss_actual_states']),
                    'expected_real_assertion_failures':len(result['rejected_variants']),
                    'unexpected_failures':0,'limitations':result['limitations']},
        'source_findings':[],'operational_private_omissions':'pause-checkpoints subtree may be omitted from a public copy with disclosed path/hash omission list; original private bytes remain in REPORT_BINDINGS.'}
for name,data in [('READING_LEDGER.json',ledger),('REVIEW.json',review)]:
    with (R/name).open('x',encoding='utf-8') as out:
        out.write(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
files=[]
for p in sorted(R.rglob('*')):
    if not p.is_file() or '__pycache__' in p.parts or p.suffix=='.pyc' or p.name=='REPORT_BINDINGS.json':continue
    rel=p.relative_to(R).as_posix()
    category='private_operational_pause_record' if rel.startswith('pause-checkpoints/') else (
             'frozen_owner_source' if rel.startswith('owner-snapshot/') or rel=='owner.zip' else
             'independent_control_and_actual_run' if rel.startswith('reviewer-runs/') or rel=='reviewer_checks.py' else
             'independent_review_and_input_evidence')
    files.append({'path':rel,'bytes':p.stat().st_size,'sha256':sha(p),'category':category})
binding={'status':'PASS','decision':'PASS','scope':'Private completed S9 source/read/control/report byte binding',
         'utc':datetime.now(timezone.utc).isoformat(),'files':files,
         'self_reference_exclusions':['REPORT_BINDINGS.json'],
         'public_copy_policy':'No promise of future transport/layout. Private operational pause records may be omitted only with an explicit omission ledger. Mathematical source, read ledger, own controls and actual expected AssertionError traces are durable mathematical evidence.',
         'no_lean_git_or_author_mutation':True}
with (R/'REPORT_BINDINGS.json').open('x',encoding='utf-8') as out:
    out.write(json.dumps(binding,ensure_ascii=False,indent=2)+'\n')
for row in files:
    p=R/row['path'];assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256']
print(json.dumps({'status':'PASS','files_bound':len(files),'output_directory':str(R),
                  'outputs':{p.name:{'bytes':p.stat().st_size,'sha256':sha(p)} for p in [R/'REVIEW.md',R/'REVIEW.json',R/'READING_LEDGER.json',R/'REPORT_BINDINGS.json']}},indent=2))
