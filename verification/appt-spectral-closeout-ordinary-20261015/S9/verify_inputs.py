from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parent
S=R/'owner-snapshot/worktree/research/breadth-tcs-20261015/phase-9-diverging-physical-reduction'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(S/'PAPER.md')=='812ba384981a4ed6ae1ae62d93723fc0505609b7ecf7997c452331947ffcb078'
assert (S/'PAPER.md').stat().st_size==16144
assert sha(S/'AUTHOR_V1_MANIFEST.json')=='417c88541d80f21932880f8ae37fd15772acf9361a7c851f5e88ccafff447932'
m=json.loads((S/'AUTHOR_V1_MANIFEST.json').read_text());rows=[]
for x in m['files']:
 p=S/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],x['path'];rows.append(x)
actual={p.relative_to(S).as_posix() for p in S.rglob('*') if p.is_file()}
assert actual=={x['path'] for x in rows}|{'AUTHOR_V1_MANIFEST.json'}
prior=R.parent/'independent-sublinear-rigidity-review-20261015/owner-snapshot/worktree/research/breadth-tcs-20261015/phase-5-sublinear-rigidity/credited-inputs'
critical=R.parent/'independent-critical-boundary-review-20261015'
sources=[]
for x in rows:
 if not x['path'].startswith('credited-inputs/'):continue
 p=S/x['path'];rel=x['path'][len('credited-inputs/'):]
 if rel.startswith('phase4/'):
  found=[q for q in critical.rglob('GLOBAL_MIXED_PHASE.md') if sha(q)==x['sha256']]
  assert found;prev=found[0];assert p.read_bytes()==prev.read_bytes()
  mode='Prior complete separate four-scope GLOBAL read, exact bytes reused; illustration dependency only'
 elif (prior/rel).is_file():
  prev=prior/rel;assert p.read_bytes()==prev.read_bytes()
  mode='Prior complete mature scientific input read, exact bytes reused; V additionally reread in full in S9'
 else:
  assert rel=='research/appt-ultralinear-spectrum-20261014/FAST_ORDER_VALUE.md',rel
  prev=None;mode='New complete scientific source reading in S9 (range context, not core dependency)'
 sources.append(dict(x,prior_full_read_copy=str(prev) if prev else None,read_scope=mode))
author=json.loads((S/'AUTHOR_EXACT_CONTROLS.json').read_text())
assert author['paper_sha256']==sha(S/'PAPER.md') and author['source_sha256']==sha(S/'author_reduction_controls.py')
assert author['finite_cases']==len(author['rows'])==47 and author['all_requested_assertions_passed']
result={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'method':'Own literal input/previous-read equality verification only; author code not executed',
 'listed_files':len(rows),'total_owner_files':len(actual),'files':rows,
 'owner_zip_sha256':sha(R/'owner.zip'),'manifest_sha256':sha(S/'AUTHOR_V1_MANIFEST.json'),
 'credited_source_reading':sources,'stored_author_result_all_rows_parsed':47,'author_code_executed':False}
(R/'INPUT_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['files','credited_source_reading']},indent=2))
print(json.dumps({'author_stored_utc':author['utc'],'rows':[{k:x[k] for k in ['kind','m','n','D','alpha','actual_chord_loss_decimal','omitting_nonzero_chord_loss_rejected','omitting_nonzero_actual_mean_rejected']} for x in author['rows']]},indent=2))
