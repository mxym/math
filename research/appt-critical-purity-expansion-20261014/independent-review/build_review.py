"""Bind the completely read initial proof to inspected status-only final text."""
from pathlib import Path
from datetime import datetime,timezone
import difflib,hashlib,json
OUT=Path(__file__).resolve().parent
ROOT=OUT.parent
REPO=Path('/home/mxym/math-appt-multiscale-20261013/research')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

# Filled only after the reviewer reads the actual changed final lines.
EXPECTED_CHANGED_LINES={'PAPER.md':[3,186],'THEOREM_MAP.md':[3,37],'README.md':[3,21,22,28,29]}
assert EXPECTED_CHANGED_LINES is not None,'Final author changes have not yet been independently inspected.'
bindings=[]
for name,oldname in [('PAPER.md','SNAPSHOT_PAPER.md'),('THEOREM_MAP.md','SNAPSHOT_THEOREM_MAP.md'),('README.md','AUTHOR_SNAPSHOT_README.md')]:
 old=OUT/oldname; final=ROOT/name
 oldlines=old.read_bytes().splitlines(keepends=True); newlines=final.read_bytes().splitlines(keepends=True)
 assert len(oldlines)==len(newlines),(name,'unexpected line-count change')
 deltas=[dict(line=i+1,before=a.decode().rstrip('\r\n'),after=b.decode().rstrip('\r\n')) for i,(a,b) in enumerate(zip(oldlines,newlines)) if a!=b]
 assert [x['line'] for x in deltas]==EXPECTED_CHANGED_LINES[name],(name,deltas)
 reversed_lines=list(newlines)
 for item in deltas: reversed_lines[item['line']-1]=oldlines[item['line']-1]
 assert b''.join(reversed_lines)==old.read_bytes()
 (OUT/('FINAL_'+name)).write_bytes(final.read_bytes())
 diff=''.join(difflib.unified_diff(old.read_text().splitlines(keepends=True),final.read_text().splitlines(keepends=True),fromfile='initial/'+name,tofile='final/'+name))
 (OUT/('FINAL_STATUS_'+name+'.diff')).write_text(diff)
 bindings.append(dict(path=name,initial_sha256=sha(old),final_sha256=sha(final),lines=len(oldlines),changed_lines=deltas,exact_reverse_to_completely_read_initial=True,mathematical_changes=0,final_reading='Only actual changed lines independently read; no second complete final reading claimed.'))
raw=[]
for p in sorted(OUT.glob('RUN_*.json')):
 d=json.loads(p.read_text())
 raw.append(dict(path=p.name,sha256=sha(p),result=d.get('result'),counts=d.get('counts'),error=d.get('error'),reviewer_script_sha256=d.get('reviewer_script_sha256')))
assert [r['result'] for r in raw]==[None,'FAIL','PASS','PASS']
last=json.loads((OUT/raw[-1]['path']).read_text())
assert last['counts']=={'Fraction':510,'binding':2,'mp180':224,'symbolic':12}
assert all(item['passed'] for item in last['checks'])
support=json.loads((OUT/'AUTHOR_REPORT_STRUCTURAL_VALIDATION.json').read_text())
assert support['parsed_rows']==48 and support['source_manifest_checked_entries']==4
deps=[]
for stage,n,sh in [('appt-critical-purity-optimizer-20261014',292,'b5c050372e382c47d753ffe0d1e15c4dae4e0c272d878bb5f31175bf0a82d270'),('appt-exact-purity-onset-20261014',361,'41edf08c0ed2d8cd9d6e15f9eeeba0c4814cab2c9a0e81565af7eab39b090d6e')]:
 p=REPO/stage/'PAPER.md'; assert sha(p)==sh and len(p.read_text().splitlines())==n
 deps.append(dict(path=str(p),sha256=sh,full_read_lines=[1,n],role='Credited immutable ordinary input; earlier credited inputs stay credited; no inherited formal audit re-run.'))
for stage,n,sh in [('appt-critical-purity-optimizer-20261014',174,'50c5b6f1ef16d3968c5b836e5661c0946c79ca529632f7eb1c2903f01b502e36'),('appt-exact-purity-onset-20261014',118,'d6ed7d7cc541b5bfbd733e6802e6bbd4f0f593c663e678d592931a0a373d1278')]:
 p=REPO/stage/'REVIEW.md'; assert sha(p)==sh and len(p.read_text().splitlines())==n
 (OUT/('DEPENDENCY_'+stage+'_REVIEW.md')).write_bytes(p.read_bytes())
 deps.append(dict(path=str(p),sha256=sh,full_read_lines=[1,n],role='Separate prior ordinary review read; not substituted by this review.'))
claims=[
 dict(id='B0',result='PASS',domain='Entire original complex all-global-unitary APPT maximum; every integer pair in each fixed |a_m|<=A window; arbitrary varying a_m and transition crossings.',reason='Substantive W full-set identity + exact Q normalized R*V comparison + uniform rank loss + uniform C2 compact maximization + one-Lipschitz positive part.'),
 dict(id='B1',result='PASS',domain='EVERY true optimizing matrix below exact eventual onset in the whole stated window, retaining every scalar/rank tie and every unitary conjugate.',reason='W exact equality classification; every discrete winner is within O(m^-5) continuous value; strong uniform curvature gives O(m^(-5/2)) scalar distance; exact head/protection/rank formulas yield all rates.'),
 dict(id='B2',result='PASS',domain='Actual integer ranks and exact trace normalization on whole compact scalar interval.',reason='Exact trace loss gives uniformly O(m^-5) after D^2 scaling; both physical adjacent ranks retained; q exact parity loss same scale; no discontinuous-branch differentiation.'),
]
record=dict(review_kind='Independent AI subagent complete ordinary written review',reviewer='/root/ordinary_review_critical_expansion',result='PASS_COMPLETE_ORDINARY_REVIEW',timestamp_utc=datetime.now(timezone.utc).isoformat(),mathematical_revision_required=False,mathematical_changes=0,initial_complete_read=dict(PAPER=dict(lines=[1,187],sha256='f0a38d5e994dfdb3b0b2ef810b04c1f9e0db565d9afe6e72a7b86153b4f8661c'),THEOREM_MAP=dict(lines=[1,37],sha256='cd8187d302640d8bcfd899a34a54c03000f117010cd9673776924e672e26d98f'),total_math_map_lines=224),final_bindings=bindings,dependencies=deps,dependency_full_paper_lines=653,dependency_full_review_lines=292,support_full_sequential_lines=174,support_readings=support['source_readings'],author_JSON_reading=dict(raw_lines=705,all_parsed=True,all_rows_checked=48,all_source_manifest_entries_checked=4,all_candidate_values_recomputed=True,all_raw_lines_sequentially_read=False),author_test_failures=support['author_failures_preserved'],claim_checks=claims,independent_raw_runs=raw,independent_final_counts=last['counts'],independent_finite_scope='96 scalar/dimension cases with exact boundary PSD criterion and physical integer ranks; 28 mp180 candidate samples. Finite controls are not whole-domain certificates and do not compute a finite full-set optimizer oracle.',independent_test_history=dict(interrupted_run='Only verified reviewer PID was interrupted during unnecessarily expanded SymPy rational identity; initial script, partial report, and full terminal output retained. Identity verified after clearing denominators.',failed_run='An exactly zero even-parity q loss rounded to a tiny negative MP subtraction. Compare the exact parity value with a tight numerical residual rather than imposing a false strict sign on rounded zero.',passed_runs=2,second_PASS_change='Immutable initial snapshots used so final status changes do not prevent reproducing independent finite controls.',records_deleted=0,author_math_modified=False),literature=dict(primary_URL='https://arxiv.org/abs/2609.18568',actually_read='Current primary metadata and abstract only, lines 8-29 of displayed page; not 23-page proof.',finding='Bounded disclosure matches primary abstract; no matching full critical two-order claim appears in that abstract.',exhaustive_search=False,priority_certificate=False),no_Lean_execution=True,no_audit_expansion=True,no_author_checker_execution=True,no_external_human_peer_review=True,no_git_or_publication_mutation=True,not_claimed=['all dimension growth regimes','every finite m or effective cutoff','other entropy orders','ASEP','unique scalar/integer below-onset optimizer','new major-conjecture count','Lean certificate'])
scope=['complete physical-set invocation','actual rank feasibility','signed exact normalized profit','uniform rational expansion and z derivatives','stationary-displacement coefficient','compact global gap and strong curvature','uniform positive part across transition','EVERY discrete winner including ties','exact rank-base shift and true rounding','fixed-window versus all-growth/effective scope']
record['complete_review_topics']=scope
manifest=[]
for p in sorted(OUT.iterdir()):
 if p.is_file() and p.name not in ['REVIEW.json','REVIEW.md']:
  manifest.append(dict(path=p.name,sha256=sha(p),bytes=p.stat().st_size))
record['review_inputs_and_raw_records']=manifest
(OUT/'REVIEW.json').write_text(json.dumps(record,indent=2)+'\n')
md=(OUT/'MATHEMATICAL_PASS_BEFORE_FINAL_STATUS.md').read_text()
md=md.replace('# Complete independent ordinary mathematical review of B0-B2','# Independent complete source-bound ordinary review of B0-B2')
old='The final source-bound REVIEW will additionally record and check the actual\nauthor status-only changes, rather than claiming to have read future text.\nThis pre-status note does not bind files that have not yet been supplied.'
new=('The final author status/disclosure changes were independently read and\nchecked. Exact reverse replacements recover every completely read initial\nbyte and hash. There are ZERO mathematical changes and no second complete\nfinal-text reading is claimed. Actual changed lines and final hashes are:'
 if any(b['changed_lines'] for b in bindings) else
 'The current bound author files are still byte-for-byte the completely read\ninitial versions. There are ZERO changes. Later author review-status edits\nrequire a separately inspected difference/reverse-hash binding; no future\ntext is covered by this current review. Current hashes are:')
for b in bindings:
 new+='\n\n- '+b['path']+': lines '+','.join(str(x['line']) for x in b['changed_lines'])+'; final SHA-256 `'+b['final_sha256']+'`.'
new+='\n\nExact differences, snapshots, source reading scopes and every retained\nexecution record are bound in REVIEW.json.'
assert old in md
md=md.replace(old,new)
md=md.replace('All 174 support lines were read','All 174 initial support lines were read')
md=md.replace("Tran's current primary arXiv metadata and abstract were separately read;\nthe bounded literature disclosure matches them.","[Tran's current primary arXiv metadata and abstract](https://arxiv.org/abs/2609.18568)\nwere separately read; the bounded literature disclosure matches them.")
(OUT/'REVIEW.md').write_text(md)
print(json.dumps(dict(result=record['result'],REVIEW_json_sha256=sha(OUT/'REVIEW.json'),REVIEW_md_sha256=sha(OUT/'REVIEW.md'),final_hashes={b['path']:b['final_sha256'] for b in bindings}),indent=2))
