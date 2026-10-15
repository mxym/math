#!/usr/bin/env python3
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
ROOT=Path(__file__).resolve().parent
def rec(p):
    raw=p.read_bytes();return {'sha256':hashlib.sha256(raw).hexdigest(),'lines':len(raw.decode().splitlines())}
source={str(p.relative_to(ROOT)):rec(p) for p in sorted((ROOT/'snapshot/L').glob('*')) if p.is_file()}
assert source['snapshot/L/PAPER.md']=={'sha256':'c76f83bf7bb4a42eee81cafbab6fd8cdb430312fc7026503acbc86a9dfbda58b','lines':205}
text=(ROOT/'REVIEW.md').read_text()
for name,data in source.items():assert data['sha256'] in text,name
assert (ROOT.parent/'optimal-entropy-order/PAPER.md').read_bytes()==(ROOT/'snapshot/L/PAPER.md').read_bytes()
deps={str(p.relative_to(ROOT)):rec(p) for p in sorted((ROOT/'snapshot/dependencies').glob('*')) if p.is_file()}
published={str(p.relative_to(ROOT)):rec(p) for p in sorted((ROOT/'snapshot/published-inputs').rglob('*')) if p.is_file()}
old={str(p.relative_to(ROOT)):rec(p) for p in sorted((ROOT/'snapshot/L-v1').glob('*')) if p.is_file()}
runs={}
for p in sorted((ROOT/'runs').glob('*/RESULT.json')):
    r=json.loads(p.read_text());assert r['status']=='PASS'
    runs[str(p.relative_to(ROOT))]={**rec(p),'status':r['status'],'source':r['source']['L/PAPER.md']}
author={};ad=ROOT/'author-evidence';ad.mkdir(exist_ok=True)
for version,runid in (('initial','20261015T075841.189768Z'),('revised','20261015T080542.309850Z')):
    p=ROOT.parent/'optimal-entropy-order/control-runs'/runid/'RESULT.json'
    q=ad/(version+'-RESULT.json');q.write_bytes(p.read_bytes());r=json.loads(q.read_text())
    author[str(q.relative_to(ROOT))]={**rec(q),'status':r['status'],'source_sha256':r['source_sha256'],
                                      'actually_executed_by_this_reviewer':False}
record={'status':'PASS','target':'complete L0-L2 actual compact-interval entropy-order optimization',
    'review_date_local':'2026-10-15 Asia/Shanghai','bound_utc':datetime.now(timezone.utc).isoformat(),
    'review_kind':'independent internal AI-agent ordinary mathematical review',
    'reviewer':'resumed independent review agent, separate from author/root',
    'external_human_peer_review':False,'blind_review':False,'Lean':False,'old_audit_expanded':False,
    'old_I_J_K_PASS_automatically_extended':False,
    'read_scope':{'initial_L_paper':'1-192','revised_L_paper':'1-205','map':'1-35','author_checks':'1-156',
                  'author_review_history':'1-20','earlier_full_mathematical_reads':['I313','J230','K336'],
                  'new_targeted_rereads':{'I':'69-253','J':'126-205','K':'263-317'}},
    'source':source,'credited_mathematical_inputs':deps,'published_inputs':published,
    'published_input_comparison':rec(ROOT/'PUBLISHED_INPUT_COMPARISON.json'),
    'earlier_source_preserved':old,
    'reviewer_contribution':'Explicit analytic B/g identities jointly removing alpha=1 and zero-contrast factors, adopted/disclosed as (5a).',
    'new_hypotheses_added':False,'target_narrowed':False,'unresolved_mathematical_findings':[],
    'complete_scope':['compact-uniform actual-state lower barrier including alpha=1',
                      'every-order all-larger-n extended integer N, allowing infinity',
                      'closed sublevel sets and finite actual attained minimum',
                      'global compact leading slope barrier',
                      'first O(1/m) order localization before applying K',
                      'every minimizing and fixed-additive-gap order localized to O(m^-2)',
                      'actual M_I=d0*m^2+ac*m+O(1), with finite integer ties retained'],
    'independent_runs':runs,'author_runs_read_but_not_executed':author,
    'independent_script':rec(ROOT/'independent_checks.py'),'history':rec(ROOT/'CONTROL_HISTORY.md'),
    'unexpected_independent_control_failures':0,'report':rec(ROOT/'REVIEW.md'),
    'limits':['any preassigned fixed compact positive-order interval containing alpha0',
              'not the entire positive alpha axis','no growing interval or alpha to zero/infinity',
              'no full compact-uniform optimizer classification needed or asserted',
              'no effective cutoff','no exact finite minimizing set or unique order',
              'no new formal theorem, major-conjecture count or priority certificate'],
    'source_binding':'Literal revised hashes. New mathematical changes require another read; status-only metadata/README/index publication needs separate exact-diff binding.'}
(ROOT/'REVIEW.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':'PASS','paper':source['snapshot/L/PAPER.md'],'report':rec(ROOT/'REVIEW.md'),'json':rec(ROOT/'REVIEW.json')}))
