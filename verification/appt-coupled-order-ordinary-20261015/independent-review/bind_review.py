#!/usr/bin/env python3
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json

ROOT=Path(__file__).resolve().parent
def record(p):
    raw=p.read_bytes()
    return {'sha256':hashlib.sha256(raw).hexdigest(),'lines':len(raw.decode().splitlines())}
source={str(p.relative_to(ROOT)):record(p) for p in sorted((ROOT/'snapshot/K').glob('*')) if p.is_file()}
assert source['snapshot/K/PAPER.md']['sha256']=='efba5e8ef99af23d69081c958dbd0f0fb1a95ef967807b7038179d9a6da0b0d5'
assert source['snapshot/K/PAPER.md']['lines']==336
assert (ROOT.parent/'coupled-order-review-input-v2/PAPER.md').read_bytes()==(ROOT/'snapshot/K/PAPER.md').read_bytes()
deps={str(p.relative_to(ROOT)):record(p) for p in sorted((ROOT/'snapshot/dependencies').glob('*')) if p.is_file()}
previous={str(p.relative_to(ROOT)):record(p) for p in sorted((ROOT/'snapshot/K-v1').glob('*')) if p.is_file()}
runs={}
for p in sorted((ROOT/'runs').glob('*/RESULT.json')):
    r=json.loads(p.read_text());runs[str(p.relative_to(ROOT))]={**record(p),'status':r['status'],'bound_paper':r['source']['K/PAPER.md']}
    assert r['status']=='PASS'
author={}
ad=ROOT/'author-evidence';ad.mkdir(exist_ok=True)
for version,runid in (('initial','20261015T072309.730072Z'),('revised','20261015T073120.266026Z')):
    p=ROOT.parent/'coupled-order-window/control-runs'/runid/'RESULT.json'
    q=ad/(version+'-RESULT.json');q.write_bytes(p.read_bytes())
    r=json.loads(q.read_text());author[str(q.relative_to(ROOT))]={**record(q),'status':r['status'],
                          'source_sha256':r['source_sha256'],'actually_executed_by_this_reviewer':False}
result={
 'status':'PASS','target':'complete K0-K3 moving-order theorem','review_date_local':'2026-10-15 Asia/Shanghai',
 'bound_utc':datetime.now(timezone.utc).isoformat(),
 'review_kind':'independent internal AI-agent ordinary mathematical review',
 'reviewer':'resumed independent review agent, separate from root/author',
 'external_human_peer_review':False,'blind_review':False,'Lean':False,'old_audit_expanded':False,
 'automatic_extension_of_old_H_I_J_review':False,
 'complete_current_manuscript_read':True,'complete_target_map_read':True,
 'read_scope':{'current_K_paper':'1-336','original_K_paper':'1-321','map':'1-44',
               'author_checks':'1-145','author_review_history':'1-18',
               'previous_full_reads_in_same_agent_session':['C461','E377','H681','I313','J230'],
               'new_targeted_uniformity_rereads':{'C':'136-445','E':'61-320','H':'239-478','I':'77-280','J':'63-205'}},
 'source':source,'credited_inputs':deps,'earlier_source':previous,
 'review_findings':[{'finding':'Equation (8) additive O(c/m) must be explicitly in the coupled bounded-delta band.',
                     'resolved':True,'resolution':'Explicit IN THE COUPLED BAND (2) in revised source; Section 5 retains delta coefficient globally.',
                     'K0_K3_target_narrowed':False}],
 'reviewer_contribution':'Independently derived full-z R coefficient supplied during review and adopted/disclosed by author in revised source.',
 'independent_runs':runs,'author_runs_read_but_not_executed':author,
 'unexpected_independent_control_failures':0,
 'history':record(ROOT/'CONTROL_HISTORY.md'),
 'independent_script':record(ROOT/'independent_checks.py'),
 'report':record(ROOT/'REVIEW.md'),
 'complete_mathematical_scope':['uniform actual all-global-unitary APPT optimizer classification',
                              'moving-kernel all-list localization and nonnegative body loss',
                              'exact tiny-tail and boundary equality with all matrix/rank ties',
                              'mD actual value law with uniform O(1/m) remainder',
                              'every actual nonbulk z parameter O(1/m)',
                              'fixed positive branch gap selection',
                              'uniform all-larger-n proof at unbounded dimension ratio',
                              'minimal FINAL onset and two-ceiling enclosure'],
 'limits':['fixed U,A only, alpha=alpha0+u/m','non-effective starting dimension',
           'no arbitrary moving alpha','no unconditional single ceiling','no exact finite transition count',
           'no ASEP claim','no priority certificate','no new major-conjecture count'],
 'source_binding':'Literal revised hashes. New mathematical changes require another read; final metadata/README edits require a separate exact-diff binding.'}
(ROOT/'REVIEW.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','paper':source['snapshot/K/PAPER.md'],
                  'report':record(ROOT/'REVIEW.md'),'json':record(ROOT/'REVIEW.json')}))
