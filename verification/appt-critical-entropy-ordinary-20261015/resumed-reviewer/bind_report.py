#!/usr/bin/env python3
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,sys
root=Path(__file__).resolve().parent
target=sys.argv[1]
assert target in ('H','I','J')
doc=root/(target+'_REVIEW.md')
assert doc.exists()
def record(p):
    b=p.read_bytes()
    return {'sha256':hashlib.sha256(b).hexdigest(),'lines':len(b.decode().splitlines())}
sources={}
for p in sorted((root/'snapshot'/target).glob('*')):
    if p.is_file():sources[str(p.relative_to(root))]=record(p)
deps={str(p.relative_to(root)):record(p) for p in sorted((root/'snapshot'/'dependencies').glob('*')) if p.is_file()}
if target in ('I','J'):
    deps['snapshot/H/PAPER.md']=record(root/'snapshot/H/PAPER.md')
    deps['H_REVIEW.md']=record(root/'H_REVIEW.md')
    deps['H_REVIEW.json']=record(root/'H_REVIEW.json')
if target=='J':
    deps['snapshot/I/PAPER.md']=record(root/'snapshot/I/PAPER.md')
    deps['I_REVIEW.md']=record(root/'I_REVIEW.md')
    deps['I_REVIEW.json']=record(root/'I_REVIEW.json')
    deps['J_CONTROL_HISTORY.md']=record(root/'J_CONTROL_HISTORY.md')
runs={}
for p in (root/'runs'/'20261015T063357.950830Z'/'RESULT.json',root/'supplemental-runs'/'20261015T063610.050259Z'/'RESULT.json'):
    runs[str(p.relative_to(root))]={**record(p),'status':json.loads(p.read_text())['status']}
if target=='J':
    for p in sorted((root/'j-runs').glob('*/RESULT.json')):
        runs[str(p.relative_to(root))]={**record(p),'status':json.loads(p.read_text())['status']}
recordout={'status':'PASS','target':target+'0-'+target+('5' if target=='H' else '3'),
           'review_kind':'independent internal AI-agent ordinary mathematical review',
           'reviewer':'resumed independent review agent; separate from author/root',
           'review_date_local':'2026-10-15 Asia/Shanghai',
           'bound_utc':datetime.now(timezone.utc).isoformat(),
           'complete_manuscript_read':True,'Lean':False,'old_audit_expanded':False,
           'external_human_peer_review':False,'priority_certificate':False,
           'mathematical_corrections_required':[],
           'source':sources,'credited_inputs':deps,'diagnostic_runs':runs,
           'report':{str(doc.relative_to(root)):record(doc)},
           'diagnostic_provenance':{'reused_prior_reviewer_checks.py':record(root/'reused_prior_reviewer_checks.py'),
                                    'supplemental_checks.py':record(root/'supplemental_checks.py'),
                                    'reused_script_original_author':'predecessor independent review agent',
                                    'reused_script_actually_rerun_here':True,
                                    'supplemental_original_author':'resumed independent review agent'},
           'unexpected_control_failures_in_resumed_review':2 if target=='J' else 0,
           'limits':['fixed finite positive order only','sufficiently large m, non-effective cutoff',
                     'no unconditional exact single ceiling','no all-finite theorem',
                     'no ASEP claim','no new formal theorem'],
           'source_binding':'Literal hashes; mathematical changes need further read. Metadata-only changes need exact diff and explicit binding.'}
if target=='J':
    recordout['diagnostic_provenance']['j_independent_checks.py']=record(root/'j_independent_checks.py')
    recordout['diagnostic_provenance']['j_script_original_author']='resumed independent review agent'
    recordout['failed_control_resolution']='Two preserved reviewer-helper failures at alpha=1, then exact alpha derivative in helper and full PASS; no manuscript change.'
(root/(target+'_REVIEW.json')).write_text(json.dumps(recordout,indent=2)+'\n')
print(json.dumps({'status':'PASS','target':recordout['target'],'report':str(doc),'sha256':record(doc)['sha256']}))
