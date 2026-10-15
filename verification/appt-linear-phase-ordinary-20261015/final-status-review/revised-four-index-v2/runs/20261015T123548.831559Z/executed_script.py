"""Destination-based canonical navigation check including nested label brackets.

The previous independent checker correctly recorded 630 checked targets; its
label regex skipped two Z[sqrt(-2)] link labels in SOLVED_PROBLEMS. This new
execution checks all 632 destinations and preserves the earlier exact result.
"""
from pathlib import Path
from datetime import datetime,timezone
from urllib.parse import urlsplit,unquote
import hashlib,json,posixpath,re,shutil,subprocess,traceback
BASE=Path(__file__).resolve().parent
STAMP=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN=BASE/'runs'/STAMP;RUN.mkdir(parents=True)
shutil.copyfile(__file__,RUN/'executed_script.py')
R={'utc':STAMP,'kind':'all current canonical file/directory destinations, metadata only',
   'mathematical_or_Lean_controls_executed':False,'groups':{}}
try:
    m=json.loads((BASE/'input-records/FINAL_CANDIDATE_INPUTS.json').read_text())
    assert m['source_base']=='49f572d05df426fe9cfc36126dfea6accc6d5407'
    paths=set(subprocess.check_output(['git','-C','/home/mxym/math-appt-multiscale-20261013',
       'ls-tree','-r','--name-only',m['source_base']],text=True).splitlines())|set(m['files'])
    canonical=['README.md','README.en.md','RESEARCH.md','SOLVED_PROBLEMS.md',
       'research/appt-linear-phase-geometry-20261015/README.md',
       'research/appt-linear-phase-geometry-20261015/STATUS.md',
       'verification/appt-linear-phase-ordinary-20261015/README.md',
       'research/research-attempts-20261015/README.md']
    records=[];pending=[]
    for src in canonical:
        for raw in re.findall(r'\]\(([^)\n]+)\)',(BASE/'snapshot'/src).read_text()):
            u=unquote(raw.strip('<>'))
            if urlsplit(u).scheme:continue
            name=u.split('#',1)[0].split('?',1)[0]
            if not name:continue
            dest=posixpath.normpath(posixpath.join(posixpath.dirname(src),name))
            assert not dest.startswith('../') and not dest.startswith('/')
            if dest in [prefix+'/FINAL_STATUS_BINDING.json' for prefix in m['new_projects'].values()]:
                pending.append({'source':src,'target':u,'resolved':dest});continue
            assert dest in paths or any(x.startswith(dest.rstrip('/')+'/') for x in paths),(src,u,dest)
            records.append({'source':src,'target':u,'resolved':dest})
    assert len(records)==632
    for path in ['notes/sqrt-minus-two-sharp-moats/README.md','notes/sqrt-minus-two-sqrt6-period/README.md']:
        assert any(x['source']=='SOLVED_PROBLEMS.md' and x['target']==path for x in records)
    (RUN/'CANONICAL_LINKS.json').write_text(json.dumps(records,indent=2,ensure_ascii=False)+'\n')
    R['groups']['canonical_targets']={'sources':canonical,'existing_destinations_checked':len(records),
      'future_self_binding_excluded':pending,'nested_label_bracket_targets_included':[
         'notes/sqrt-minus-two-sharp-moats/README.md','notes/sqrt-minus-two-sqrt6-period/README.md'],
      'earlier_630_result_unchanged':True,'new_anchor_check_separate':'20261015T123426.549666Z',
      'whole_repository_historical_inbound_anchor_audit':False,'external_URLs_fetched':False}
    R['status']='PASS';R['decision']='PASS'
except BaseException:
    R['status']='FAIL';R['decision']='FAIL';R['traceback']=traceback.format_exc()
finally:
    R['executed_script_sha256']=hashlib.sha256((RUN/'executed_script.py').read_bytes()).hexdigest()
    (RUN/'RESULT.json').write_text(json.dumps(R,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'run':str(RUN),'status':R['status'],'groups':R['groups']},indent=2,ensure_ascii=False))
if R['status']!='PASS':print(R['traceback']);raise SystemExit(1)
