"""Four-index navigation check, independent of old three-index disposition."""
from pathlib import Path,PurePosixPath
from datetime import datetime,timezone
from urllib.parse import unquote,urlsplit
import hashlib,json,re,shutil,traceback,unicodedata,difflib
BASE=Path(__file__).resolve().parent
STAMP=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN=BASE/'runs'/STAMP;RUN.mkdir(parents=True)
shutil.copyfile(__file__,RUN/'executed_script.py')
R={'utc':STAMP,'kind':'four-index navigation and exact two-line repair only',
   'mathematical_controls_or_Lean_rerun':False,'groups':{}}
def sha(x):return hashlib.sha256(x).hexdigest()
def urls(s):return re.findall(r'\[[^\]\n]*\]\(([^\n)]*)\)',s)
def slug(s):
    s=s.strip().lower().replace('`','').replace('*','')
    return ''.join(c for c in s if not unicodedata.category(c).startswith(('P','S')) or c in '-_').replace(' ','-')
def resolve(src,path):
    bits=[]
    for b in (PurePosixPath(src).parent/PurePosixPath(path)).parts:
        if b=='.':continue
        if b=='..':bits.pop()
        else:bits.append(b)
    return '/'.join(bits)
try:
    canonical=['README.md','README.en.md','RESEARCH.md','SOLVED_PROBLEMS.md',
      'research/research-attempts-20261015/README.md',
      'research/appt-linear-phase-geometry-20261015/README.md',
      'research/appt-linear-phase-geometry-20261015/STATUS.md',
      'verification/appt-linear-phase-ordinary-20261015/README.md']
    records=[]
    for src in canonical:
        p=BASE/'base'/src;old=set(urls(p.read_text())) if p.exists() else set()
        new=(BASE/'snapshot'/src).read_text()
        assert '#已宣称解决的问题' not in new
        for target in urls(new):
            if target in old or '#' not in target or urlsplit(target).scheme:continue
            path,anchor=unquote(target).split('#',1)
            dest=resolve(src,path) if path else src
            headings=[x.lstrip('#').strip() for x in (BASE/'snapshot'/dest).read_text().splitlines() if x.startswith('#')]
            assert anchor in [slug(x) for x in headings],(src,target,dest)
            records.append({'source':src,'target':target,'fragment':anchor})
    assert any(x['source']=='SOLVED_PROBLEMS.md' and x['target']=='README.md#预印本' for x in records)
    R['groups']['new_anchor_checks']={'count':len(records),'records':records,
        'old_or_external_anchors_not_recertified':True,'known_inbound_broken_route_repaired':True}
    nav=BASE/'snapshot/verification/appt-linear-phase-ordinary-20261015/readme-organization-history/navigation-correction'
    before=(nav/'SOLVED_PROBLEMS.before.md').read_bytes();after=(BASE/'snapshot/SOLVED_PROBLEMS.md').read_bytes()
    a=before.splitlines(keepends=True);b=after.splitlines(keepends=True)
    assert [i+1 for i,(x,y) in enumerate(zip(a,b)) if x!=y]==[1,3] and len(a)==len(b)
    generated=''.join(difflib.unified_diff(before.decode().splitlines(keepends=True),after.decode().splitlines(keepends=True),fromfile='SOLVED_PROBLEMS.before.md',tofile='SOLVED_PROBLEMS.md'))
    stored=(nav/'NAVIGATION_CORRECTION.diff').read_text()
    # Historical revision replaced a three-line block, including its unchanged
    # blank separator; the reconstructed before/after bytes provide the exact
    # authoritative check rather than requiring a particular diff grouping.
    assert '-# 已宣称解决的问题与专题结果' in stored and '+# 问题与专题成果索引' in stored
    assert '-[返回首页]' in stored and '+[返回首页]' in stored
    (RUN/'EXACT_SOLVED_DIFF.diff').write_text(generated)
    R['groups']['two_line_repair']={'before_sha256':sha(before),'after_sha256':sha(after),
        'changed_one_based_lines':[1,3],'all_remaining_bytes_literal':True,
        'stored_historical_diff_sha256':sha((nav/'NAVIGATION_CORRECTION.diff').read_bytes()),
        'generated_minimal_diff_sha256':sha(generated.encode())}
    for name in ['README.md','README.en.md','RESEARCH.md','SOLVED_PROBLEMS.md']:
        assert b'\r' not in (BASE/'base'/name).read_bytes() and b'\r' not in (BASE/'snapshot'/name).read_bytes()
    R['groups']['line_endings']={'base_and_candidate_all_LF':True}
    R['status']='PASS';R['decision']='PASS'
except BaseException:
    R['status']='FAIL';R['decision']='FAIL';R['traceback']=traceback.format_exc()
finally:
    R['executed_script_sha256']=sha((RUN/'executed_script.py').read_bytes())
    (RUN/'RESULT.json').write_text(json.dumps(R,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'run':str(RUN),'status':R['status'],'groups':R['groups']},indent=2,ensure_ascii=False))
if R['status']!='PASS':print(R['traceback']);raise SystemExit(1)
