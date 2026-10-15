"""New navigation anchors and exact historical layout patch, private only."""
from pathlib import Path,PurePosixPath
from datetime import datetime,timezone
from urllib.parse import unquote,urlsplit
import hashlib,json,re,shutil,traceback,unicodedata
BASE=Path(__file__).resolve().parent
SNAP=BASE/'snapshot'
STAMP=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN=BASE/'runs'/STAMP;RUN.mkdir(parents=True)
shutil.copyfile(__file__,RUN/'executed_script.py')
R={'kind':'independent new navigation and historical metadata byte checks',
   'mathematical_or_Lean_controls_executed':False,'utc':STAMP,'groups':{}}
def sha(b):return hashlib.sha256(b).hexdigest()
def urls(t):return re.findall(r'\[[^\]\n]*\]\(([^\n)]*)\)',t)
def slug(s):
    s=s.strip().lower().replace('`','').replace('*','')
    return ''.join(ch for ch in s if not unicodedata.category(ch).startswith(('P','S')) or ch in '-_').replace(' ','-')
def resolve(src,path):
    bits=[]
    for b in (PurePosixPath(src).parent/PurePosixPath(path)).parts:
        if b=='.':continue
        if b=='..':bits.pop()
        else:bits.append(b)
    return '/'.join(bits)
def apply_hunks(original,lines):
    old=original.splitlines(keepends=True);out=[];cursor=0;i=0
    while i<len(lines):
        m=re.match(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',lines[i])
        if not m:i+=1;continue
        start=int(m[1])-1;oc=int(m[2] or 1);nc=int(m[4] or 1)
        assert start>=cursor
        out.extend(old[cursor:start]);cursor=start;i+=1;oldused=0;newused=0
        while oldused<oc or newused<nc:
            line=lines[i];assert line[0] in ' +-'
            if line[0] in ' -':assert old[cursor]==line[1:],(cursor,old[cursor],line);cursor+=1;oldused+=1
            if line[0] in ' +':out.append(line[1:]);newused+=1
            i+=1
        assert oldused==oc and newused==nc
    out.extend(old[cursor:]);return ''.join(out)
try:
    canonical=['README.md','README.en.md','research/research-attempts-20261015/README.md',
      'research/appt-linear-phase-geometry-20261015/README.md',
      'research/appt-linear-phase-geometry-20261015/STATUS.md',
      'verification/appt-linear-phase-ordinary-20261015/README.md']
    records=[]
    for src in canonical:
        old=set(urls((BASE/'base'/src).read_text())) if (BASE/'base'/src).exists() else set()
        for target in urls((SNAP/src).read_text()):
            if target in old or '#' not in target or urlsplit(target).scheme:continue
            p,anchor=unquote(target).split('#',1)
            path=resolve(src,p) if p else src
            headings=[line.lstrip('#').strip() for line in (SNAP/path).read_text().splitlines() if line.startswith('#')]
            assert anchor in [slug(x) for x in headings],(src,target,path,headings)
            records.append({'source':src,'target':target,'heading_fragment':anchor})
    R['groups']['new_anchor_checks']={'count':len(records),'records':records,'old_external_or_unchanged_anchors_not_recertified':True}
    hist=SNAP/'verification/appt-linear-phase-ordinary-20261015/readme-organization-history'
    patch=(hist/'LAYOUT_CORRECTION.diff').read_text().splitlines(keepends=True)
    starts=[i for i,x in enumerate(patch) if x.startswith('--- v1/')];starts.append(len(patch))
    outputs=[]
    for z in range(len(starts)-1):
        chunk=patch[starts[z]:starts[z+1]];name=chunk[0].strip().removeprefix('--- v1/')
        initial=(hist/'layout-history/before-table-placement-fix'/name).read_text()
        corrected=apply_hunks(initial,chunk[2:])
        current=(SNAP/name).read_text()
        newlines=[line for line in current.splitlines(keepends=True) if 'appt-linear-phase-geometry-20261015/README.md' in line]
        assert len(newlines)==1
        assert corrected==current.replace(newlines[0],'')
        dst=RUN/('reconstructed-'+name);dst.write_text(corrected)
        outputs.append({'name':name,'original_sha256':sha(initial.encode()),'reconstructed_sha256':sha(corrected.encode()),
              'exact_current_candidate_after_removing_only_new_phase_row':True})
    assert len(outputs)==2
    R['groups']['layout_patch']={'files':outputs,'history_finding_preserved':True,'current_binding_does_not_relabel_historical_SHA':True}
    first=BASE/'runs/20261015T122151.779216Z/executed_script.py'
    final=BASE/'runs/20261015T122213.681966Z/executed_script.py'
    import difflib
    diff=''.join(difflib.unified_diff(first.read_text().splitlines(keepends=True),final.read_text().splitlines(keepends=True),fromfile='first-failed-checker',tofile='corrected-checker'))
    assert "p.name!='FINAL_STATUS_BINDING.json'" in diff
    assert "p.relative_to(STAGE/'public-sources'/name)!=Path('FINAL_STATUS_BINDING.json')" in diff
    (BASE/'CHECKER_CORRECTION.diff').write_text(diff)
    R['groups']['real_failure_preservation']={'first_run':'20261015T122151.779216Z','later_run':'20261015T122213.681966Z',
        'cause':'reviewer checker excluded historical binding basenames, corrected only to root-relative exclusion',
        'exact_diff_sha256':sha(diff.encode()),'candidate_source_changed':False}
    R['status']='PASS';R['decision']='PASS'
except BaseException:
    R['status']='FAIL';R['decision']='FAIL';R['traceback']=traceback.format_exc()
finally:
    R['executed_script_sha256']=sha((RUN/'executed_script.py').read_bytes())
    (RUN/'RESULT.json').write_text(json.dumps(R,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'run':str(RUN),'status':R['status'],'groups':R['groups']},indent=2,ensure_ascii=False))
if R['status']!='PASS':print(R['traceback']);raise SystemExit(1)
