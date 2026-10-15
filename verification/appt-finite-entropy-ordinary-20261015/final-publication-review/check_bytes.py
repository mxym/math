"""Byte/status binding only. No mathematical or author checker execution."""
from pathlib import Path
from datetime import datetime,timezone
import re,json,hashlib,difflib,subprocess,traceback

base=Path(__file__).resolve().parent
stage=base.parent/'finite-han-publication'
snap=base/'snapshot';snap.mkdir(parents=True,exist_ok=True)
sha=lambda data:hashlib.sha256(data).hexdigest()
files={}
def capture(source,relative):
    data=source.read_bytes();target=snap/relative;target.parent.mkdir(parents=True,exist_ok=True)
    if target.exists():assert target.read_bytes()==data,str(relative)
    else:target.write_bytes(data)
    files[str(relative)]={'sha256':sha(data),'bytes':len(data),'lines':len(data.splitlines())}
def patch(data,diff,reverse=False):
    old=data.splitlines(keepends=True);rows=diff.splitlines(keepends=True)
    result=[];cursor=0;i=0;hunks=0
    while i<len(rows):
        row=rows[i]
        if not row.startswith(b'@@ '):i+=1;continue
        match=re.match(rb'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',row);assert match,row
        oldstart=int(match[1]);oldcount=int(match[2] or b'1');newstart=int(match[3]);newcount=int(match[4] or b'1')
        start,count=(newstart,newcount) if reverse else (oldstart,oldcount)
        pos=start if count==0 else start-1
        assert pos>=cursor
        result.extend(old[cursor:pos]);cursor=pos;used=made=0;i+=1
        while i<len(rows) and not rows[i].startswith(b'@@ '):
            row=rows[i]
            if not row or row[:1] not in [b' ',b'+',b'-']:break
            action=row[:1];payload=row[1:]
            if reverse:action={b'+':b'-',b'-':b'+',b' ':b' '}[action]
            if action in [b' ',b'-']:
                assert cursor<len(old) and old[cursor]==payload,(cursor,row,old[cursor] if cursor<len(old) else b'EOF')
                cursor+=1;used+=1
            if action in [b' ',b'+']:result.append(payload);made+=1
            i+=1
        expected=(newcount,oldcount) if reverse else (oldcount,newcount)
        assert (used,made)==expected,(used,made,expected)
        hunks+=1
    result.extend(old[cursor:]);assert hunks>0
    return b''.join(result),hunks

try:
    capture(stage/'FINAL_SOURCE_CANDIDATES.json',Path('FINAL_SOURCE_CANDIDATES.json'))
    for folder in ['public-sources','index-candidates','index-candidate-history']:
        for p in sorted((stage/folder).rglob('*')):
            if p.is_file() and p.name!='FINAL_STATUS_BINDING.json':capture(p,p.relative_to(stage))
    spec=json.loads((stage/'FINAL_SOURCE_CANDIDATES.json').read_text())
    review_paths={
      'appt-finite-entropy-bounds-20261015':('independent-all-aspect-orders-review','snapshot-v2','PAPER.md'),
      'han-fourier-overlap-20261015':('independent-han-q31-review-20261015','snapshot-v2','HAN_QUESTION_3_1_NEGATIVE_ANSWER.md'),
      'appt-linear-critical-rigidity-20261015':('independent-linear-critical-rigidity-review','snapshot','PAPER.md')}
    source_relations={}
    for project,(reviewdir,snapshot,papername) in review_paths.items():
        candidate=stage/'public-sources'/project;review=base.parent/reviewdir
        previous=(review/snapshot/papername).read_bytes();final=(candidate/'PAPER.md').read_bytes();diff=(candidate/'FINAL_STATUS.diff').read_bytes()
        assert sha(previous)==spec[project]['reviewed_paper_sha256']
        assert sha(final)==spec[project]['final_paper_sha256']
        assert sha(diff)==spec[project]['status_diff_sha256']
        back,hunks=patch(final,diff,True);assert back==previous
        forward,_=patch(previous,diff);assert forward==final
        for name in ['REVIEW.md','REVIEW.json']:assert (candidate/name).read_bytes()==(review/name).read_bytes(),(project,name)
        source_relations[project]={'reviewed_paper_sha256':sha(previous),'final_paper_sha256':sha(final),'paper_diff_sha256':sha(diff),'paper_hunks':hunks,'reverse_restores_own_math_snapshot_exactly':True,'forward_from_own_math_snapshot_exactly_matches_final':True,'literal_original_REVIEW_md_json_preserved':True}
        if 'map_relation' in spec[project]:
            oldmap=(review/snapshot/'THEOREM_MAP.md').read_bytes();newmap=(candidate/'THEOREM_MAP.md').read_bytes();mdiff=(candidate/'FINAL_STATUS_MAP.diff').read_bytes()
            mapspec=spec[project]['map_relation']
            assert sha(oldmap)==mapspec['reviewed_sha256'];assert sha(newmap)==mapspec['final_sha256'];assert sha(mdiff)==mapspec['status_diff_sha256']
            assert patch(newmap,mdiff,True)[0]==oldmap;assert patch(oldmap,mdiff)[0]==newmap
            preserved=candidate/'author-versions/final-reviewed-mathematical-source'
            assert (preserved/'PAPER.md').read_bytes()==previous;assert (preserved/'THEOREM_MAP.md').read_bytes()==oldmap
            source_relations[project]['map']={**mapspec,'reverse_restores_own_snapshot_exactly':True,'preserved_original_math_source_and_map':True}
    # R runtime metadata: exact reviewed pre-append log and old requirements preserved.
    R=stage/'public-sources/appt-finite-entropy-bounds-20261015';oldR=base.parent/'independent-all-aspect-orders-review'
    oldlog=(oldR/'snapshot-v2/RESEARCH_LOG.md').read_bytes();newlog=(R/'RESEARCH_LOG.md').read_bytes()
    assert (R/'author-versions/before-runtime-metadata-correction/RESEARCH_LOG.md').read_bytes()==oldlog
    assert newlog.startswith(oldlog)
    (base/'R_RUNTIME_APPEND.txt').write_bytes(newlog[len(oldlog):])
    assert (R/'author-versions/before-runtime-metadata-correction/requirements.txt').read_bytes()==(oldR/'snapshot/requirements.txt').read_bytes()
    assert (R/'requirements.txt').read_bytes()==b'mpmath==1.2.1\n'
    runtime={'old_log_sha256':sha(oldlog),'new_log_sha256':sha(newlog),'only_appended':True,'append_sha256':sha(newlog[len(oldlog):]),'old_requirement':(oldR/'snapshot/requirements.txt').read_text().strip(),'new_requirement':(R/'requirements.txt').read_text().strip(),'old_pin_and_reviewed_log_preserved':True}
    # Both Han immutable version packets and canonical renamed controls are literal.
    H=stage/'public-sources/han-fourier-overlap-20261015';oldH=base.parent/'independent-han-q31-review-20261015'
    for oldfolder,newfolder in [('snapshot','review-v1'),('snapshot-v2','review-v2')]:
        for p in (oldH/oldfolder).iterdir():
            if p.is_file():assert (H/'author-versions'/newfolder/p.name).read_bytes()==p.read_bytes(),p.name
    assert (H/'HAN_Q31_TARGET_AND_SOURCE_MAP.json').read_bytes()==(oldH/'snapshot-v2/HAN_Q31_TARGET_AND_SOURCE_MAP.json').read_bytes()
    assert (H/'han_q31_exact_controls.py').read_bytes()==(oldH/'snapshot-v2/han_q31_exact_controls.py').read_bytes()
    assert (H/'AUTHOR_CONTROLS.json').read_bytes()==(oldH/'snapshot-v2/HAN_Q31_EXACT_CONTROLS.json').read_bytes()
    historical=json.loads((H/'HISTORICAL_INPUTS.json').read_text())
    tcs='/home/mxym/math-breadth-tcs-20261015'
    allnames=subprocess.check_output(['git','-C',tcs,'ls-tree','-r','--name-only',historical['source_commit']]).decode().splitlines()
    history_checks={}
    for name,digest in historical['files'].items():
        matches=[p for p in allnames if p.endswith('/'+name) or p==name];assert len(matches)==1,(name,matches)
        data=(H/name).read_bytes();assert sha(data)==digest
        assert data==subprocess.check_output(['git','-C',tcs,'show',historical['source_commit']+':'+matches[0]])
        history_checks[name]={'sha256':digest,'source_path':matches[0],'literal_commit_bytes':True,'new_full_math_review':False}
    # New rows only: remove them and demand exact immutable old index bytes.
    index=stage/'index-candidates';bindings=json.loads((index/'INDEX_BINDINGS.json').read_text())
    additions={};current=None
    for row in (index/'ADDED_ROWS.md').read_bytes().splitlines(keepends=True):
        title=row.decode().strip()
        if title in bindings:current=title;additions[current]=[]
        elif row.startswith(b'|'):assert current is not None;additions[current].append(row)
    indexes={};root='/home/mxym/math-appt-multiscale-20261013';commit='665e9e26d43fa83cb7eb6823cd2cd56b1ac08680'
    for name,spec0 in bindings.items():
        previous=subprocess.check_output(['git','-C',root,'show',commit+':'+name]);final=(index/name).read_bytes()
        assert sha(previous)==spec0['before_sha256'];assert sha(final)==spec0['after_sha256']
        rows=additions[name];assert len(rows)==3
        for row in rows:assert final.count(row)==1
        stripped=b''.join(row for row in final.splitlines(keepends=True) if row not in rows)
        assert stripped==previous,(name,'old index bytes changed')
        diff=''.join(difflib.unified_diff(previous.decode().splitlines(True),final.decode().splitlines(True),fromfile='immutable665e/'+name,tofile='candidate/'+name))
        (base/(name.replace('.','_')+'.diff')).write_text(diff)
        indexes[name]={**spec0,'immutable_base':commit,'old_bytes_exactly_preserved':True,'exact_new_rows':[r.decode().rstrip('\n') for r in rows]}
    out={'status':'PASS','utc':datetime.now(timezone.utc).isoformat(),'files':files,'source_relations':source_relations,'R_runtime_metadata':runtime,'Han_v1_v2_and_canonical_bytes':True,'Han_historical_files':history_checks,'indexes':indexes,'new_math_read':False,'math_controls_executed':False,'Lean':False,'future_evidence_layout_checked':False}
    (base/'BYTE_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'PASS','captured_files':len(files),'paper_reverse_checks':3,'map_reverse_checks':2,'three_indexes_old_bytes_preserved':True,'R_runtime_append':newlog[len(oldlog):].decode()},indent=2))
except Exception:
    (base/'BYTE_CHECKS_FAILURE.json').write_text(json.dumps({'status':'FAIL','utc':datetime.now(timezone.utc).isoformat(),'traceback':traceback.format_exc(),'math_controls_executed':False},indent=2)+'\n')
    raise
