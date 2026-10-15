"""P final metadata byte checks; no mathematics, plotting or controls run."""
from pathlib import Path
from datetime import datetime, timezone
import difflib, hashlib, json, re, subprocess

HERE=Path(__file__).resolve().parent
STAGE=HERE.parent
PUB=STAGE/'growing-order-publication'
CANDIDATE=PUB/'public-sources'/'appt-growing-renyi-order-20261015'
INDEX=PUB/'index-candidates'
REVIEW=STAGE/'independent-growing-order-review'
BASE='ffe78dc5bbb5c9465af31b2b5b354ca99c76b32a'
REPO='/home/mxym/math-appt-multiscale-20261013'
manifest={'captured_utc':datetime.now(timezone.utc).isoformat(),'files':{}}

def sha(data):return hashlib.sha256(data).hexdigest()

def put(relative,data,source):
    dest=HERE/relative
    if dest.exists():assert dest.read_bytes()==data,str(dest)
    else:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
    item={'sha256':sha(data),'bytes':len(data),'lines':len(data.splitlines()),'source':source}
    manifest['files'][relative]=item
    return item

for path in sorted(CANDIDATE.rglob('*')):
    if path.is_file() and path.name!='FINAL_STATUS_BINDING.json':
        put('snapshot/candidate/'+path.relative_to(CANDIDATE).as_posix(),path.read_bytes(),str(path))
for path in INDEX.iterdir():
    if path.is_file():put('snapshot/index/'+path.name,path.read_bytes(),str(path))
put('snapshot/FINAL_SOURCE_CANDIDATE.json',(PUB/'FINAL_SOURCE_CANDIDATE.json').read_bytes(),str(PUB/'FINAL_SOURCE_CANDIDATE.json'))

def reverse(final,patch):
    lines=final.splitlines(keepends=True);changes=patch.splitlines(keepends=True)
    assert changes[0].startswith(b'--- ') and changes[1].startswith(b'+++ ')
    i,pos,out,hunks=2,0,[],[]
    while i<len(changes):
        m=re.fullmatch(rb'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@[^\n]*\n',changes[i]);assert m
        oldstart,oldcount,newstart,newcount=int(m[1]),int(m[2] or b'1'),int(m[3]),int(m[4] or b'1')
        assert pos<=newstart-1
        out.extend(lines[pos:newstart-1]);pos=newstart-1;i+=1;oldseen=newseen=0
        while i<len(changes) and not changes[i].startswith(b'@@ '):
            prefix,payload=changes[i][:1],changes[i][1:]
            assert prefix in (b' ',b'+',b'-')
            if prefix in (b' ',b'+'):
                assert lines[pos]==payload,(pos,lines[pos],payload)
                pos+=1;newseen+=1
            if prefix in (b' ',b'-'):out.append(payload);oldseen+=1
            i+=1
        assert (oldseen,newseen)==(oldcount,newcount)
        hunks.append({'old_start':oldstart,'old_count':oldcount,'new_start':newstart,'new_count':newcount})
    out.extend(lines[pos:])
    return b''.join(out),hunks

final=(CANDIDATE/'PAPER.md').read_bytes()
patch=(CANDIDATE/'FINAL_STATUS.diff').read_bytes()
old=(REVIEW/'snapshot/P-v3/PAPER.md').read_bytes()
restored,hunks=reverse(final,patch)
assert restored==old and len(hunks)==2
assert sha(old)=='3d038944ad35c16fb1c3c99db4fcc096f3a12e543016048a002c035712516e06'
assert sha(final)=='4b9a453a6187e660f2f387e4e2e82bd4721287b12f583c46b4b91c11aae05cc5'
assert sha(patch)=='c16230da02f733264c4258ff20b2f82e8f129fc8a5a0790c7e0d854a639ac025'
regen=''.join(difflib.unified_diff(old.decode().splitlines(True),final.decode().splitlines(True),
    fromfile=patch.splitlines()[0][4:].decode(),tofile=patch.splitlines()[1][4:].decode())).encode()
assert regen==patch
put('reconstructed/REVIEWED-PAPER.md',restored,'exact inverse of final status diff')
candidate_manifest=json.loads((PUB/'FINAL_SOURCE_CANDIDATE.json').read_text())
assert candidate_manifest['reviewed_paper_sha256']==sha(old)
assert candidate_manifest['final_paper_sha256']==sha(final)
assert candidate_manifest['status_diff_sha256']==sha(patch)
assert not candidate_manifest['new_math_since_frozen_review']
for name in ['THEOREM_MAP.md','checks.py','REVIEW_HISTORY.md']:
    assert (CANDIDATE/name).read_bytes()==(REVIEW/'snapshot/P-v3'/name).read_bytes()
for name in ['REVIEW.md','REVIEW.json']:
    assert (CANDIDATE/name).read_bytes()==(REVIEW/name).read_bytes()
for name in ['PAPER.md','THEOREM_MAP.md','checks.py']:
    assert (CANDIDATE/'author-versions/before-fixed-dimension-quantifier-fix'/name).read_bytes()==(REVIEW/'author-versions/before-fixed-dimension-quantifier-fix'/name).read_bytes()
for name in ['PAPER.md','THEOREM_MAP.md','checks.py','REVIEW_HISTORY.md']:
    assert (CANDIDATE/'author-versions/before-sharper-upper-rate'/name).read_bytes()==(REVIEW/'snapshot/P-v2'/name).read_bytes()
for folder in (CANDIDATE/'control-runs').iterdir():
    for path in folder.iterdir():
        if path.is_file():assert path.read_bytes()==(REVIEW/'author-evidence'/folder.name/path.name).read_bytes()

index_author=json.loads((INDEX/'INDEX_BINDINGS.json').read_text())
rows=(INDEX/'ADDED_ROWS.md').read_text()
indices={}
for name in ['README.md','README.en.md','RESEARCH.md']:
    before=subprocess.run(['git','-C',REPO,'show',BASE+':'+name],check=True,stdout=subprocess.PIPE).stdout
    after=(INDEX/name).read_bytes()
    newrows=[line for line in after.splitlines(keepends=True) if b'research/appt-growing-renyi-order-20261015/README.md' in line]
    assert len(newrows)==1 and after.count(newrows[0])==1
    assert after.replace(newrows[0],b'',1)==before
    assert newrows[0].decode().strip() in rows
    assert index_author[name]['before_sha256']==sha(before)
    assert index_author[name]['after_sha256']==sha(after) and index_author[name]['added_rows']==1
    put('snapshot/base-ffe78dc5/'+name,before,'git show '+BASE+':'+name)
    diff=''.join(difflib.unified_diff(before.decode().splitlines(True),after.decode().splitlines(True),
        fromfile=BASE+'/'+name,tofile='candidate/'+name))
    put('index-diffs/'+name+'.diff',diff.encode(),'complete generated index difference')
    indices[name]={'base_commit':BASE,'before_sha256':sha(before),'after_sha256':sha(after),
        'only_added_rows':1,'all_old_bytes_preserved':True,'added_row':newrows[0].decode().rstrip('\n')}

provenance=json.loads((CANDIDATE/'figures/PROVENANCE.json').read_text())
for name,digest in provenance['files'].items():assert sha((CANDIDATE/'figures'/name).read_bytes())==digest
assert provenance['parameters']=={'c_min':.08,'c_max':6,'samples':900,'fixed_m':[2,3,5]}
assert provenance['formula']=='max(log((m+1)/(m-1)),log(3)-1/c); joint m->infinity replaces bulk by zero'

initial=(HERE/'initial-snapshot/README.md').read_bytes()
middle=(HERE/'history/metadata-v2/README.md').read_bytes()
author_old={sha(p.read_bytes()):p for p in (CANDIDATE/'author-versions').rglob('README.md')}
assert sha(initial) in author_old and sha(middle) in author_old
assert sha(middle)=='32552bf975d27c077f2f302b5f1cac783fd317a83e265bc9d932402819c4139b'
latest=(CANDIDATE/'README.md').read_bytes()
for label,aa,bb in [('v1-to-v2',initial,middle),('v2-to-final',middle,latest)]:
    diff=''.join(difflib.unified_diff(aa.decode().splitlines(True),bb.decode().splitlines(True),
        fromfile=label+'/old-README.md',tofile=label+'/new-README.md'))
    put('history/README-'+label+'.diff',diff.encode(),'complete metadata clarification difference')

checks={'checked_utc':datetime.now(timezone.utc).isoformat(),
    'decision':'PASS','reviewed_sha256':sha(old),'final_sha256':sha(final),'status_diff_sha256':sha(patch),
    'status_hunks':hunks,'inverse_exact':True,'complete_forward_diff_exact':True,
    'mathematical_changes':False,'literal_reports_maps_scripts_history_retained':True,
    'source_versions_and_author_runs_retained_exactly':True,'index_relations':indices,
    'README_versions':{'initial_sha256':sha(initial),'middle_sha256':sha(middle),'final_sha256':sha(latest),
        'old_author_paths':{digest:str(author_old[digest].relative_to(CANDIDATE)) for digest in [sha(initial),sha(middle)]}},
    'figure':{'provenance':provenance,'file_hashes_match':True,'source_read':True,
        'plot_executed_by_reviewer':False,'PNG_visually_inspected_by_reviewer':False,
        'finite_extrema_or_plot_execution_semantics_certified':False},
    'mathematical_or_author_controls_executed':False,'Lean_executed':False,
    'future_evidence_layout_verified':False,
    'planned_evidence_reference':'verification/appt-growing-order-ordinary-20261015/README.md'}
(HERE/'INPUT_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
(HERE/'BYTE_CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps({'decision':'PASS','snapshot_files':len(manifest['files']),
    'inverse_exact':True,'indices_one_row_only':list(indices),
    'README_final_sha256':sha(latest),'figure_hash_matches':True,'controls_rerun':False,
    'future_evidence_layout_verified':False}))
