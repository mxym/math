"""Independent metadata/source/index check only. No mathematical controls,
author preflight, Lean, network or Git mutations are executed.
"""
from pathlib import Path
from collections import Counter
from decimal import Decimal
import datetime,difflib,hashlib,json,posixpath,re,subprocess,traceback,urllib.parse

R=Path(__file__).resolve().parent;S=R/'candidate-snapshot'
REPO=Path('/home/mxym/math-appt-multiscale-20261013')
BASE='5bbb10af2b165ce9bec56ba4cb929733496cf192'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
digest=lambda b:hashlib.sha256(b).hexdigest()
load=lambda p:json.loads(p.read_text())
dump=lambda p,x:p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
git=lambda repo,*a:subprocess.check_output(['git','-C',str(repo),*a])

def links(text):
    return re.findall(r'\]\(([^\r\n]*?)\)',text)

def anchors(text):
    out=set(re.findall(r'\b(?:id|name)=["\x27]([^"\x27]+)["\x27]',text));seen={}
    in_fence=False
    for line in text.splitlines():
        if line.lstrip().startswith(('```','~~~')):in_fence=not in_fence;continue
        if in_fence:continue
        m=re.match(r'^ {0,3}#{1,6}\s+(.+?)\s*#*\s*$',line)
        if not m:continue
        title=re.sub(r'<[^>]*>','',m.group(1)).lower()
        slug=''.join(c for c in title if c.isalnum() or c in ' _-')
        slug=slug.replace(' ','-');idx=seen.get(slug,0);seen[slug]=idx+1
        out.add(slug+('-'+str(idx) if idx else ''))
    return out

def perform(folder,result):
    mf=load(S/'FINAL_CANDIDATE_INPUTS.json')
    assert mf['source_base']==BASE and set(mf['mathematical_scopes'])=={'X','S5','S6','Zloss'}
    assert len(mf['files'])==499 and set(mf['files'])==set(mf['stage_file_lookup'])
    for rel,x in mf['files'].items():
        p=S/mf['stage_file_lookup'][rel]
        assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],rel
    result['manifest_input_files_verified']=499
    prep=load(S/'SOURCE_PREPARATION.json')
    own={
     'X':R.parent/'independent-all-dimension-positive-entropy-review-20261015',
     'S5':R.parent/'independent-sublinear-rigidity-review-20261015',
     'S6':R.parent/'independent-growing-peak-rigidity-review-20261015',
     'Zloss':R.parent/'independent-zero-order-all-path-losses-review-20261015'}
    manifests={'X':('AUTHOR_V2_MANIFEST.json','00a0de17b10d77c8844a7d482fac5f991708c8079b950739c7a809ac1e19db0e'),
               'S5':('AUTHOR_V1_MANIFEST.json','2d415d69e3728fb2b26f46ff9f866d067ead83efbc12b22f0fd4f1dec88586b8'),
               'S6':('AUTHOR_V1_MANIFEST.json','c3ac74c2808473892a46302a934a59fa0dc9d9063b4e77ab7b386fa264086b1e'),
               'Zloss':('AUTHOR_V1_MANIFEST.json','9b9a598a79fba70f1ae10a8a094a4651d5fb9b54ee9b589dd772dbf6ff6a367e')}
    scopes={}
    for scope,x in prep['scopes'].items():
        pub=S/'public-sources'/x['destination']
        roots=[p.parent for p in own[scope].rglob(manifests[scope][0]) if sha(p)==manifests[scope][1]]
        assert len(roots)==1,(scope,roots)
        private=roots[0]
        actual_files={p.relative_to(pub).as_posix() for p in pub.rglob('*') if p.is_file()}
        expected_extra={'INDEPENDENT_REVIEW.md','INDEPENDENT_REVIEW.json'} if scope in ['X','S5','S6'] else set()
        assert actual_files==set(x['source_files'])|expected_extra,scope
        for ext in ['md','json']:
            if expected_extra:
                assert (pub/('INDEPENDENT_REVIEW.'+ext)).read_bytes()==(own[scope]/('REVIEW.'+ext)).read_bytes()
        for rel,v in x['source_files'].items():
            assert (pub/rel).read_bytes()==(private/rel).read_bytes(),(scope,rel)
            assert sha(pub/rel)==v['sha256'] and (pub/rel).stat().st_size==v['bytes']
        assert sha(pub/'PAPER.md')==mf['mathematical_scopes'][scope]['paper_sha256']
        if scope in ['X','Zloss']:
            wrapper=pub.parent
            for ext in ['md','json']:assert (wrapper/('REVIEW.'+ext)).read_bytes()==(own[scope]/('REVIEW.'+ext)).read_bytes()
        else:
            for ext in ['md','json']:assert (pub/('INDEPENDENT_REVIEW.'+ext)).read_bytes()==(own[scope]/('REVIEW.'+ext)).read_bytes()
        scopes[scope]={'paper_sha256':sha(pub/'PAPER.md'),'owner_source_files_literal':len(x['source_files']),
                       'additional_literal_independent_report_copies':len(expected_extra),
                       'original_private_source':str(private),'review_md_sha256':sha(own[scope]/'REVIEW.md'),
                       'review_json_sha256':sha(own[scope]/'REVIEW.json')}
    result['mathematical_scopes_source_bytes_only']=scopes

    evidence=S/'public-sources/appt-entropy-spectrum-ordinary-20261015'
    copies=load(evidence/'PUBLIC_EVIDENCE_COPY_BINDINGS.json');copy_results={}
    all_omissions=[]
    for scope,rec in copies.items():
        priv=Path(rec['private_source']);pub=evidence/scope
        assert priv.resolve()==own[scope].resolve(),scope
        declared=rec['copied_durable_files'];omitted=rec['explicit_omissions']
        dur={p.relative_to(priv).as_posix() for p in priv.rglob('*') if p.is_file() and p.suffix!='.pyc' and '__pycache__' not in p.parts}
        assert dur==set(declared)|set(omitted),(scope,sorted(dur-set(declared)-set(omitted)))
        actual={p.relative_to(pub).as_posix() for p in pub.rglob('*') if p.is_file()}
        assert actual==set(declared),(scope,sorted(actual-set(declared)),sorted(set(declared)-actual))
        for rel,x in declared.items():
            assert (pub/rel).read_bytes()==(priv/rel).read_bytes(),(scope,rel)
            assert sha(pub/rel)==x['sha256'] and (pub/rel).stat().st_size==x['bytes']
        for rel,x in omitted.items():
            assert scope=='X' and rel=='private-primary-evidence/official-retrieval.json'
            assert not (pub/rel).exists() and (priv/rel).is_file()
            assert sha(priv/rel)==x['sha256']
            all_omissions.append({'scope':scope,'path':rel,'sha256':sha(priv/rel)})
        copy_results[scope]={'copied_durable_files':len(declared),'omissions':len(omitted)}
    assert len(all_omissions)==1
    result['literal_public_review_projection']=copy_results;result['private_omission']=all_omissions

    # Read the immutable base, never fetch or inspect a moving worktree as source.
    tree=git(REPO,'ls-tree','-r','-z',BASE)
    base_files={}
    for entry in tree.split(b'\0'):
        if entry:
            meta,path=entry.split(b'\t',1);base_files[path.decode()]=meta.decode().split()[2]
    indices=load(S/'index-candidates/INDEX_BINDINGS.json');idx={}
    remove={
     'README.md':['| APPT 全正阶熵统一首项与阶数转变 |','| 极值图论与离散几何 |'],
     'README.en.md':['| APPT entropy at every positive order |','| Extremal graphs and discrete geometry |'],
     'RESEARCH.md':['| APPT 全正阶与任意长宽比熵统一式 |']}
    added={
     'README.md':['| APPT 全维数、全扩展阶数的相对熵统一式 |','| 同一 APPT 方向：两个全长宽比增长阶谱窗口 |','| 同一 APPT 方向：零阶边界的三项非负谱损失 |','| 极值图论与离散几何 |'],
     'README.en.md':['| APPT relative entropy across both dimensions and every extended order |','| Same APPT direction: two arbitrary-aspect growing-order spectral windows |','| Same APPT direction: three nonnegative zero-boundary spectral losses |','| Extremal graphs and discrete geometry |'],
     'RESEARCH.md':['| APPT 全维数与全扩展阶数熵统一式 |','| 同一 APPT 主线：两个全aspect增长阶实际谱窗口 |','| 同一 APPT 主线：任意零阶路径的三非负谱损失 |']}
    basecopies=R/'base-index-copies';basecopies.mkdir(exist_ok=True)
    for rel,x in indices.items():
        original=git(REPO,'show',BASE+':'+rel)
        candidate=(S/'index-candidates'/rel).read_bytes()
        assert digest(original)==x['before_sha256'] and digest(candidate)==x['after_sha256'],rel
        bpath=basecopies/rel;bpath.parent.mkdir(parents=True,exist_ok=True);bpath.write_bytes(original)
        before=original.decode();after=candidate.decode()
        assert not (Counter(links(before))-Counter(links(after))),rel
        assert not re.search(r'^#{1,6}\s+已宣称解决的问题\s*$',after,re.M)
        diff=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='base/'+rel,tofile='candidate/'+rel))
        (folder/(rel.replace('/','_')+'.actual.diff')).write_text(diff)
        if rel in remove:
            b=before.splitlines(True);a=after.splitlines(True)
            removed=[line for line in b if any(line.startswith(k) for k in remove[rel])]
            inserted=[line for line in a if any(line.startswith(k) for k in added[rel])]
            assert len(removed)==len(remove[rel]) and len(inserted)==len(added[rel]),rel
            assert [line for line in b if line not in removed]==[line for line in a if line not in inserted],rel
            assert len(a)-len(b)==2
        else:
            ops=difflib.SequenceMatcher(a=before.splitlines(True),b=after.splitlines(True)).get_opcodes()
            assert all(op[0] in ['equal','insert'] for op in ops),rel
            assert re.findall(r'^## .+$',before,re.M)==re.findall(r'^## .+$',after,re.M)
            assert len(re.findall(r'^## .+$',after,re.M))==7
            assert '7203.967775' in after and '仍未解决' in after and '未审作者' in after
        idx[rel]={'before_sha256':digest(original),'after_sha256':digest(candidate),
                  'all_prior_link_occurrences_preserved':True,'exact_narrow_byte_diff':True}
    old_binding_rel='research/research-attempts-20261015/FINAL_STATUS_BINDING.json'
    old=git(REPO,'show',BASE+':'+old_binding_rel)
    assert digest(old)=='af9506a92cec7827b94ff832d79c7a4b08c33eb5d3a3e1bd9de4ff5a10d441d3'
    assert old_binding_rel not in mf['stage_file_lookup']
    (basecopies/'historical-catalog-FINAL_STATUS_BINDING.json').write_bytes(old)
    result['four_indices']=idx;result['old_catalog_binding_unchanged_and_not_destination']=digest(old)

    # UC0 provenance/status/clock only; no subsidiary mathematical review.
    uc=load(S/'index-candidates/UC0_SOURCE_BINDING.json')
    QREPO=Path('/home/mxym/math-breadth-quantum-20261015')
    uc_public=S/'public-sources/research-attempts-uc0-completed-20261015'
    for rel,x in uc['files'].items():
        raw=git(QREPO,'show',uc['source_commit']+':'+uc['source_prefix']+rel)
        assert raw==(uc_public/rel).read_bytes() and digest(raw)==x['sha256'] and len(raw)==x['bytes'],rel
        blob=git(QREPO,'rev-parse',uc['source_commit']+':'+uc['source_prefix']+rel).decode().strip()
        assert blob==x['git_blob'],rel
    clock=load(uc_public/'CLOCK.json');pres=load(uc_public/'PRESERVATION.json')
    iso=lambda s:datetime.datetime.fromisoformat(s)
    intervals=clock['active_intervals'];total_us=0
    for x in intervals:
        dt=iso(x['end_utc'])-iso(x['start_utc']);assert dt.total_seconds()>=0
        total_us+=(dt.days*86400+dt.seconds)*1000000+dt.microseconds
    assert Decimal(total_us)/1000000==Decimal('7203.967775')
    assert abs(Decimal(str(clock['effective_seconds_closed']))-Decimal(total_us)/1000000)<Decimal('1e-9')
    assert clock['complete'] and clock['full_problem_solved'] is False and clock['new_major_count']==0
    assert not pres['full_target_solved'] and not pres['independent_review'] and pres['new_major_count']==0
    for left,right in zip(intervals,intervals[1:]):
        assert iso(left['end_utc'])<=iso(right['start_utc'])
    expected_gaps={(x['end_utc'],y['start_utc']) for x,y in zip(intervals,intervals[1:])}
    actual_gaps={(x['start_utc'],x['end_utc']) for x in clock['excluded_intervals']}
    assert expected_gaps==actual_gaps
    assert 'UNRESOLVED' in (uc_public/'FINAL_MATHEMATICAL_STATUS.md').read_text()
    result['UC0']={'scope':'Immutable source/status/clock only; subsidiary mathematics remains author-only, not reviewed',
                   'source_commit':uc['source_commit'],'literal_files_native_git_verified':4,
                   'effective_seconds_exact':'7203.967775','full_problem_solved':False,'new_major_count':0,
                   'original_archive_only_recorded_not_replayed':True}

    # New files overlay immutable base; directory links and local anchors included.
    lookup={k:S/v for k,v in mf['stage_file_lookup'].items()}
    dirs=set()
    for rel in set(base_files)|set(lookup):
        parent=posixpath.dirname(rel)
        while parent:dirs.add(parent);parent=posixpath.dirname(parent)
    cache={}
    def readrepo(rel):
        if rel in lookup:return lookup[rel].read_bytes()
        if rel not in cache:cache[rel]=git(REPO,'show',BASE+':'+rel)
        return cache[rel]
    allowed_pending={x['target'] for x in mf['pending_self_binding_links']}
    nav=[];pending=[];external=0;fragment_count=0
    for rel in mf['canonical_documents']:
        text=readrepo(rel).decode()
        for raw in links(text):
            link=raw.strip('<>')
            if re.match(r'^[a-zA-Z][a-zA-Z0-9+.-]*:',link):external+=1;continue
            path,sep,frag=link.partition('#');path=urllib.parse.unquote(path);frag=urllib.parse.unquote(frag)
            dest=posixpath.normpath(posixpath.join(posixpath.dirname(rel),path)) if path else rel
            assert not dest.startswith(('/','../')),(rel,link,dest)
            if dest in allowed_pending:
                pending.append({'source':rel,'target':dest});continue
            assert dest in lookup or dest in base_files or dest in dirs,(rel,link,dest)
            if sep and frag:
                doc=dest+'/README.md' if dest in dirs else dest
                assert frag in anchors(readrepo(doc).decode()),(rel,link,'MISSING_ANCHOR',frag)
                fragment_count+=1
            nav.append({'source':rel,'target':dest,'fragment':frag if sep else None,'raw':raw})
    parent_links=load(S/'CANONICAL_LINKS.json')
    ours=Counter((x['source'],x['target']) for x in nav)
    theirs=Counter((x['source'],x['target']) for x in parent_links)
    assert not (theirs-ours),theirs-ours
    dump(folder/'INDEPENDENT_CANONICAL_LINKS.json',nav)
    result['navigation']={'canonical_documents':len(mf['canonical_documents']),'local_link_occurrences':len(nav),
                           'current_anchor_occurrences_verified':fragment_count,'external_link_occurrences_left_literal':external,
                           'parent488_paths_independently_covered':len(parent_links),
                           'pending_authorized_binding_links':pending,'remote_url_availability_checked':False}
    result['no_author_math_control_or_preflight_executed']=True
    result['no_Lean_Git_mutation_network_or_root_write']=True

def main():
    utc=datetime.datetime.now(datetime.timezone.utc);folder=R/'runs'/utc.strftime('%Y%m%dT%H%M%S.%fZ')
    folder.mkdir(parents=True);source=Path(__file__).read_bytes();(folder/'independent_metadata_checks.py').write_bytes(source)
    result={'utc':utc.isoformat(),'status':'RUNNING','scope':'Independent source/status/README/index/navigation only; prior mathematics not rerun',
            'source_sha256':hashlib.sha256(source).hexdigest(),'input_manifest_sha256':sha(S/'FINAL_CANDIDATE_INPUTS.json')}
    try:perform(folder,result);result['status']='PASS'
    except Exception:
        result.update(status='FAIL',actual_failure=traceback.format_exc())
        dump(folder/'RESULT.json',result);raise
    result['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump(folder/'RESULT.json',result);dump(R/'LATEST_RUN.json',{'run':str(folder),'source_sha256':result['source_sha256']})
    print(json.dumps({k:v for k,v in result.items() if k not in ['mathematical_scopes_source_bytes_only','four_indices','private_omission']},indent=2))

if __name__=='__main__':main()
