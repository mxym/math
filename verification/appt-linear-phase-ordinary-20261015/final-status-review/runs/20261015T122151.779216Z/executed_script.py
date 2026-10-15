"""Private source/status/index checker, not a mathematical or Lean audit.

No author diagnostic, old kernel tool, Git mutation, network request or
publication operation is executed. All outputs are retained under this folder.
"""
from pathlib import Path,PurePosixPath
from datetime import datetime,timezone
from collections import Counter
from urllib.parse import unquote,urlsplit
import hashlib,json,re,shutil,subprocess,traceback,unicodedata

BASE=Path(__file__).resolve().parent
STAGE=Path('/mnt/d/math/tmp/research-resume-20261015/scalar-phase-publication')
OWN=Path('/mnt/d/math/tmp/research-resume-20261015/independent-scalar-phase-review')
REPO=Path('/home/mxym/math-appt-multiscale-20261013')
COMMIT='c4e0d9e713ba349d376469231789bb7b36915b7d'
STAMP=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN=BASE/'runs'/STAMP;RUN.mkdir(parents=True)
shutil.copyfile(__file__,RUN/'executed_script.py')
R={'utc':STAMP,'kind':'independent metadata/source/index byte checks only','groups':{},
   'mathematical_controls_rerun':False,'author_code_imported_or_executed':False,
   'Lean_or_kernel_executed':False,'git_mutation_or_fetch':False,
   'future_transport_or_publication_guarantee':False}
def sha(data):return hashlib.sha256(data).hexdigest()
def git_blob(commit,path,repo=REPO):
    return subprocess.check_output(['git','-C',str(repo),'show',commit+':'+path])
def candidate(key):
    if '/' not in key:return STAGE/'index-candidates'/key
    for name,prefix in M['new_projects'].items():
        if key.startswith(prefix+'/'):
            return STAGE/'public-sources'/name/Path(key).relative_to(prefix)
    raise AssertionError('unrecognized candidate '+key)
def section(text,heading):
    start=text.index(heading);end=text.find('\n## ',start+len(heading))
    return text[start:] if end<0 else text[start:end]
def urls(text):
    return re.findall(r'\[[^\]\n]*\]\(([^\n)]*)\)',text)

try:
    M=json.loads((BASE/'input-records/FINAL_CANDIDATE_INPUTS.json').read_text())
    assert M['source_base']==COMMIT
    assert (STAGE/'FINAL_CANDIDATE_INPUTS.json').read_bytes()==(BASE/'input-records/FINAL_CANDIDATE_INPUTS.json').read_bytes()
    assert len(M['files'])==232
    for key,h in M['files'].items():
        assert sha((BASE/'snapshot'/key).read_bytes())==h,key
        assert candidate(key).read_bytes()==(BASE/'snapshot'/key).read_bytes(),key
    actual=set()
    for name,prefix in M['new_projects'].items():
        for p in (STAGE/'public-sources'/name).rglob('*'):
            if p.is_file() and p.name!='FINAL_STATUS_BINDING.json':
                actual.add(prefix+'/'+str(p.relative_to(STAGE/'public-sources'/name)))
    actual.update(['README.md','README.en.md','RESEARCH.md'])
    assert actual==set(M['files']),{'unexpected':sorted(actual-set(M['files'])),'missing':sorted(set(M['files'])-actual)}
    assert not any(Path(key).suffix.lower() in ['.pdf','.png','.jpg'] for key in actual)
    R['groups']['manifest_inventory']={'files':len(actual),'all_current_candidate_bytes_matched':True,
      'all_files_present_and_no_unlisted_payload':True,'external_raw_pdf_in_batch':False}

    geom=BASE/'snapshot/research/appt-linear-phase-geometry-20261015'
    maths=[('pole-onset/PAPER.md','snapshot-v2/PAPER.md','83c2240adfbca39009ff446504cc477f47684a0e5de1db52439862053bbcad79'),
           ('ge-one/PURE_ENVELOPE_GE_ONE.md','ge-one-review/PURE_ENVELOPE_GE_ONE.md','ad1a5aabca9d3fcf2e960cbf43bcf7cfbdfd232cc58b86bbaf355229656016a9'),
           ('bulk-onset/PAPER.md','bulk-onset-review/PAPER_V1.md','3e1f67ee40b28af0b9de3a643488524fdb38f508d663f63e2ec82f7bc4322804')]
    for dest,old,h in maths:
        assert (geom/dest).read_bytes()==(OWN/old).read_bytes() and sha((geom/dest).read_bytes())==h
    matched=[]
    for prefix,prior in [('pole-onset',OWN/'snapshot-v2'),('bulk-onset',OWN/'bulk-onset-review/snapshot')]:
        for p in prior.rglob('*'):
            if p.is_file():
                dest=geom/prefix/p.relative_to(prior)
                assert dest.read_bytes()==p.read_bytes(),str(dest)
                matched.append(str(dest.relative_to(BASE/'snapshot')))
    reports=[('pole-onset','REVIEW_V2'),('ge-one','ge-one-review/REVIEW'),('bulk-onset','bulk-onset-review/REVIEW')]
    for prefix,old in reports:
        for ext in ['.md','.json']:
            assert (geom/prefix/('REVIEW'+ext)).read_bytes()==(OWN/(old+ext)).read_bytes()
    assert (geom/'REVIEW.md').read_bytes()==(OWN/'COMBINED_REVIEW.md').read_bytes()
    assert (geom/'REVIEW.json').read_bytes()==(OWN/'COMBINED_REVIEW.json').read_bytes()
    evidence=BASE/'snapshot/verification/appt-linear-phase-ordinary-20261015/independent-source'
    owned_files={str(p.relative_to(OWN)) for p in OWN.rglob('*') if p.is_file()}
    copied_files={str(p.relative_to(evidence)) for p in evidence.rglob('*') if p.is_file()}
    assert copied_files==owned_files,{'extra':sorted(copied_files-owned_files),'missing':sorted(owned_files-copied_files)}
    for path in copied_files:assert (evidence/path).read_bytes()==(OWN/path).read_bytes(),path
    R['groups']['frozen_math_and_evidence']={'exact_math_sources':[{ 'path':p,'sha256':h} for p,_,h in maths],
        'author_and_credited_files_byte_compared':len(matched),'independent_evidence_files_byte_compared':len(copied_files),
        'three_separate_review_pairs_literal':True,'combined_index_literal':True,
        'no_status_patch_or_mathematical_source_edit':True}

    index=json.loads((BASE/'input-records/index-candidates/INDEX_BINDINGS.json').read_text())
    index_records={}
    for name,v in index.items():
        before=(BASE/'base'/name).read_bytes();after=(BASE/'snapshot'/name).read_bytes()
        assert before==git_blob(COMMIT,name) and sha(before)==v['before_sha256']
        assert sha(after)==v['after_sha256']
        hist=BASE/'snapshot/verification/appt-linear-phase-ordinary-20261015/readme-organization-history/before'/name
        if hist.exists():assert hist.read_bytes()==before
        index_records[name]=dict(v)
    cnold=(BASE/'base/README.md').read_text();cnnew=(BASE/'snapshot/README.md').read_text()
    enold=(BASE/'base/README.en.md').read_text();ennew=(BASE/'snapshot/README.en.md').read_text()
    claimmap=json.loads((BASE/'snapshot/verification/appt-linear-phase-ordinary-20261015/readme-organization-history/CLAIM_MERGE_MAP.json').read_text())
    oldclaims=section(cnold,'## 已宣称解决的问题')
    rows=[line for line in oldclaims.splitlines() if line.startswith('|')][2:]
    assert len(rows)==16 and rows==[x['original_claim_row'] for x in claimmap['all_original_claim_rows']]
    assert '## 已宣称解决的问题' not in cnnew and '## Claimed results' not in ennew
    for x in claimmap['all_original_claim_rows']:
        assert x['new_row'] in section(cnnew,'## 预印本')
        assert x['new_row'] in cnnew and x['proof_status_not_expanded'] is True
        for target in urls(x['original_claim_row']):assert target in urls(cnnew),target
    oldwritten={}
    for name,old,new,heading in [('README.md',cnold,cnnew,'## 已书面证明的问题'),
       ('README.en.md',enold,ennew,'## Results with complete written proofs')]:
        oldsec=section(old,heading);newsec=section(new,heading)
        oldrows=[line for line in oldsec.splitlines() if line.startswith('|')]
        assert all(line in newsec.splitlines() for line in oldrows)
        assert newsec.count('appt-linear-phase-geometry-20261015/README.md')==1
        for target in set(urls(old)):
            if target in ['#已宣称解决的问题','#claimed-results']:continue
            assert target in urls(new),(name,target)
        oldwritten[name]=len(oldrows)-2
        # All text from the proof/reproduction heading onward is literal: this
        # covers the old audit limitations, license/copyright and archival text.
        footer='## 证明与复现' if name=='README.md' else '## Proof and reproduction'
        assert old[old.index(footer):]==new[new.index(footer):]
    rold=(BASE/'base/RESEARCH.md').read_text();rnew=(BASE/'snapshot/RESEARCH.md').read_text()
    added=[x for x in rnew.splitlines(keepends=True) if 'appt-linear-phase-geometry-20261015/README.md' in x]
    assert len(added)==1 and rnew.replace(added[0],'')==rold
    R['groups']['index_reorganization']={'index_hashes':index_records,'original_claim_rows':16,
       'all_16_exact_source_rows_mapped':True,'old_written_rows_literal_preserved':oldwritten,
       'all_prior_readme_link_targets_preserved_except_removed_section_anchors':True,
       'proof_license_archive_footers_literal':True,'research_only_one_added_row':True,
       'historical_merge_map_after_hashes_are_not_current_index_binding':True}

    catalog=BASE/'snapshot/research/research-attempts-20261015'
    stages=json.loads((catalog/'STAGE_SOURCES.json').read_text());sr=[]
    for item in stages['summaries']:
        blob=git_blob(item['source_commit'],item['source_repository_path'])
        actual=(catalog/item['public_copy']).read_bytes()
        assert actual==blob and sha(blob)==item['sha256'] and len(blob)==item['bytes']
        sr.append({'source_commit':item['source_commit'],'repository_path':item['source_repository_path'],
                   'sha256':sha(blob),'bytes':len(blob),'public_copy':item['public_copy']})
    assert json.loads((catalog/'PROJECT_KIND.json').read_text())['requires']=='source/status/index review only; no mathematical promotion'
    cap=json.loads((catalog/'stage-summaries/quantum-depolarizing.json').read_text())
    assert cap['complete_target_solved'] is False and cap['ordinary_author_only'] is True and cap['new_major_results']==0
    assert 'full SIC existence target was not\nsolved by this stage' in (catalog/'stage-summaries/quantum-sic.md').read_text()
    assert 'This full target remains unproved and unrefuted here' in (catalog/'stage-summaries/tcs-fei.md').read_text()
    R['groups']['catalog_stage_provenance']={'exact_owned_commit_blobs_read_back':sr,
       'metadata_only_not_mathematical_certification':True,'no_external_full_proof_endorsement':True}

    # Canonical navigation only. Frozen proof/history/credited snapshots have
    # original source-relative references, and are not reinterpreted as pages
    # authored for the new package layout.
    gitpaths=subprocess.check_output(['git','-C',str(REPO),'ls-tree','-r','--name-only',COMMIT],text=True).splitlines()
    available=set(gitpaths)|set(M['files'])
    future={prefix+'/FINAL_STATUS_BINDING.json' for prefix in M['new_projects'].values()}
    canonical=['README.md','README.en.md','RESEARCH.md',
      'research/appt-linear-phase-geometry-20261015/README.md',
      'research/appt-linear-phase-geometry-20261015/STATUS.md',
      'verification/appt-linear-phase-ordinary-20261015/README.md',
      'research/research-attempts-20261015/README.md']
    linkrecords=[];futurelinks=[]
    for src in canonical:
        for raw in urls((BASE/'snapshot'/src).read_text()):
            target=unquote(raw.strip('<>'))
            if urlsplit(target).scheme:continue
            filename=target.split('#',1)[0].split('?',1)[0]
            if not filename:continue
            # POSIX normalization independent of host filesystem.
            pieces=[]
            for x in (PurePosixPath(src).parent/PurePosixPath(filename)).parts:
                if x=='.':continue
                if x=='..':
                    assert pieces,('link escapes repository',src,target)
                    pieces.pop()
                else:pieces.append(x)
            resolved='/'.join(pieces)
            if resolved in future:futurelinks.append({'source':src,'target':target,'resolved':resolved});continue
            assert resolved in available or any(x.startswith(resolved.rstrip('/')+'/') for x in available),(src,target,resolved)
            linkrecords.append({'source':src,'target':target,'resolved':resolved})
    (RUN/'CANONICAL_LINKS.json').write_text(json.dumps(linkrecords,indent=2,ensure_ascii=False)+'\n')
    R['groups']['navigation']={'canonical_sources':canonical,'existing_file_or_directory_targets_checked':len(linkrecords),
       'pending_binding_links_excluded_until_write':futurelinks,
       'external_urls_not_fetched_or_certified':True,'historical_snapshot_relative_links_not_reaudited':True}
    R['status']='PASS';R['decision']='PASS'
except BaseException:
    R['status']='FAIL';R['decision']='FAIL';R['traceback']=traceback.format_exc()
finally:
    R['executed_script_sha256']=sha((RUN/'executed_script.py').read_bytes())
    (RUN/'RESULT.json').write_text(json.dumps(R,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'run':str(RUN),'status':R['status'],'groups':R['groups']},indent=2,ensure_ascii=False))
if R['status']!='PASS':
    print(R['traceback']);raise SystemExit(1)
