"""Hash all prepared bytes and check narrow index changes/current navigation privately."""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import hashlib,json,posixpath,re,subprocess

stage=Path(__file__).resolve().parent;public=stage/'public-sources'
root=Path('/home/mxym/math-appt-multiscale-20261013')
current='5bbb10af2b165ce9bec56ba4cb929733496cf192'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a):return subprocess.check_output(['git','-C',str(root),*a])
assert git('rev-parse','HEAD').decode().strip()==current and not git('status','--porcelain').strip()
layout={
 'appt-all-dimension-entropy-profile-20261015':'research/appt-all-dimension-entropy-profile-20261015',
 'appt-growing-order-rigidity-20261015':'research/appt-growing-order-rigidity-20261015',
 'appt-zero-order-losses-20261015':'research/appt-zero-order-losses-20261015',
 'appt-entropy-spectrum-ordinary-20261015':'verification/appt-entropy-spectrum-ordinary-20261015',
 'research-attempts-uc0-completed-20261015':'research/research-attempts-20261015/uc0-completed'}
assert set(p.name for p in public.iterdir() if p.is_dir())==set(layout)
files={};lookup={}
for name,dest in layout.items():
    for p in sorted((public/name).rglob('*')):
        if p.is_file():
            rel=dest+'/'+p.relative_to(public/name).as_posix()
            assert '__pycache__' not in p.parts and p.suffix!='.pyc'
            files[rel]={'sha256':sha(p),'bytes':p.stat().st_size};lookup[rel]=p
indices=json.loads((stage/'index-candidates/INDEX_BINDINGS.json').read_text())
for rel,v in indices.items():
    p=stage/'index-candidates'/rel
    assert sha(root/rel)==v['before_sha256'] and sha(p)==v['after_sha256']
    before=(root/rel).read_text();after=p.read_text()
    urls=lambda t:Counter(re.findall(r'\]\(([^\n]+?)\)',t))
    assert not (urls(before)-urls(after)),('An old URL occurrence was removed',rel)
    assert not re.search(r'^#{1,6}\s+已宣称解决的问题\s*$',after,re.M)
    if rel in ('README.md','README.en.md','RESEARCH.md'):
        assert after.count('appt-all-dimension-entropy-profile-20261015/README.md')==1
        assert after.count('appt-growing-order-rigidity-20261015/README.md')==1
        assert after.count('appt-zero-order-losses-20261015/README.md')==1
        assert len(after.splitlines())==len(before.splitlines())+2
    else:
        assert after.count('## ')==before.count('## ')
        assert before.count('## ')==7 # six categories plus the records section
        assert '7203.967775' in after and '仍未解决' in after
    files[rel]={'sha256':sha(p),'bytes':p.stat().st_size};lookup[rel]=p
extra={'research/research-attempts-20261015/UC0_SOURCE_BINDING.json':stage/'index-candidates/UC0_SOURCE_BINDING.json'}
for rel,p in extra.items():files[rel]={'sha256':sha(p),'bytes':p.stat().st_size};lookup[rel]=p
prep=json.loads((stage/'SOURCE_PREPARATION.json').read_text())
assert set(prep['scopes'])=={'X','S5','S6','Zloss'}
for name,v in prep['scopes'].items():
    source=public/v['destination']
    for rel,r in v['source_files'].items():
        assert sha(source/rel)==r['sha256'] and (source/rel).stat().st_size==r['bytes']
    assert sha(source/'PAPER.md')==v['paper_sha256']
copies=json.loads((public/'appt-entropy-spectrum-ordinary-20261015/PUBLIC_EVIDENCE_COPY_BINDINGS.json').read_text())
for scope,v in copies.items():
    for rel,r in v['copied_durable_files'].items():
        p=public/'appt-entropy-spectrum-ordinary-20261015'/scope/rel
        assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
    for rel,r in v['explicit_omissions'].items():
        assert scope=='X' and rel.startswith('private-primary-evidence/')
        assert not (public/'appt-entropy-spectrum-ordinary-20261015'/scope/rel).exists()
canonical=list(indices)+[
 layout['appt-all-dimension-entropy-profile-20261015']+'/README.md',
 layout['appt-all-dimension-entropy-profile-20261015']+'/STATUS.md',
 layout['appt-growing-order-rigidity-20261015']+'/README.md',
 layout['appt-growing-order-rigidity-20261015']+'/STATUS.md',
 layout['appt-growing-order-rigidity-20261015']+'/REVIEW.md',
 layout['appt-zero-order-losses-20261015']+'/README.md',
 layout['appt-zero-order-losses-20261015']+'/STATUS.md',
 layout['appt-entropy-spectrum-ordinary-20261015']+'/README.md']
checked=[];pending=[]
for rel in canonical:
    for link in re.findall(r'\]\(([^\n]+?)\)',lookup[rel].read_text()):
        if '://' in link or link.startswith(('#','mailto:')):continue
        target=link.split('#',1)[0].strip('<>')
        if not target:continue
        dest=posixpath.normpath(posixpath.join(posixpath.dirname(rel),target))
        assert not dest.startswith(('/','../')),(rel,link)
        if dest.endswith('/FINAL_STATUS_BINDING.json'):
            pending.append({'source':rel,'target':dest})
        else:
            assert dest in lookup or any(k.startswith(dest.rstrip('/')+'/') for k in lookup) or (root/dest).exists(),(rel,link,dest)
            checked.append({'source':rel,'target':dest})
receipt={'utc':datetime.now(timezone.utc).isoformat(),'status':'PASS',
 'purpose':'source/status/navigation preparation; not mathematical or Lean audit',
 'source_base':current,'projects':layout,'modified_indices':indices,
 'extra_source_files':{rel:str(p.relative_to(stage)) for rel,p in extra.items()},
 'mathematical_scopes':{k:{q:v[q] for q in ('paper_sha256','review_md_sha256','review_json_sha256')} for k,v in prep['scopes'].items()},
 'canonical_documents':canonical,'canonical_links_checked':len(checked),'pending_self_binding_links':pending,
 'files':files,'stage_file_lookup':{rel:p.relative_to(stage).as_posix() for rel,p in lookup.items()},
 'new_Lean':False,'new_major_count':0}
(stage/'FINAL_CANDIDATE_INPUTS.json').write_text(json.dumps(receipt,indent=2)+'\n')
(stage/'CANONICAL_LINKS.json').write_text(json.dumps(checked,indent=2)+'\n')
print(json.dumps({'status':'PASS','bound_files':len(files),'canonical_links':len(checked),
                  'four_math_scopes_fixed':True,'UC0_is_unresolved_attempt_only':True}))
