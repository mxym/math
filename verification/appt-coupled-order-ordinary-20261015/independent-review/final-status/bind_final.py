#!/usr/bin/env python3
"""Final K metadata, figure-provenance and three-index-row byte binding.

No mathematical controls or plotting program are executed.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,difflib,subprocess

HERE=Path(__file__).resolve().parent
REVIEW=HERE.parent
PUBLICATION=REVIEW.parent/'coupled-publication'
CANDIDATE=PUBLICATION/'public-sources/appt-coupled-order-window-20261015'
INDEX=PUBLICATION/'index-candidates'
STAMP=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
SAVE=HERE/'snapshots'/STAMP
SAVE.mkdir(parents=True)
def sha(b):return hashlib.sha256(b).hexdigest()
def record(b):return {'sha256':sha(b),'bytes':len(b)}
def textrecord(b):return {**record(b),'lines':len(b.decode().splitlines())}
def reverse_patch(final,patch):
    lines=patch.splitlines(keepends=True);src=final.splitlines(keepends=True)
    assert lines[0].startswith(b'--- ') and lines[1].startswith(b'+++ ')
    rg=re.compile(rb'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@.*\n?')
    i=2;pos=0;out=[];hunks=0
    while i<len(lines):
        hit=rg.fullmatch(lines[i]);assert hit
        count_old=int(hit[2] or b'1');count_new=int(hit[4] or b'1');start=int(hit[3])-1
        assert start>=pos
        out.extend(src[pos:start]);pos=start;before=len(out);used=0;i+=1
        while i<len(lines) and not lines[i].startswith(b'@@ '):
            tag=lines[i][:1];payload=lines[i][1:]
            assert tag in (b' ',b'+',b'-')
            if tag in (b' ',b'+'):
                assert src[pos]==payload
                pos+=1;used+=1
            if tag in (b' ',b'-'):out.append(payload)
            i+=1
        assert used==count_new and len(out)-before==count_old
        hunks+=1
    out.extend(src[pos:])
    return b''.join(out),hunks

paper=(CANDIDATE/'PAPER.md').read_bytes();patch=(CANDIDATE/'FINAL_STATUS.diff').read_bytes()
prior=(REVIEW/'snapshot/K/PAPER.md').read_bytes()
assert sha(paper)=='1de40761542d4f482841a285d84e874633b87a14e1f89baf26edd8302303024a'
assert sha(patch)=='058d7dfe73cd03ef96e6aa73c67bfbd37aa7ebb7d88a0b7a96d608bddcec742f'
assert sha(prior)=='efba5e8ef99af23d69081c958dbd0f0fb1a95ef967807b7038179d9a6da0b0d5'
restored,hunks=reverse_patch(paper,patch)
assert restored==prior and hunks==2
forward=''.join(difflib.unified_diff(prior.decode().splitlines(keepends=True),paper.decode().splitlines(keepends=True),
                 fromfile='K/reviewed/PAPER.md',tofile='K/final/PAPER.md')).encode()
assert forward==patch
for name in ('THEOREM_MAP.md','checks.py','REVIEW_HISTORY.md'):
    assert (CANDIDATE/name).read_bytes()==(REVIEW/'snapshot/K'/name).read_bytes()
for name in ('REVIEW.md','REVIEW.json'):
    assert (CANDIDATE/name).read_bytes()==(REVIEW/name).read_bytes()
assert sha((CANDIDATE/'README.md').read_bytes())=='86b1fc980ab7007e7395844bd18ed117be22895e606a348d25fd0cc1da4962af'

names=['PAPER.md','README.md','FINAL_STATUS.diff','LITERATURE_SCREEN.md','figure.py',
       'figures/PROVENANCE.json','figures/coupled-transition.png','figures/coupled-transition.svg',
       'THEOREM_MAP.md','checks.py','REVIEW_HISTORY.md','REVIEW.md','REVIEW.json','requirements.txt']
files={}
for name in names:
    raw=(CANDIDATE/name).read_bytes();p=SAVE/'project'/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
    files[name]=record(raw)
(SAVE/'RESTORED_REVIEWED_PAPER.md').write_bytes(restored)
provenance=json.loads((CANDIDATE/'figures/PROVENANCE.json').read_text())
control_path=CANDIDATE/provenance['source_control'];control=control_path.read_bytes()
assert sha(control)==provenance['source_control_sha256']
control_data=json.loads(control)
assert control_data['status']=='PASS'
assert control_data['source_sha256']['PAPER.md']==sha(prior)
assert control_data['groups']['transition_constants']==provenance['constants']
for name,hashval in provenance['files'].items():assert sha((CANDIDATE/'figures'/name).read_bytes())==hashval
(SAVE/'FIGURE_SOURCE_CONTROL_RESULT.json').write_bytes(control)

# Read only the three new rows semantically. Verify unchanged old index text
# mechanically against the immutable base; do not claim a fresh read of it.
base_ref='f50d05a07'
repo='/home/mxym/math-appt-multiscale-20261013'
base_commit=subprocess.run(['git','rev-parse',base_ref],cwd=repo,capture_output=True,check=True).stdout.decode().strip()
ib=json.loads((INDEX/'INDEX_BINDINGS.json').read_text())
added=(INDEX/'ADDED_ROWS.md').read_text().splitlines();index_rows={}
for name,meta in ib.items():
    old=subprocess.run(['git','show',base_commit+':'+name],cwd=repo,capture_output=True,check=True).stdout
    new=(INDEX/name).read_bytes()
    assert sha(old)==meta['before_sha256'] and sha(new)==meta['after_sha256']
    before=old.splitlines(keepends=True);after=new.splitlines(keepends=True)
    changes=[o for o in difflib.SequenceMatcher(None,before,after,autojunk=False).get_opcodes() if o[0]!='equal']
    assert len(changes)==1
    op,i,j,k,l=changes[0]
    assert op=='insert' and i==j and l-k==1
    row=after[k].decode().rstrip('\r\n')
    assert row.startswith('| ') and 'research/appt-coupled-order-window-20261015/README.md' in row
    assert b''.join(after[:k]+after[l:])==old
    where=added.index(name)
    declared=next(x for x in added[where+1:] if x.strip())
    assert row==declared
    assert 'mD(Eα−Gα)=max{0,L₊,L₋}+O_(U,A)(1/m)' in row
    assert 'sufficiently large m' in row or '充分大 m' in row
    p=SAVE/'indices'/name;p.parent.mkdir(exist_ok=True);p.write_bytes(new)
    (SAVE/'indices'/('BEFORE-'+name)).write_bytes(old)
    delta=''.join(difflib.unified_diff(old.decode().splitlines(keepends=True),new.decode().splitlines(keepends=True),
                                    fromfile='before/'+name,tofile='after/'+name))
    (SAVE/'indices'/(name+'.diff')).write_text(delta)
    index_rows[name]={'status':'PASS','before_sha256':sha(old),'after_sha256':sha(new),
                      'added_row':row,'one_literal_added_row_only':True,'all_prior_bytes_preserved':True}
for name in ('ADDED_ROWS.md','INDEX_BINDINGS.json'):(SAVE/'indices'/name).write_bytes((INDEX/name).read_bytes())
history=(PUBLICATION/'INDEX_REVISION_HISTORY.md').read_bytes();(SAVE/'INDEX_REVISION_HISTORY.md').write_bytes(history)
old_readme=CANDIDATE/'author-versions/publication-status-v1/README.md'
assert sha(old_readme.read_bytes())=='81ab0656f371bf619c03d18cad02ef8a2c330becabb797a745d583f120e1d5c3'
(SAVE/'INITIAL_PROJECT_README.md').write_bytes(old_readme.read_bytes())
for name in ('ADDED_ROWS.md','INDEX_BINDINGS.json'):
    p=SAVE/'initial-index-candidates'/name;p.parent.mkdir(exist_ok=True)
    p.write_bytes((PUBLICATION/'index-candidates-v1'/name).read_bytes())

index_record={'status':'PASS','kind':'three-new-index-row scope and byte binding','base_commit':base_commit,
              'rows':index_rows,'semantic_read_scope':'Only the three added rows, not a fresh read of old index contents.',
              'history':textrecord(history),'mathematical_target_changed':False,
              'requested_metadata_fix':'Retain mD scaling, O_(U,A)(1/m), and sufficiently-large-m quantifier.',
              'fix_resolved':True,'controls_rerun':False}
(HERE/'INDEX_BINDING.json').write_text(json.dumps(index_record,indent=2)+'\n')

primary=[{'url':'https://arxiv.org/abs/2608.03390v2','read_scope':'official abstract and metadata only'},
         {'url':'https://arxiv.org/abs/2609.18568v1','read_scope':'official abstract and metadata only'},
         {'url':'https://arxiv.org/abs/2610.12000','read_scope':'official abstract and metadata only'}]
(HERE/'PRIMARY_SCOPE_READ.json').write_text(json.dumps({'date_local':'2026-10-15 Asia/Shanghai','pages':primary,
    'full_papers_read':False,'proofs_validated':False,'exhaustive_search':False,'priority_certificate':False},indent=2)+'\n')

binding={'status':'PASS','target':'K0-K3 final status, README, bounded-literature wording, figure provenance and three index rows',
         'review_kind':'independent internal AI-agent final metadata/source binding',
         'bound_utc':datetime.now(timezone.utc).isoformat(),'review_date_local':'2026-10-15 Asia/Shanghai',
         'reviewed_paper_sha256':sha(prior),'final_paper_sha256':sha(paper),'status_diff_sha256':sha(patch),
         'reviewed_paper_lines':336,'final_paper_lines':len(paper.decode().splitlines()),
         'two_status_hunks_manually_read':True,'reverse_diff_recovers_reviewed_bytes':True,
         'entire_forward_diff_byte_identical':True,'mathematics_and_quantifiers_unchanged':True,
         'README_fully_read':True,'LITERATURE_SCREEN_fully_read':True,'figure_py_fully_read':True,
         'figure_provenance_fully_read':True,'figure_constant_record_equal_to_bound_author_run':True,
         'figure_artifacts_match_provenance_hashes':True,'figure_scope':'limiting-law numerical illustration only',
         'PNG_visual_layout_independently_reviewed_here':False,
         'PNG_layout_note':'Author/root reported a visual layout check. This reviewer checked formula/provenance/caption scope, not image layout.',
         'bounded_primary_scope':primary,'full_paper_literature_audit':False,'priority_certificate':False,
         'all_three_new_index_rows_scope_checked':True,'index_binding':record((HERE/'INDEX_BINDING.json').read_bytes()),
         'index_before_after':{n:{k:v for k,v in d.items() if k.endswith('sha256')} for n,d in index_rows.items()},
         'files':files,'figure_source_control':record(control),
         'metadata_findings_resolved':['Project README now explicitly says sufficiently large m.',
                                      'Three index rows now retain mD scaling and O_(U,A)(1/m) remainder, with sufficiently large m.'],
         'mathematical_controls_rerun':False,'figure_executed_here':False,'Lean':False,'old_audit_expanded':False,
         'external_human_peer_review':False,'new_mathematics_covered':False,
         'evidence_link_layout_note':'Shared verification README is to be created during integration; this binding does not certify future packaging layout.'}

# Check that no candidate input moved while the binding was assembled.
for name,rec in files.items():assert sha((CANDIDATE/name).read_bytes())==rec['sha256']
dest=CANDIDATE/'FINAL_STATUS_BINDING.json';assert not dest.exists()
raw=(json.dumps(binding,indent=2)+'\n').encode()
dest.write_bytes(raw);(HERE/'FINAL_STATUS_BINDING.json').write_bytes(raw)
(REVIEW/'FINAL_STATUS_BINDING.json').write_bytes(raw)

report='''# K final status, public scope, figure and index binding

15 October 2026, Asia/Shanghai. **PASS** for the literal final K candidate
and the three new root-index rows recorded here. This is an independent
internal AI-agent metadata/source read after the complete separate K0-K3
mathematical review, not a new proof, Lean check or external human review.
No mathematical controls or figure program were executed in this step.

The entire two-hunk FINAL_STATUS.diff was read. Both hunks change only
ordinary-review completion wording and its evidence references. Independent
byte-line reverse application restores the exact 336-line reviewed source;
the ENTIRE independently generated forward difference equals the provided
patch. No unlisted formula, hypothesis, quantifier, equality case, or proof
change exists. The map, mathematical controls and REVIEW_HISTORY are
byte-identical to the mathematical freeze; REVIEW.md/json exactly match
the completed independent mathematical review.

- Reviewed PAPER SHA-256: `'''+sha(prior)+'''`
- Final PAPER SHA-256: `'''+sha(paper)+'''`
- FINAL_STATUS.diff SHA-256: `'''+sha(patch)+'''`
- Final project README SHA-256: `'''+files['README.md']['sha256']+'''`

The README was read in full, including the final clarification explicitly
saying sufficiently large m. It accurately gives alpha=alpha_0+u/m on each
fixed bounded u,a domain, the mD-scaled formula WITH O_(U,A)(1/m), every
actual optimizer and tie, fixed-gap selection only, all-larger-n minimal
FINAL onset, and the two-ceiling ambiguity. Its description of the actual
domain finding, adopted reviewer coefficient, and four source-bound author/
independent PASS runs is accurate. It does not imply arbitrary moving
order, all finite dimensions, a single exact ceiling or a new major count.

The bounded literature screen was read completely. I additionally opened
only the official abstract/metadata pages for
[Ahiable--Kothakonda--Winter v2](https://arxiv.org/abs/2608.03390v2),
[Tran v1](https://arxiv.org/abs/2609.18568v1), and
[Patra--Hiesmayr](https://arxiv.org/abs/2610.12000).
The recorded scope descriptions and metadata are consistent with these
abstracts. No full paper or PDF was newly read; no proof of another paper,
exhaustive novelty search, exact discovery-query replay or priority claim
is certified. Abstract silence about K is not promoted to silence of an
entire paper or the literature. PRIMARY_SCOPE_READ.json records this limit.

figure.py and PROVENANCE.json were read completely. The plot computes
max(0,L_+,L_-) and its corresponding affine onset frontier. Its dashed
head-equality contour can continue into the bulk; the README explicitly
explains this. Constants are read from the revised author control result;
the source result hash, constant dictionary, and both image hashes match
the provenance record. The displayed alpha_0,d_0 and (u_c,a_c) decimals
are illustrations, not exact definitions, a proven sign for u_c, or rigorous
interval certificates. The plot is a LIMITING explanation, not an exact
finite-dimensional phase diagram or evidence for the whole feasible set.
I did not execute plotting, rerun its mathematical controls or inspect PNG
layout; the author/root reported that visual check. This is a provenance,
formula and caption-scope check only.

All THREE added rows in README.md, README.en.md and RESEARCH.md were read.
Their initial summaries omitted the K1 remainder, and one Chinese summary
also left the mD scaling implicit. The author adopted the requested exact
scaling, O_(U,A)(1/m) and sufficiently-large-m wording in every row. Their
final scope is accurate. Both initial candidates and the metadata history
are preserved; these were metadata findings, not hidden mathematical
execution FAILs. Each final index candidate is compared with the immutable
base commit `'''+base_commit+'''`.
Each differs by exactly ONE inserted literal table row, that row matches
ADDED_ROWS.md, and removing it restores every original index byte. Only
the new rows were semantically reviewed; no fresh read of the old index
contents is claimed. INDEX_BINDING.json gives exact before/after hashes.

Source and restored-byte snapshots are retained under
`snapshots/'''+STAMP+'''/`. Candidate FINAL_STATUS_BINDING.json and its two
independent-directory copies are identical. They record all source,
figure, provenance, screen and index hashes. The root tree and all candidate
PAPER/map/checks/README/diff/index source files were not modified by the
reviewer. Future shared-evidence README/link layout must still be supplied
during integration and is not pre-certified here. Unknown future source
bytes or new mathematical extensions are outside this binding.
'''
doc=HERE/'FINAL_STATUS_REVIEW.md';doc.write_text(report)
result={'status':'PASS','scope':binding['target'],'bound_utc':datetime.now(timezone.utc).isoformat(),
        'binding_sha256':sha(raw),'report':textrecord(doc.read_bytes()),
        'source_binding':binding,'index_binding_sha256':sha((HERE/'INDEX_BINDING.json').read_bytes()),
        'primary_scope_record_sha256':sha((HERE/'PRIMARY_SCOPE_READ.json').read_bytes()),
        'metadata_revision_history':textrecord(history),'script':textrecord(Path(__file__).read_bytes()),
        'snapshot_directory':str(SAVE),'mathematical_controls_rerun':False,'new_mathematics_covered':False}
(HERE/'FINAL_STATUS_REVIEW.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','final_paper_sha256':sha(paper),'binding_sha256':sha(raw),
                  'report_sha256':sha(doc.read_bytes()),
                  'report_json_sha256':sha((HERE/'FINAL_STATUS_REVIEW.json').read_bytes()),
                  'index_binding_sha256':sha((HERE/'INDEX_BINDING.json').read_bytes())}))
