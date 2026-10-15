#!/usr/bin/env python3
"""Byte binding after manual status-diff and full README read.

No mathematical controls are rerun. Only three authorized new candidate
FINAL_STATUS_BINDING.json files and this reviewer's own evidence are written.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,difflib

ROOT=Path(__file__).resolve().parent
PUBLIC=ROOT.parent/'public-sources'
META=PUBLIC/'FINAL_SOURCE_CANDIDATES.json'
manifest=json.loads(META.read_text())
stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
SAVE=ROOT/'final-source-snapshots'/stamp
SAVE.mkdir(parents=True)

def sha(raw):return hashlib.sha256(raw).hexdigest()
def rec(raw):return {'sha256':sha(raw),'bytes':len(raw),'lines':len(raw.decode().splitlines())}
def reverse_patch(final,diff):
    """Apply the literal unified difference backwards to byte lines."""
    pp=diff.splitlines(keepends=True); ff=final.splitlines(keepends=True)
    assert pp[0].startswith(b'--- ') and pp[1].startswith(b'+++ ')
    i=2; pos=0; restored=[]; hunks=0
    header=re.compile(rb'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@.*\n?')
    while i<len(pp):
        hit=header.fullmatch(pp[i]);assert hit,('invalid hunk',i,pp[i])
        oldstart=int(hit[1]);oldcount=int(hit[2] or b'1')
        newstart=int(hit[3]);newcount=int(hit[4] or b'1')
        start=newstart-1
        assert start>=pos
        restored.extend(ff[pos:start]);pos=start
        before=len(restored); used=0; i+=1
        while i<len(pp) and not pp[i].startswith(b'@@ '):
            ln=pp[i]; tag=ln[:1]; payload=ln[1:]
            if tag in (b' ',b'+'):
                assert pos<len(ff) and ff[pos]==payload,('final-line mismatch',pos)
                pos+=1;used+=1
            if tag in (b' ',b'-'):restored.append(payload)
            assert tag in (b' ',b'-',b'+'),('unsupported patch marker',ln)
            i+=1
        assert used==newcount and len(restored)-before==oldcount
        hunks+=1
    restored.extend(ff[pos:])
    return b''.join(restored),hunks

entries={}; pending={}
for key in ('H','I','J'):
    cfg=manifest[key]; base=PUBLIC/cfg['project']; reviewed=ROOT/'snapshot'/key/'PAPER.md'
    final=(base/'PAPER.md').read_bytes(); prior=reviewed.read_bytes(); patch=(base/'FINAL_STATUS.diff').read_bytes()
    assert sha(final)==cfg['final_paper_sha256']
    assert sha(prior)==cfg['reviewed_paper_sha256']
    assert sha(patch)==cfg['status_diff_sha256']
    assert len(final.decode().splitlines())==cfg['final_lines']
    restored,hunks=reverse_patch(final,patch)
    assert restored==prior,'Reverse patch did not restore literal reviewed bytes'
    generated=''.join(difflib.unified_diff(prior.decode().splitlines(keepends=True),
                       final.decode().splitlines(keepends=True),
                       fromfile=key+'/reviewed/PAPER.md',tofile=key+'/final/PAPER.md')).encode()
    assert generated==patch,'The presented diff does not equal the entire literal source difference'
    assert (base/'REVIEW.md').read_bytes()==(ROOT/(key+'_REVIEW.md')).read_bytes()
    assert (base/'REVIEW.json').read_bytes()==(ROOT/(key+'_REVIEW.json')).read_bytes()
    for name in ('THEOREM_MAP.md',)+(('FOLLOWUP_TARGET.md',) if key=='H' else ()):
        assert (base/name).read_bytes()==(ROOT/'snapshot'/key/name).read_bytes()
    if key=='I':assert (base/'CONTROL_HISTORY.md').read_bytes()==(ROOT/'snapshot/I/CONTROL_HISTORY.md').read_bytes()
    names=['PAPER.md','README.md','FINAL_STATUS.diff','REVIEW.md','REVIEW.json','THEOREM_MAP.md','checks.py','requirements.txt']
    if key=='H':names.append('FOLLOWUP_TARGET.md')
    if key=='I':names.append('CONTROL_HISTORY.md')
    files={}
    dest=SAVE/key;dest.mkdir()
    for name in names:
        raw=(base/name).read_bytes();files[name]=rec(raw);(dest/name).write_bytes(raw)
    (dest/'RESTORED_REVIEWED_PAPER.md').write_bytes(restored)
    entry={
        'status':'PASS','project':cfg['project'],'target':key+'0-'+key+('5' if key=='H' else '3'),
        'review_kind':'independent AI-agent final metadata/README/source binding',
        'bound_utc':datetime.now(timezone.utc).isoformat(),'review_date_local':'2026-10-15 Asia/Shanghai',
        'reviewed_paper_sha256':sha(prior),'final_paper_sha256':sha(final),
        'status_diff_sha256':sha(patch),'readme_sha256':files['README.md']['sha256'],
        'ordinary_report_sha256':files['REVIEW.md']['sha256'],
        'ordinary_review_json_sha256':files['REVIEW.json']['sha256'],
        'full_readme_read':True,'entire_status_diff_manually_read':True,
        'reverse_diff_restores_reviewed_bytes':True,'whole_forward_diff_byte_identical':True,
        'diff_hunks':hunks,'mathematical_claims_and_quantifiers_unchanged':True,
        'only_paper_changes':'Review-completion status and references; no mathematical proof or target change.',
        'readme_scope_accuracy':'Checked against the complete previously reviewed targets and actual retained failure histories.',
        'control_runs_repeated_for_this_binding':False,'Lean':False,'old_audit_expanded':False,
        'external_human_peer_review':False,'files':files,
        'final_status_report':'FINAL_STATUS_REVIEW.md/json, retained with shared reviewer evidence',
        'outside_scope':['new mathematical source changes','varying-order/coupled-alpha extension',
                         'exhaustive literature or priority verification','all finite dimensions','new formal verification']}
    if key=='H':entry['readme_clarification']='O(m^-3) applies to the real arguments of the two ceilings; the integer ceiling values can differ by one.'
    if key=='I':entry['dependency_clarification']='I proves o(m) unconditionally and O(1) conditionally; the separate reviewed J establishes that condition for every fixed positive alpha.'
    if key=='J':entry['diagnostic_clarification']='The alpha_x and minimum-d decimals are illustrations, not exact constants or rigorous interval certificates. Two genuine reviewer-helper FAILs and subsequent PASSs are retained.'
    path=base/'FINAL_STATUS_BINDING.json'
    assert not path.exists(),'Do not overwrite an earlier binding'
    pending[path]=(entry,base)
    entries[key]=entry

# Detect concurrent mutation before writing any authorized candidate file.
for path,(entry,base) in pending.items():
    for name,info in entry['files'].items():assert sha((base/name).read_bytes())==info['sha256']
for path,(entry,base) in pending.items():
    path.write_text(json.dumps(entry,indent=2)+'\n')
    entry['binding_file_sha256']=sha(path.read_bytes())
    # The on-disk binding is self-hash-free; only the independent report records
    # its hash, avoiding a circular hash requirement.

text='''# Final status, README and literal source binding

15 October 2026, Asia/Shanghai. Independent internal AI-agent review by the
resumed reviewer. **PASS for all three final candidates bound below.**

This is the final metadata/source check following the complete, separate
H0-H5, I0-I3 and J0-J3 mathematical reviews. It does not rerun or enlarge
those reviews, repeat mathematical controls, invoke Lean, expand an old
audit, or certify an external human peer review. No new mathematical claim
has been added by the status edits.

All three new READMEs were read in full. H states the original actual
all-global-unitary APPT object, EACH fixed finite positive order including
von Neumann, the entire fixed linear critical band, every optimizing
matrix and all ties, true ranks/traces, half-order final/all-larger-n
onset and no new Lean. An initially ambiguous description of ceiling
spacing was corrected by the author before this binding: O(m^-3) is the
spacing of the REAL arguments, whereas the integer ceilings may differ
if the narrow interval contains an integer. The corrected full README
was then reread; no claim that integer ceiling spacing is O(m^-3) remains.

I accurately distinguishes its unconditional o(m) remainder from its
conditional O(1) refinement, and attributes removal of the condition to
the SEPARATE reviewed J proof. It keeps the complete original final-onset
quantifier and documents the actual endpoint-omission diagnostic failure.
J accurately states all fixed-order uniqueness/nondegeneracy, analytic
branches and strict derivatives, one transverse crossing, the actual
critical-window sign conclusion, and the unconditional fixed-order O(1)
onset. It retains both leading signs at the crossing without saying both
win at each finite dimension. Its alpha_x and minimum-d decimals are
expressly illustrations, not exact definitions or rigorous intervals.
It discloses both actual independent reviewer numeric-helper failures
and subsequent PASSs, with the internal AI-agent status explicit.

The ordinary reports copied into the candidates are byte-identical to the
reviewer's H_REVIEW, I_REVIEW and latest J_REVIEW, respectively. Original
maps and H follow-up/I history match the reviewed copies. Each literal
FINAL_STATUS.diff was read completely and contains review-completion
status, source references, and corresponding proof-status language only.
For EACH candidate I independently reversed its unified difference on
byte lines, checked every context/addition and hunk count, and recovered
the original reviewed PAPER bytes exactly. I also independently generated
the ENTIRE forward unified difference and verified byte equality with the
presented diff. This detects any unlisted source changes. No mathematical
formula, hypothesis, dimension/order quantifier, equality case, sign/rank
tie, or proof step was changed.

The source snapshots and restored reviewed bytes are preserved under
`final-source-snapshots/'''+stamp+'''/`. Exact hashes are:

| Target | Reviewed PAPER SHA-256 | Final PAPER SHA-256 | Final README SHA-256 |
|---|---|---|---|
'''
for key,entry in entries.items():
    text+='| '+key+' | `'+entry['reviewed_paper_sha256']+'` | `'+entry['final_paper_sha256']+'` | `'+entry['readme_sha256']+'` |\n'
text+='''
The separate FINAL_STATUS_REVIEW.json records these sources, diffs, reports,
target maps and created FINAL_STATUS_BINDING files by SHA-256. The three
candidate binding files were the only writes outside the reviewer's own
directory. PAPER/README/DIFF, earlier frozen sources and ordinary reports
were not modified by the reviewer. Author and reviewer failure snapshots
are retained as history, not alternate current theorem statements. This
step does not verify new future evidence-location layout or packaging;
those links must be retained when the repository integration is assembled.

The preserved old predecessor-review script has its original byte hash.
Restoring its expected sibling input directory supports its old INPUT
path without changing its code and claiming unchanged bytes. No rerun
of that script or any other mathematical control was performed here.

The new proposed alpha=alpha_x+u/m coupled-window research is explicitly
OUTSIDE this binding. Neither fixed-order theorems nor final metadata
edits automatically supply such a varying-order theorem. Mathematical
changes after these literal final hashes require a new read. There is
no priority certificate, single exact ceiling, effective cutoff, or
all-finite-dimensional/ASEP claim.
'''
doc=ROOT/'FINAL_STATUS_REVIEW.md';doc.write_text(text)
record={'status':'PASS','review_kind':'independent final status/source/README binding',
        'bound_utc':datetime.now(timezone.utc).isoformat(),'manual_readmes_complete':True,
        'manual_diffs_complete':True,'mathematical_controls_rerun':False,'Lean':False,
        'manifest':rec(META.read_bytes()),'targets':entries,
        'report':rec(doc.read_bytes()),'script':rec(Path(__file__).read_bytes()),
        'snapshot_directory':str(SAVE),'unexpected_failures_in_this_binding':0,
        'changes_requested':['H README: clarify that O(m^-3) applies to real ceiling arguments, not their integer difference.'],
        'requested_change_resolved_before_binding':True,
        'writes_outside_own_directory':[str(p) for p in pending],
        'outside_scope':['new coupled varying-alpha mathematics','later packaging/link layout','new Lean or old audit expansion','priority verification']}
(ROOT/'FINAL_STATUS_REVIEW.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':'PASS','report_sha256':sha(doc.read_bytes()),
                  'report_json_sha256':sha((ROOT/'FINAL_STATUS_REVIEW.json').read_bytes()),
                  'final_paper_hashes':{k:v['final_paper_sha256'] for k,v in entries.items()}}))
