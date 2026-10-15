"""Revise only publication navigation/transport metadata, retaining all original versions."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, difflib

base = Path('/mnt/d/math/tmp/research-resume-20261015')
stage = base / 'scalar-phase-publication'
root = Path('/home/mxym/math-appt-multiscale-20261013')
indices = stage / 'index-candidates'
public = stage / 'public-sources'
hist = public / 'appt-linear-phase-ordinary-20261015/readme-organization-history/navigation-correction'
newhead = '49f572d05df426fe9cfc36126dfea6accc6d5407'
oldhead = 'c4e0d9e713ba349d376469231789bb7b36915b7d'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def replace_once(p, old, new):
    text = p.read_text()
    assert text.count(old) == 1, (str(p), old, text.count(old))
    p.write_text(text.replace(old, new, 1))

if hist.exists():
    raise RuntimeError('Do not overwrite the navigation correction history')
sync = json.loads((stage / 'PARALLEL_SYNC_RECEIPT.json').read_text())
assert sync['new_head'] == newhead and sync['root_clean']
for project in public.iterdir():
    assert not (project / 'FINAL_STATUS_BINDING.json').exists(), project.name
hist.mkdir(parents=True)
private_history = stage / 'before-four-index-navigation-revision'
private_history.mkdir()
for name in ['PREPARED_CANDIDATES.json', 'FINAL_CANDIDATE_INPUTS.json',
             'preflight_metadata.py', 'integrate.py', 'commit.py', 'transport.py']:
    shutil.copyfile(stage / name, private_history / name)
shutil.copytree(indices, private_history / 'index-candidates')
shutil.copyfile(base / 'prepare_scalar_publication.py', private_history / 'prepare_scalar_publication.py')
shutil.copyfile(root / 'SOLVED_PROBLEMS.md', hist / 'SOLVED_PROBLEMS.before.md')
original = (root / 'SOLVED_PROBLEMS.md').read_text()
oldnav = '[具名猜想与问题清单](README.md#已宣称解决的问题)'
newnav = '[预印本与问题对应](README.md#预印本)'
oldtitle = '# 已宣称解决的问题与专题结果'
newtitle = '# 问题与专题成果索引'
assert original.count(oldnav) == original.count(oldtitle) == 1
updated = original.replace(oldtitle, newtitle, 1).replace(oldnav, newnav, 1)
(indices / 'SOLVED_PROBLEMS.md').write_text(updated)
patch = ''.join(difflib.unified_diff(original.splitlines(True), updated.splitlines(True),
                                   fromfile='SOLVED_PROBLEMS.before.md', tofile='SOLVED_PROBLEMS.md'))
(hist / 'NAVIGATION_CORRECTION.diff').write_text(patch)
shutil.copyfile(Path(__file__), hist / 'executed_revision_script.py')
index = json.loads((indices / 'INDEX_BINDINGS.json').read_text())
for name, vals in index.items():
    assert sha(root / name) == vals['before_sha256'], name
    assert sha(indices / name) == vals['after_sha256'], name
index['SOLVED_PROBLEMS.md'] = {'before_sha256': sha(root / 'SOLVED_PROBLEMS.md'),
                               'after_sha256': sha(indices / 'SOLVED_PROBLEMS.md')}
(indices / 'INDEX_BINDINGS.json').write_text(json.dumps(index, indent=2) + '\n')
record = json.loads((stage / 'PREPARED_CANDIDATES.json').read_text())
record['original_preparation_base'] = record['source_base']
record['source_base'] = newhead
record['index_candidates'] = index
record['navigation_revision_utc'] = datetime.now(timezone.utc).isoformat()
record['prior_candidates_preserved'] = str(private_history)
(stage / 'PREPARED_CANDIDATES.json').write_text(json.dumps(record, indent=2) + '\n')

evidence_readme = public / 'appt-linear-phase-ordinary-20261015/README.md'
shutil.copyfile(evidence_readme, hist / 'EVIDENCE_README.before.md')
replace_once(evidence_readme, 'all three\nrepository index edits', 'all four\nrepository index edits')
preflight = stage / 'preflight_metadata.py'
replace_once(preflight, "for name in ['README.md','README.en.md','RESEARCH.md']:files[name]=indices/name",
             "for name in ['README.md','README.en.md','RESEARCH.md','SOLVED_PROBLEMS.md']:files[name]=indices/name")
replace_once(preflight, "canonical=['README.md','README.en.md','RESEARCH.md',",
             "canonical=['README.md','README.en.md','RESEARCH.md','SOLVED_PROBLEMS.md',")
integrate = stage / 'integrate.py'
replace_once(integrate, "base='" + oldhead + "'", "base='" + newhead + "'")
replace_once(integrate,
             "prior=Path('/mnt/d/math/tmp/research-resume-20261015/finite-han-publication/TRANSPORT_BINDINGS.json')",
             "prior=stage/'PARALLEL_BASE_BINDINGS.json'")
replace_once(integrate, "if recovering and rel in ['README.md','README.en.md','RESEARCH.md']:continue",
             "if recovering and rel in ['README.md','README.en.md','RESEARCH.md','SOLVED_PROBLEMS.md']:continue")
replace_once(stage / 'commit.py',
             'research: determine APPT coexistence thresholds and the large-order pure envelope',
             'research: organize result and attempt indexes; add reviewed APPT phase proofs')
replace_once(stage / 'transport.py',
             "'kind':'ordinary APPT scalar pole and bulk coexistence thresholds,",
             "'kind':'bilingual result/attempt index organization and ordinary APPT scalar pole and bulk coexistence thresholds,")
builder = base / 'prepare_scalar_publication.py'
replace_once(builder, "!='" + oldhead + "'", "!='" + newhead + "'")
replace_once(builder, 'all three\nrepository index edits', 'all four\nrepository index edits')
insert = """solved=(root/'SOLVED_PROBLEMS.md').read_text()
assert solved.count('[具名猜想与问题清单](README.md#已宣称解决的问题)')==1
solved=solved.replace('# 已宣称解决的问题与专题结果','# 问题与专题成果索引',1).replace('[具名猜想与问题清单](README.md#已宣称解决的问题)','[预印本与问题对应](README.md#预印本)',1)
(indices/'SOLVED_PROBLEMS.md').write_text(solved)
indexrecord['SOLVED_PROBLEMS.md']={'before_sha256':sha(root/'SOLVED_PROBLEMS.md'),'after_sha256':sha(indices/'SOLVED_PROBLEMS.md')}
"""
replace_once(builder, "(indices/'INDEX_BINDINGS.json').write_text", insert + "(indices/'INDEX_BINDINGS.json').write_text")
finding = {'utc': datetime.now(timezone.utc).isoformat(), 'kind': 'real navigation defect and upstream-base correction',
           'finding': 'Removing the former claimed-results heading left an active inbound anchor in SOLVED_PROBLEMS.md; old 451-link checks did not include that file.',
           'correction': 'Change only the catalog title and one navigation link; bind all four final index files. Three mathematical source bytes and individual review scopes are unchanged.',
           'old_base': oldhead, 'new_upstream_base': newhead,
           'upstream_sync_receipt_sha256': sha(stage / 'PARALLEL_SYNC_RECEIPT.json'),
           'solved_before_sha256': sha(root / 'SOLVED_PROBLEMS.md'),
           'solved_after_sha256': sha(indices / 'SOLVED_PROBLEMS.md'),
           'four_index_bindings': index,
           'independent_final_binding_pending': True, 'new_Lean_executions': 0}
(hist / 'FINDING_AND_REVISION.json').write_text(json.dumps(finding, indent=2) + '\n')
shutil.copyfile(stage / 'PARALLEL_SYNC_RECEIPT.json', hist / 'PARALLEL_SYNC_RECEIPT.json')
(stage / 'FOUR_INDEX_REVISION.json').write_text(json.dumps({**finding,
    'revised_script_hashes': {str(p.relative_to(base)): sha(p) for p in
                            [preflight, integrate, stage / 'commit.py', stage / 'transport.py', builder]}}, indent=2) + '\n')
print(json.dumps({'status': 'FOUR_INDEX_CANDIDATES_PREPARED', 'source_base': newhead,
                  'index_count': len(index), 'mathematical_sources_unchanged': True}))
