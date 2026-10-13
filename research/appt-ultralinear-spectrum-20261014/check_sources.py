"""Read-only source/review/diagnostic/link correspondence, not a Lean audit."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

packet=Path(__file__).resolve().parent
repo=packet.parents[1]
manifest=json.loads((packet/'SOURCE_HASHES.json').read_text())
errors=[]
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
for rel,expected in manifest['files'].items():
    path=packet/rel
    if not path.is_file() or digest(path)!=expected:
        errors.append('packet '+rel)
for rel,expected in manifest['inherited_inputs'].items():
    path=repo/rel
    if not path.is_file() or digest(path)!=expected:
        errors.append('inherited '+rel)
review=json.loads((packet/'MANUSCRIPT_REVIEW.json').read_text())
if review['changes_requested']:
    errors.append('unresolved review requests')
checks=[]
for item in review['reviewed_files']:
    ok=digest(repo/item['path'])==item['sha256']
    checks.append({'path':item['path'],'pass':ok,'sha256':item['sha256']})
    if not ok:
        errors.append('review '+item['path'])
if len(checks)!=3:
    errors.append('expected three full-read sources')
for name in ['DIAGNOSTICS_STANDARD.json','DIAGNOSTICS_OPTIMIZED.json','DIAGNOSTICS_WSL.json']:
    data=json.loads((packet/name).read_text())
    if data['status']!='PASS' or data['case_count']!=42:
        errors.append('diagnostic '+name)
comparison=json.loads((packet/'DIAGNOSTIC_COMPARISON.json').read_text())
if comparison['status']!='PASS':
    errors.append('environment comparison')
links=0
for path in packet.glob('*.md'):
    for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)',path.read_text()):
        if target.startswith(('https:','http:','mailto:','#')):
            continue
        links+=1
        if not (path.parent/target.split('#',1)[0]).is_file():
            errors.append('link '+path.name+' -> '+target)
result={'kind':'Literal working-tree source/review/link check',
        'worktree_head_at_check':subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip(),
        'packet_sources':len(manifest['files']),'inherited_inputs':len(manifest['inherited_inputs']),
        'reviewed_sources':checks,'owned_links':links,'finite_cases_per_run':42,
        'universal_proof_by_script':False,'lean_execution':False,'new_audit_roots':0,
        'errors':errors,'status':'PASS' if not errors else 'FAIL'}
(packet/'SOURCE_CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='reviewed_sources'},indent=2))
if errors:
    raise SystemExit(1)
