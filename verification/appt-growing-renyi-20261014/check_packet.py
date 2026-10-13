"""Read-only byte/review/link validation. No Lean or mathematical solver."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

repo = Path(__file__).resolve().parents[2]
packet = repo/'research/appt-growing-renyi'
record_dir = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

manifest = json.loads((packet/'SOURCE_HASHES.json').read_text())
errors = []
for category in ('files', 'inherited_mathematical_inputs'):
    for rel, expected in manifest[category].items():
        path = repo/rel
        if not path.is_file() or digest(path) != expected:
            errors.append('Source binding: '+rel)

review_checks = []
for name in ('MANUSCRIPT_REVIEW.json', 'LINEAR_ORDER_REVIEW.json', 'ALL_ORDER_REVIEW.json'):
    data = json.loads((packet/name).read_text())
    if data.get('unresolved_required_changes', data.get('changes_requested', [])):
        errors.append('Outstanding review request: '+name)
    for item in data.get('reviewed_files', data.get('source_files', [])):
        path = repo/item['path']
        passed = path.is_file() and digest(path) == item['sha256']
        review_checks.append({'review': name, 'path': item['path'],
                              'sha256': item['sha256'], 'pass': passed})
        if not passed:
            errors.append('Review binding: '+item['path'])
if len(review_checks) != 12:
    errors.append('Expected twelve literal full-read source records')

links_checked = 0
link_sources = [packet/'README.md', record_dir/'README.md']
link_sources += [repo/name for name in ('README.md', 'README.en.md', 'RESEARCH.md', 'SOLVED_PROBLEMS.md')]
for source in link_sources:
    for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)', source.read_text()):
        if target.startswith(('https:', 'http:', 'mailto:', '#', 'codex:')):
            continue
        target = target.split('#', 1)[0]
        if not target:
            continue
        # Only new packet and verification navigation is owned by this check.
        if source.parent not in (packet, record_dir) and 'appt-growing-renyi' not in target:
            continue
        links_checked += 1
        if not (source.parent/target).is_file():
            errors.append('Local link: '+str(source.relative_to(repo))+' -> '+target)

record = {
    'date': '2026-10-14 Asia/Shanghai',
    'kind': 'Read-only literal source/review/link correspondence',
    'worktree_head_at_check': subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD']).decode().strip(),
    'checked_object': 'Literal working-tree bytes bound by SOURCE_HASHES.json, including any pending catalogue edits',
    'packet_files_checked': len(manifest['files']),
    'inherited_mathematical_files_checked': len(manifest['inherited_mathematical_inputs']),
    'reviewed_source_checks': review_checks,
    'local_links_checked': links_checked,
    'mathematical_proof_by_script': False,
    'lean_execution': False,
    'new_audit_roots': 0,
    'external_human_peer_review': False,
    'priority_certification': False,
    'errors': errors,
    'status': 'PASS' if not errors else 'FAIL',
}
(record_dir/'CHECK.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps({k: v for k, v in record.items() if k != 'reviewed_source_checks'}, indent=2))
if errors:
    raise SystemExit(1)
