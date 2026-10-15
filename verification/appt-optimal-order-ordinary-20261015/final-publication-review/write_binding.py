"""Publish the authorized final metadata binding, without running controls."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

HERE = Path(__file__).resolve().parent
PUB = HERE.parent / 'optimal-order-publication'
CANDIDATE = PUB / 'public-sources' / 'appt-optimal-entropy-order-20261015'
INDEX = PUB / 'index-candidates'

def info(data):
    return {'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data),
            'lines': len(data.splitlines())}

def fileinfo(path):
    return info(path.read_bytes())

manifest = json.loads((HERE / 'INPUT_MANIFEST.json').read_text())
for relative, record in manifest['files'].items():
    assert fileinfo(HERE / relative)['sha256'] == record['sha256'], relative
for path in sorted(CANDIDATE.rglob('*')):
    if path.is_file() and path.name != 'FINAL_STATUS_BINDING.json':
        assert path.read_bytes() == (HERE / 'snapshot' / 'candidate' / path.relative_to(CANDIDATE)).read_bytes()
for path in INDEX.iterdir():
    if path.is_file():
        assert path.read_bytes() == (HERE / 'snapshot' / 'index' / path.name).read_bytes()
assert fileinfo(CANDIDATE / 'README.md')['sha256'] == '74aa112c6be680616d74786b204574f605387f331c2b8ed30b085a51e16d044a'
checks = json.loads((HERE / 'BYTE_CHECKS.json').read_text())
for scope in ['L', 'M']:
    relation = checks['math_source_relations'][scope]
    assert relation['inverse_exact'] and relation['complete_diff_exact']
    assert not relation['mathematical_changes']
files = {path.name: fileinfo(path) for path in CANDIDATE.iterdir() if path.is_file()
         and path.name != 'FINAL_STATUS_BINDING.json'}
binding = {
    'decision': 'PASS',
    'kind': 'independent final source-status README and three-index byte binding',
    'reviewer': 'internal AI agent /root/critical_entropy_review_resume_20261015',
    'bound_utc': datetime.now(timezone.utc).isoformat(),
    'mathematical_scopes_separate': ['L0-L2', 'M0-M2'],
    'new_mathematical_review': False,
    'new_mathematical_or_author_controls_executed': False,
    'new_Lean_or_old_audit_expansion': False,
    'external_human_peer_review': False,
    'author_mathematical_sources_changed': False,
    'source_relations': checks['math_source_relations'],
    'candidate_top_level_files': files,
    'literal_L_M_reports_preserved_exactly': True,
    'REVIEW_md_json_are_root_assembled_index_not_new_independent_reports': True,
    'readme_scope': {
        'actual_original_all_global_unitary_APPT': True,
        'N_least_integer_N_ge_m_all_later_integer_n_infinity_allowed': True,
        'all_positive_finite_orders_minimized_after_separate_escape_exclusions': True,
        'sufficiently_large_m_and_each_fixed_H': True,
        'every_minimizing_or_fixed_additive_gap_order': True,
        'integer_ties_and_no_finite_unique_order': True,
        'numeric_constants_illustrations_not_intervals': True,
        'no_arbitrary_moving_order_whole_extremum_classification': True,
        'internal_AI_ordinary_review_not_external_human_or_Lean': True,
        'initial_M_independent_checker_failure_directly_disclosed': True},
    'metadata_history': {
        'two_clarifications': ['explicit least integer N>=m',
            'direct initial M checker failure and retained versions/successes disclosure'],
        'old_README_author_copy': 'author-versions/publication-metadata-v1/README.md',
        'old_README_sha256': fileinfo(CANDIDATE / 'author-versions/publication-metadata-v1/README.md')['sha256'],
        'clarification_diff': fileinfo(HERE / 'history/publication-metadata-v1/README-clarifications.diff'),
        'math_changes': False,
        'unresolved_findings': []},
    'actual_M_failure_history_preserved_in_literal_review': {
        'failed_run': '20261015T083524.651443Z',
        'cause': 'reviewer diagnostic unproved coefficient ten too small; source O constant not fixed to ten',
        'passed_runs': ['20261015T083604.420048Z', '20261015T084023.622885Z'],
        'controls_rerun_for_this_binding': False},
    'index_relations': checks['index_relations'],
    'index_ADDED_ROWS_md': fileinfo(INDEX / 'ADDED_ROWS.md'),
    'index_author_BINDINGS_json': fileinfo(INDEX / 'INDEX_BINDINGS.json'),
    'independent_read_report': fileinfo(HERE / 'FINAL_STATUS_REVIEW.md'),
    'input_manifest': fileinfo(HERE / 'INPUT_MANIFEST.json'),
    'exact_byte_checks': fileinfo(HERE / 'BYTE_CHECKS.json'),
    'future_evidence_layout_verified': False,
    'planned_evidence_reference_only': 'verification/appt-optimal-order-ordinary-20261015/README.md',
    'future_integration_git_readback_or_transport_certified': False,
    'no_new_major_conjecture_count': True,
    'no_fetch_commit_push_submission_or_release_by_this_task': True
}
payload = (json.dumps(binding, indent=2) + '\n').encode()
own = HERE / 'FINAL_STATUS_BINDING.json'
candidate = CANDIDATE / 'FINAL_STATUS_BINDING.json'
own.write_bytes(payload)
candidate.write_bytes(payload)
assert own.read_bytes() == candidate.read_bytes() == payload
result = {'decision': 'PASS', 'scope': 'L/M final metadata and three indices only',
          'binding': fileinfo(own), 'report': fileinfo(HERE / 'FINAL_STATUS_REVIEW.md'),
          'candidate_binding_identical': True, 'controls_rerun': False,
          'future_evidence_layout_verified': False}
(HERE / 'FINAL_STATUS_REVIEW.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
