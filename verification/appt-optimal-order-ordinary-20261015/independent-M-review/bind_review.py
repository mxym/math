"""Bind the completed ordinary mathematical read; run no mathematical control."""
from pathlib import Path
from datetime import datetime, timezone
import difflib, hashlib, json

here = Path(__file__).resolve().parent
author = here.parent / 'optimal-entropy-order'

def entry(path):
    b = path.read_bytes()
    return {'sha256': hashlib.sha256(b).hexdigest(), 'bytes': len(b),
            'lines': len(b.splitlines())}

manifest = json.loads((here / 'INPUT_MANIFEST.json').read_text())
for relative, item in manifest['files'].items():
    assert entry(here / relative)['sha256'] == item['sha256'], relative
for name in ['GLOBAL_ORDER.md', 'GLOBAL_TARGET.md', 'global_checks.py',
             'PAPER.md', 'THEOREM_MAP.md', 'checks.py', 'REVIEW_HISTORY.md']:
    assert (author / name).read_bytes() == (here / 'snapshot' / 'M' / name).read_bytes(), name
runs = []
for name, status in [('20261015T083524.651443Z', 'FAIL'),
                     ('20261015T083604.420048Z', 'PASS'),
                     ('20261015T084023.622885Z', 'PASS')]:
    folder = here / 'runs' / name
    result = json.loads((folder / 'RESULT.json').read_text())
    assert result['status'] == status
    assert result['script_sha256'] == entry(folder / 'independent_checks.py')['sha256']
    assert result['input_manifest_sha256'] == entry(folder / 'INPUT_MANIFEST.json')['sha256']
    runs.append({'run': name, 'status': status, 'result': entry(folder / 'RESULT.json'),
                 'executed_script': entry(folder / 'independent_checks.py')})
old = (here / 'runs' / runs[0]['run'] / 'independent_checks.py').read_text()
fixed = (here / 'runs' / runs[1]['run'] / 'independent_checks.py').read_text()
assert old.replace('and abs(loss) * m**8 < 10,', 'and abs(loss) * m**8 < 2 / d0**2,') == fixed
portable = (here / 'runs' / runs[2]['run'] / 'independent_checks.py').read_text()
expected = fixed.replace('psi_a(y)/a, regular even at a=0. Used only for a<=1/2.',
                         'psi_a(y)/a, regular at a=0; all uses here stay away from a=1.').replace(
    "HERE.parent / 'independent-optimal-order-review' / 'runs' / '20261015T081127.835786Z' / 'RESULT.json'",
    "HERE / 'snapshot' / 'L-review' / 'independent-RESULT.json'")
assert portable == expected
assert (here / 'independent_checks.py').read_text() == portable
for earlier, later in zip(runs, runs[1:]):
    aa = (here / 'runs' / earlier['run'] / 'independent_checks.py').read_text().splitlines(True)
    bb = (here / 'runs' / later['run'] / 'independent_checks.py').read_text().splitlines(True)
    diff = ''.join(difflib.unified_diff(aa, bb, fromfile=earlier['run'], tofile=later['run']))
    (here / ('CHECKER-' + earlier['run'] + '-to-' + later['run'] + '.diff')).write_text(diff)
final_run = here / 'runs' / runs[-1]['run']
final = json.loads((final_run / 'RESULT.json').read_text())
assert final['groups']['symbolic']['checks'] == 4
assert final['groups']['tiny_order_factorization']['cases'] == 15
assert final['groups']['growing_order_gain']['cases'] == 15
assert final['groups']['exact_derivative']['cases'] == 45
assert final['groups']['fixed_state_unbounded_samples']['cases'] == 15
assert len(final['expected_rejections']) == 3
for rejected in final['expected_rejections']:
    assert rejected['status'] == 'REJECTED'
author_result = here / 'author-evidence' / 'global-control-runs' / '20261015T083026.400414Z' / 'RESULT.json'
assert json.loads(author_result.read_text())['status'] == 'PASS'
record = {
    'decision': 'PASS',
    'scope': 'M0-M2 frozen ordinary mathematical proof, separately from L0-L2',
    'reviewer': 'internal AI reviewer agent /root/critical_entropy_review_resume_20261015',
    'reviewed_utc': datetime.now(timezone.utc).isoformat(),
    'blind_review': False, 'external_human_peer_review': False,
    'formal_verification': False, 'new_Lean': False, 'old_audit_expanded': False,
    'author_sources_modified': False, 'mathematical_gaps_found': [],
    'math_sources': {name: entry(here / 'snapshot' / 'M' / name)
                     for name in ['GLOBAL_ORDER.md', 'GLOBAL_TARGET.md']},
    'actual_read': {
        'M': 'full 222-line manuscript and full 28-line target',
        'L': 'full current 205-line c76f83bf manuscript reread; separate earlier L PASS retained',
        'I_J_K': 'same reviewer full earlier frozen reads; published bytes/status-only inverse diffs previously compared, copied here; no automatic M coverage',
        'author_M_checker': 'full 89-line script and actual run RESULT read and hash-checked, not executed',
        'literature': 'no new exhaustive literature or priority investigation'},
    'claims': {
        'M0': 'one common physical n_m excludes every 0<alpha<=1/2 using alpha-relative analytic gain, derivative and physical rank error',
        'M1': 'same n_m excludes every alpha>=2 using uniform 2..alpha_star relative estimates then one fixed actual state, order monotonicity and universal integer bulk bound',
        'M2': 'full positive-axis finite attained FINAL-onset minimum, closed nonempty compact minimizing set, value d0*m^2+ac*m+O(1), every minimizer/fixed-additive-gap order alpha0+uc/m+O_H(m^-2)',
        'quantifiers': 'original all-global-unitary APPT; exact physical integer ranks and ties; N tests every later integer n; +infinity permitted; no positive-order lower or upper bound assumed before exclusion'},
    'not_claimed': ['exact finite onset or minimizing set', 'unique finite minimizing order',
        'effective dimension bound', 'arbitrary-moving-order exact entropy optimizer theorem',
        'finite diagnostics as full feasible-set proof', 'rigorous interval values for illustrated constants',
        'external human review', 'new Lean', 'new major-conjecture count'],
    'separate_L_report': entry(here / 'snapshot' / 'L-review' / 'REVIEW.json'),
    'input_manifest': entry(here / 'INPUT_MANIFEST.json'),
    'ordinary_report': entry(here / 'REVIEW.md'),
    'control_history': entry(here / 'CONTROL_HISTORY.md'),
    'independent_script': entry(here / 'independent_checks.py'),
    'independent_runs': runs,
    'unexpected_independent_failures': 1,
    'failure_resolution': 'unproved diagnostic coefficient ten too small for m^8 rank loss; source asserts unspecified O constant; checker fixed to 2/d0^2 only; source and first failure preserved',
    'final_run_portability_change': 'same exact independent L-result bytes now local to this snapshot; scalar-helper docstring clarified; no mathematical control or bound change',
    'expected_rejections_in_each_pass': final['expected_rejections'],
    'author_run': {'name': '20261015T083026.400414Z', 'status': 'PASS',
                   'result': entry(author_result), 'executed_by_reviewer': False,
                   'nine_pure_author_L_scalar_helpers_AST_selected': True},
    'final_metadata_binding': 'pending; this report binds mathematical source only'
}
(here / 'REVIEW.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'decision': record['decision'], 'scope': record['scope'],
                   'report': entry(here / 'REVIEW.md'), 'record': entry(here / 'REVIEW.json'),
                   'final_run': runs[-1]['run'], 'source_unchanged': True}))
