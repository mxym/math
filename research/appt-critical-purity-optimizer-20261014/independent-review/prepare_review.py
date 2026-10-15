"""Freeze actual review evidence; no git, publication, author, or Lean changes."""
from pathlib import Path
from fractions import Fraction as F
from datetime import datetime, timezone
import hashlib
import json
import difflib
import shutil

DIR = Path(__file__).resolve().parent
BASE = DIR.parent
REPO = Path('/home/mxym/math-appt-multiscale-20261013/research')
QBASE = BASE.parent / 'appt-exact-purity-onset-20261014'


def bind(path):
    raw = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
            'bytes': len(raw), 'lines': len(raw.splitlines())}


def frac(raw):
    return F(raw)


delta = json.loads((BASE / 'FINAL_STATUS_DELTAS.json').read_text())
source = {}
expected_changed = {'PAPER.md': [3, 291], 'THEOREM_MAP.md': [3, 36], 'README.md': [3, 17, 18]}
for name in expected_changed:
    initial = BASE / ('INITIAL_' + name)
    final = BASE / name
    ib, fb = initial.read_bytes(), final.read_bytes()
    assert hashlib.sha256(ib).hexdigest() == delta[name]['initial_sha256']
    assert hashlib.sha256(fb).hexdigest() == delta[name]['final_sha256']
    backwards = fb
    for change in reversed(delta[name]['changes']):
        old, new = change['old'].encode(), change['new'].encode()
        assert backwards.count(new) == 1
        backwards = backwards.replace(new, old, 1)
    assert backwards == ib
    il, fl = ib.splitlines(), fb.splitlines()
    assert len(il) == len(fl)
    changed = [i + 1 for i, (x, y) in enumerate(zip(il, fl)) if x != y]
    assert changed == expected_changed[name]
    shutil.copyfile(initial, DIR / ('SNAPSHOT_' + name))
    shutil.copyfile(final, DIR / ('FINAL_' + name))
    source[name] = {'initial': bind(initial), 'final': bind(final),
        'full_initial_read_ranges': [[1, len(il)]],
        'actual_final_changed_lines_read': changed,
        'inverse_status_reconstruction_sha256': hashlib.sha256(backwards).hexdigest(),
        'mathematical_changes': 0, 'no_second_complete_final_read_claimed': True,
        'initial_snapshot': 'SNAPSHOT_' + name, 'final_snapshot': 'FINAL_' + name,
        'status_diff': bind(BASE / ('FINAL_STATUS_' + name + '.diff'))}

support = {}
for name, expected in [
    ('LITERATURE.md', '25428c200426f1380417bcd55050faab15513d8ee60cbff8e90f3fde030a93ff'),
    ('check_critical.py', '9b9cece20e23d6984f48f045d5059b1765505531ed6c5667f94b8087cc858ef9'),
    ('author_checks.json', '0b355183445c5d76a9734bbfe2df5ba3b00b94fbdd3a6f68522736ebcf74cb4d')]:
    data = bind(BASE / name)
    assert data['sha256'] == expected
    data['reading_method'] = ('complete structured JSON parse and all result rows checked; no sequential raw-line claim'
                              if name.endswith('.json') else 'complete sequential reading')
    if not name.endswith('.json'):
        data['read_ranges'] = [[1, data['lines']]]
    support[name] = data

author = json.loads((BASE / 'author_checks.json').read_text())
assert author['status'] == 'PASS_AUTHOR_FINITE_CONTROLS'
for name, row in author['files'].items():
    reference = source[name]['initial'] if name in source else bind(BASE / name)
    assert row['sha256'] == reference['sha256']
    assert row['lines'] == reference['lines']
for row in author['all_slot_psd_controls']:
    assert frac(row['exact_psd_slack']) >= 0
for row in author['tiny_tail_relative_comparisons']:
    assert frac(row['old_profit_over_bulk']) > 0
    assert frac(row['feasible_improvement']) > 0
    assert float(row['anomaly_gain_per_tau']) < .02
    assert float(row['body_gain_per_protection_slack']) > .1
for row in author['strict_endpoint_body_controls']:
    assert frac(row['strict_endpoint_improvement']) > 0
for row in author['tiny_protection_slack_controls']:
    assert frac(row['strict_improvement']) > 0
for row in author['false_unconditional_variance_bound_controls']:
    assert frac(row['actual_body_derivative_over_kappa']) < F(1, 4)
    assert row['body_not_profitable'] and row['false_universal_derivative_bound_rejected']
counts = {name: len(author[name]) for name in [
    'symbolic_groups', 'all_slot_psd_controls', 'tiny_tail_relative_comparisons',
    'strict_endpoint_body_controls', 'tiny_protection_slack_controls',
    'false_unconditional_variance_bound_controls']}
assert counts == {'symbolic_groups': 5, 'all_slot_psd_controls': 378,
    'tiny_tail_relative_comparisons': 18, 'strict_endpoint_body_controls': 9,
    'tiny_protection_slack_controls': 6, 'false_unconditional_variance_bound_controls': 3}
validation = {'status': 'PASS_STRUCTURED_AUTHOR_JSON_VALIDATION', 'counts': counts,
              'manifest_source_matches_initial_bytes': True,
              'all_result_rows_checked': True, 'author_code_imported_or_rerun': False}
(DIR / 'AUTHOR_REPORT_STRUCTURAL_VALIDATION.json').write_text(json.dumps(validation, indent=2) + '\n')

dependencies = {}
for key, path in [('C0-C4', REPO / 'appt-cubic-entropy-20261014/PAPER.md'),
                  ('E0-E4', REPO / 'appt-exact-cubic-bulk-20261014/PAPER.md'),
                  ('Q0-Q3', QBASE / 'PAPER.md')]:
    rec = bind(path)
    rec['read_ranges'] = [[1, rec['lines']]]
    rec['scope'] = 'complete ordinary manuscript read to verify correct invocation; credited earlier inputs remain credited; no Lean/audit rerun'
    snap = 'DEPENDENCY_' + key.replace('-', '_') + '_PAPER.md'
    shutil.copyfile(path, DIR / snap)
    rec['snapshot'] = snap
    dependencies[key] = rec
qreview = json.loads((QBASE / 'independent-review/REVIEW.json').read_text())
assert qreview['verdict'] == 'PASS_COMPLETE_INDEPENDENT_ORDINARY_REVIEW'
assert qreview['source_binding']['PAPER.md']['final']['sha256'] == dependencies['Q0-Q3']['sha256']
qreview_binding = bind(QBASE / 'independent-review/REVIEW.json')
assert qreview_binding['sha256'] == '1594615be9547e9236f4ad7a0b837b574864fba3da085a609560fdf7a21661e9'
helper = bind(QBASE / 'check_onset.py')
assert helper['sha256'] == '1f03b7bf332c304bc7ab408b897ccbd72ecc019a9a4be9b0e1a901b44898ac03'
helper['read_ranges'] = [[1, helper['lines']]]
helper['scope'] = 'complete sequential code reading to check imported author functions; reviewer did not import or run this code, and no old main was executed'
shutil.copyfile(QBASE / 'check_onset.py', DIR / 'CREDITED_AUTHOR_HELPER_check_onset.py')

ind = json.loads((DIR / 'independent_checks.json').read_text())
assert not ind['failures']
for row in ind['bindings']:
    filename = Path(row['path']).name
    assert row['sha256'] == source[filename]['initial']['sha256']
assert ind['script_binding']['sha256'] == bind(DIR / 'check_independent.py')['sha256']
for row in ind['tiny_tail_deformation']:
    assert frac(row['exact_positive_min_slack']) > 0
    assert frac(row['exact_max_rank_one_product']) < 1
    assert row['normalized_purity_strictly_increases']

findings = [
    (7,63,'whole finite statement',
     'The target is every actual all-unitary APPT optimizer on each fixed A critical band, not a selected trial family. The compact scalar and two actual ranks retain every tie; no scalar uniqueness is asserted.'),
    (65,109,'unrestricted localization and uniform body variance',
     'E0 controls every profitable state and has errors proportional to c, excluding arbitrarily tiny c>0 near the empty profile. C0/C4 then localize the entire lists and J loss. Dividing by D*kappa^2 and using the uniform bounded-moment expansion gives variance->1/4 without a rate assumption.'),
    (111,135,'exact cost of every omitted anomaly',
     'The actual fully assigned Schmidt witness is PSD. Positive kappa makes its inverse base PD. Nonnegative walks keep all selected-edge walks and 2*tau/a^2 from every remaining slot, including overlaps. The strictly increasing implicit cost gives c-c0>=1.6*tau with no additive error.'),
    (137,160,'feasibility of same-coordinate boundary deformation',
     'The retained theta has top R entries one and bottom K zero, so the changed contrast preserves the adverse spectral-pairing shape. The single-edge base is PD and its exact rank-one product is one. All edge permutations and zero Schmidt coordinates are covered; arbitrary middle theta stays feasible.'),
    (162,181,'relative true-normalization comparison',
     'The raw increment excludes coordinate one, so there is no cross term with the retained head. Subtraction of actual logarithms cancels the leading signed trace mass. Remaining energy is <=eta*tau and all mean/quadratic errors are proportional to tau. Arbitrarily tiny tails are covered.'),
    (183,217,'uniform contrast gain and strict finite tail/slack elimination',
     'The exact derivative expands uniformly as 2*k*variance+O(k^2+1/D). Profitable-state localization supplies variance near 1/4 over the whole protection interval, giving derivative>=k/4. Its integrated coefficient tends to 1/8, so 1/10 is valid. The relative removal error <=tau/50 is strictly beaten using c-c0>=1.6*tau, including tau=0 with positive slack.'),
    (219,235,'strict endpoint cube equality',
     'Every body cube point is genuinely feasible with fixed head. Trace reweighting yields a convex combination of normalized endpoint vertices. They are distinct because their common positive head fixes any rescaling. Strict purity convexity therefore excludes every interior body coordinate at an optimizer.'),
    (237,256,'exact scalar/rank value and all matrix equality',
     'Localization puts every nonbulk optimizer strictly inside [1,3]. All parameters in that compact interval are physical. The chord is exact, the real trace optimum has one sign change, and only floor/ceil can win. Both counts fit uniformly; the equivalent finite maximum of continuous branches proves attainment despite floor/ceil switches. Every unitary conjugate and all genuine ties are retained.'),
    (258,277,'strict phase selection on the entire band',
     'Q0-Q3 excludes every nonbulk optimizer at or above onset. Below onset the rational boundary profile has h-n>=1/8 uniformly throughout the band, not only at N-1. Its order m^-8 purity margin dominates the actual integer-rank loss of order m^-11. Thus bulk cannot win anywhere below onset in the stated band.'),
    (279,292,'scope and provenance',
     'The assertion is ordinary and eventual for each fixed A. It claims neither an effective cutoff, all finite dimensions, other entropy orders, ASEP, scalar-parameter uniqueness, new major-conjecture solution, nor a Lean audit. The bounded literature disclosures do not claim exhaustive historical priority.')]

review = {
    'verdict': 'PASS_COMPLETE_INDEPENDENT_ORDINARY_REVIEW',
    'reviewer': '/root/ordinary_review_critical_purity',
    'utc_completed': datetime.now(timezone.utc).isoformat(),
    'target': 'W0-W3: original complex all-global-unitary APPT; exact finite purity value and EVERY optimizer throughout each fixed |n-m^2/4|<=A*m eventual band',
    'review_kind': 'independent AI subagent ordinary mathematical review; not external human peer review or formal certification',
    'mathematical_issues': [], 'required_mathematical_changes': 0,
    'full_initial_mathematical_source_lines_read': 328,
    'support_lines_sequentially_read': 207,
    'credited_author_helper_lines_read': 207,
    'dependency_ordinary_lines_read': 1199,
    'actual_final_status_lines_read': 7,
    'source_binding': source, 'unchanged_support': support,
    'credited_dependency_binding': dependencies,
    'credited_Q0_separate_review_binding': qreview_binding,
    'credited_author_helper_binding': helper,
    'status_delta_manifest': bind(BASE / 'FINAL_STATUS_DELTAS.json'),
    'findings': [{'paper_lines': [lo,hi], 'topic': topic, 'conclusion': 'PASS', 'reason': reason}
                 for lo,hi,topic,reason in findings],
    'independent_controls': {
        'executions': 4, 'passing_executions': 3,
        'script': bind(DIR / 'check_independent.py'),
        'final_raw_report': bind(DIR / 'independent_checks.json'),
        'versions': ind['versions'], 'precision_digits': 420,
        'counts': {'symbolic': 8, 'all_pattern_exact_fraction_PSD': 882,
            'tiny_tail_deformations': 3, 'zero_tail_tiny_slack': 3,
            'cube_checks': 3, 'integer_rank_exclusion': 56,
            'nearest_only_rejected': 1, 'unconditional_contrast_bound_rejected': 1,
            'small_m_false_extension_rejected': 1},
        'author_code_imported_or_rerun': False,
        'failures_or_invalid_runs': [{'execution': 1,
            'kind': 'independent test construction: ordered Sympy substitutions reintroduced unscaled D',
            'evidence': bind(DIR / 'INITIAL_FAILED_RUN.txt'),
            'resolution': 'apply Y,Z moment substitution first, then D scaling; author mathematics unchanged'}],
        'passing_raw_records_retained': [bind(DIR / name) for name in [
            'PASS_BEFORE_EXTRA_GUARD.json', 'PASS_BEFORE_EXACT_SLACK.json', 'independent_checks.json']],
        'repeat_reason': 'meaningful additional unconditional-variance guard and exact rational slack evidence; early passing reports preserved',
        'deleted_records': False,
        'scope': 'finite controls complement the complete written proof; no finite collection is a whole-domain certificate'},
    'author_controls': {'status': author['status'], 'counts': counts,
        'reading': 'entire JSON parsed; every result row and initial source manifest checked; no sequential 5250-line reading claim',
        'validation': bind(DIR / 'AUTHOR_REPORT_STRUCTURAL_VALIDATION.json'),
        'report_binding': support['author_checks.json'], 'script_rerun_by_reviewer': False,
        'profitable_nonoptimal_multihead_states_retained': True},
    'primary_literature_screen': {'method': 'bounded metadata and abstract reading only',
        'primary_urls': ['https://arxiv.org/abs/2609.18568',
            'https://journals.aps.org/pra/abstract/10.1103/PhysRevA.76.052325'],
        'full_primary_proofs_read_or_priority_certified': False},
    'scope_exclusions': ['no new Lean/Lake/kernel execution', 'no inherited audit-scope expansion',
        'no external human peer review or exhaustive priority certification',
        'no effective M_A or all-small-dimension theorem', 'no ASEP or other entropy order',
        'no unique maximizing z assertion', 'no git or publication mutation by reviewer']}
(DIR / 'REVIEW.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps({'verdict': review['verdict'], 'math_changes': 0,
                  'lines': {'initial_math': 328, 'support': 207, 'helper': 207,
                            'dependencies': 1199, 'actual_final_status': 7},
                  'review_json': bind(DIR / 'REVIEW.json')}))
