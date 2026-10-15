#!/usr/bin/env python3
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import copy
import difflib
import math
from fractions import Fraction

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent
ROOT = Path('/home/mxym/math-appt-multiscale-20261013')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def bind(path, ranges, **extra):
    return {'path': str(path), 'sha256': sha(path),
            'total_lines': len(path.read_text().splitlines()),
            'actual_read_ranges': ranges, **extra}

initial = json.loads((HERE / 'REVIEW_INITIAL.json').read_text())
review = copy.deepcopy(initial)
coverage = review['coverage']
coverage.pop('initial_current_PAPER.md')
coverage.pop('initial_current_THEOREM_MAP.md')
expected = {
    'PAPER.md': {'initial': 'ae5f04557e63a4af6f1d4329448f81d7ca30ea41099770b88a748bba68ce4927',
                 'final': '02143109991a9f6fba342d9f51d672b32e14fbec70a0b3c81bf24714d09ee21c',
                 'changes': [3, 377], 'reads': [[1, 6], [371, 377]]},
    'THEOREM_MAP.md': {'initial': '5e36d29cefa57f69dddccff7337db73bb633805983565ab7eb7b273b0cabb6c3',
                       'final': '488edad996b1aca123898ef3711cf2c6e849344beec7d884e1f3dee0ec19b68f',
                       'changes': [3, 5], 'reads': [[1, 18]]}
}
delta_records = {}
for name, spec in expected.items():
    old = (PACKET / ('INITIAL_' + name)).read_bytes()
    new = (PACKET / name).read_bytes()
    assert hashlib.sha256(old).hexdigest() == spec['initial']
    assert hashlib.sha256(new).hexdigest() == spec['final']
    before = old.decode().splitlines(keepends=True)
    after = new.decode().splitlines(keepends=True)
    assert len(before) == len(after)
    changes = [i + 1 for i, (x, y) in enumerate(zip(before, after)) if x != y]
    assert changes == spec['changes']
    reversed_lines = list(after)
    for line in changes:
        reversed_lines[line - 1] = before[line - 1]
    assert ''.join(reversed_lines).encode() == old
    delta_records[name] = {'only_changed_lines': changes,
                           'mathematical_changed_lines': [],
                           'inverse_hash_equals_initial': True,
                           'actual_delta_context_read': spec['reads'],
                           'changes': [{'line': i, 'initial': before[i - 1].rstrip('\n'),
                                        'final': after[i - 1].rstrip('\n')} for i in changes]}
    coverage[name] = bind(PACKET / name, spec['reads'],
                          initial_complete_review_source='INITIAL_' + name,
                          complete_second_final_reread_claimed=(name == 'THEOREM_MAP.md'),
                          binding='Exact disclosed status-only byte delta; reversing it restores the fully read initial source hash.')
review['final_status_deltas'] = delta_records
review['created_utc'] = datetime.now(timezone.utc).isoformat()
review['verdict'] = 'PASS: complete independent ordinary mathematical proof review of final E0-E4, with final status-only byte binding'
review['mathematical_initial_complete_lines'] = 395
review['mathematical_revisions'] = []
review['complete_second_final_paper_reread_claimed'] = False
for name, lines in [('README.md', 38), ('LITERATURE.md', 42), ('check_exact_bulk.py', 176)]:
    supplementary_expected = {
        'README.md': '837973428742210a95e8b8e87752507069ae64a3df76a293e92ba1db5857640e',
        'LITERATURE.md': '2267c2756ecb2a8b54b65e5a9e8b9caba96f0d418f0a310e4ab1d8b822ad2c54',
        'check_exact_bulk.py': 'bcfdf581e14a874b9ac30561e339cfd04d195bf1828fb505606f979099b003f3'
    }
    assert sha(PACKET / name) == supplementary_expected[name]
    coverage[name] = bind(PACKET / name, [[1, lines]],
                          author_script_rerun=False if name.endswith('.py') else None,
                          classification='Separately read supplementary source; not extra mathematical proof coverage.')
utility = PACKET.parent / 'appt-cubic-entropy-20261014/check_cubic.py'
assert sha(utility) == 'b7f69605ee10f0e16ed2cf5faaa451f95f95c0d321c315f8e99c4a03e8afd0e3'
coverage['credited_cubic_check_cubic.py'] = bind(utility, [[1, 209]],
                                              use='Imported exact pattern, Fraction LDL, kernel, interval optimum and entropy utility; unchanged prior bound bytes.',
                                              script_executed_by_this_reviewer=False)
report_path = PACKET / 'FINITE_CONTROLS.json'
assert sha(report_path) == 'e54166aa4a989ba5f4e0a47f96a133af3247da5932da266a4833f59361f1a13f'
author = json.loads(report_path.read_text())
rows = author['relative_controls']
assert len(rows) == author['tiny_head_unbounded_D_relative_checks'] == 576
assert author['implementation_sha256'] == sha(PACKET / 'check_exact_bulk.py')
assert author['credited_utility_sha256'] == sha(utility)
assert not author['retained_failed_controls']
assert all(Fraction(row['all_pattern_exact_margin']) > 0 for row in rows)
assert all(math.isfinite(float(row['relative_error_over_kappaT_plus_T2_overD']))
           and 0 <= float(row['relative_error_over_kappaT_plus_T2_overD']) < 100
           for row in rows)
coverage['FINITE_CONTROLS.json'] = bind(report_path, [[1, 150]],
                                      complete_raw_json_reread_claimed=False,
                                      additional_actual_inspection='Entire JSON parsed. All report keys/nonrelative values printed and inspected; every one of 576 relative rows programmatically inspected for profile, m, D multiplier, alpha, body tag, positive exact margin, and finite reported residual. This is not a raw 7619-line reread.')
before_script = PACKET / 'BEFORE_SINGULAR_CHECK_EXACT_BULK.py'
before_report = PACKET / 'BEFORE_SINGULAR_FINITE_CONTROLS.json'
old_report = json.loads(before_report.read_text())
assert old_report['implementation_sha256'] == sha(before_script)
assert not old_report['retained_failed_controls']
assert all(old_report[key] == author[key] for key in old_report
           if key != 'implementation_sha256')
coverage['BEFORE_SINGULAR_CHECK_EXACT_BULK.py'] = bind(before_script, [],
                                                   inspection='Actual full structured diff versus the completely read final author script; only 11 lines adding the singular-hole controls differ. No second full raw read claimed.')
coverage['BEFORE_SINGULAR_FINITE_CONTROLS.json'] = bind(before_report, [],
                                                     inspection='Complete JSON parsed to verify successful original result, its script binding, and structural equality of every old report field other than implementation hash; no raw full-line reread claimed.')
coverage['inherited_EXACT_RECTANGULAR.md'] = bind(ROOT / 'research/appt-multilevel-counterexample/EXACT_RECTANGULAR.md', [[1, 80]],
                                               use='Only earlier stated sufficient n>=m^3-m-2 purity region and domain were checked for supplementary provenance. No new audit of its complete proof is asserted.')
review['author_supporting_file_review'] = {
    'verdict': 'PASS for the separately stated finite/supporting/documentary claims',
    'new_document_and_author_code_complete_lines': 256,
    'unchanged_credited_utility_complete_lines': 209,
    'author_script_executed_by_this_reviewer': False,
    'retained_before_singular_success': True,
    'reported_controls': {'integer_rank_ties': 4,
                          'interval_cone_and_integer_controls': 225,
                          'exact_finite_slot_pattern_checks': 102,
                          'relative_controls': 576,
                          'singular_hole_controls': 12,
                          'actual_alpha2_lower_band_states': 4,
                          'same_head_above_band_states': 4,
                          'unsafe_extensive_false_winner': 'explicitly rejected'},
    'relative_rows_structured_inspection': {
        'm': sorted({row['m'] for row in rows}),
        'D_over_m3_decimal_exponents': sorted({row['D_power'] for row in rows}),
        'orders': sorted({row['alpha'] for row in rows}),
        'body_tags': sorted({row['body'] for row in rows}),
        'all_reported_exact_margins_positive': True,
        'all_reported_scaled_residuals_finite_and_below_100': True,
        'max_reported_scaled_residual': max(float(row['relative_error_over_kappaT_plus_T2_overD'])
                                          for row in rows)},
    'reason': 'Rank kinks, exact versus continuous maxima, actual all-pattern finite matrix margins, trace-subtracted endpoint/interior spectra, arbitrarily tiny heads, extreme D, singular zero eigenvalues, finite O(m) profitable lower states and rejected false winners are separately described. Counts are finite controls, not full-domain certificates. Unchanged imported utility is bound explicitly. No author implementation was rerun or represented as independent testing.'
}
review['independent_primary_context_screen'] = {
    'purpose': 'Check supporting provenance scope, not priority or a complete primary-paper proof audit.',
    'sources': [
        {'url': 'https://arxiv.org/abs/2609.18568',
         'actual_context_read': 'Metadata, abstract and submission history, rendered lines 8-29.',
         'verified': 'v1 16 September 2026; outer spectral-polytope bounds and exact qubit entropy/purity scope as disclosed.'},
        {'url': 'https://arxiv.org/abs/2608.03390v2',
         'actual_context_read': 'Metadata, abstract and submission history, rendered lines 8-30.',
         'verified': 'v2 18 September 2026; numerical eventual entropy coincidence and inscribed-polytope bounds.'},
        {'url': 'https://arxiv.org/html/2608.03390v2#S6.SS2',
         'actual_context_read': 'Targeted statement rendered 881-902 and numerical concluding remarks 983-995. Additional returned context was not represented as a complete section or 48-page proof audit.',
         'verified': 'Section 6.2 is an inscribed-polytope von Neumann calculation with numerical actual-set observations; it does not state this full-positive-order growing-m minimal eventual actual-set O(m) onset theorem.'}
    ],
    'historical_novelty_or_no_prior_solution_certificate': False
}
(HERE / 'REVIEW.json').write_text(json.dumps(review, indent=2) + '\n', encoding='utf-8')

md = (HERE / 'REVIEW_INITIAL.md').read_text()
md = md.replace('Verdict: **PASS for the complete initial E0-E4 mathematical statements.**',
                'Verdict: **PASS for the complete written statements E0-E4**, including the final status-only source binding.')
md = md.replace('Their immutable INITIAL copies have those exact hashes. No mathematical\n'
                'defect or manuscript mathematical revision was found. A second complete\n'
                'final reread is not claimed. Any later change requires a separate delta binding.',
                'Their immutable INITIAL copies have those exact hashes. No mathematical\n'
                'defect or manuscript mathematical revision was found. Final PAPER.md changes\n'
                'only status at lines 3 and 377; SHA256 is\n'
                '`02143109991a9f6fba342d9f51d672b32e14fbec70a0b3c81bf24714d09ee21c`.\n'
                'Reversing those two byte changes restores the exact fully read initial hash.\n'
                'Final context 1-6 and 371-377 was read; a second complete final-paper\n'
                'reread is not claimed. Final THEOREM_MAP.md was fully read at 1-18; its only changes\n'
                'are status at 3 and 5, with final SHA256\n'
                '`488edad996b1aca123898ef3711cf2c6e849344beec7d884e1f3dee0ec19b68f`.\n'
                'Its inverse byte delta also restores the initial hash and all E0-E4 rows\n'
                'are unchanged.')
md = md.replace('Author supporting files have not yet been provided/read at this initial\n'
                'mathematics verdict. Their inspection will be reported separately.\n', '''Supplementary sources were read separately: README.md complete 1-38,
LITERATURE.md complete 1-42, and author check_exact_bulk.py complete 1-176.
The imported credited cubic utility was read complete 1-209 and matches
its prior SHA256 exactly. Neither author script was rerun by this reviewer.
The author report was read raw at 1-150 and parsed entirely: every key and
nonrelative value was inspected, and all 576 relative rows were examined
programmatically for profiles, dimensions, orders, body tags, exact margins
and reported errors. A raw 7619-line reread is not claimed.

Author finite evidence separately includes four integer ties, 225 interval
controls, 102 exact finite slot-pattern tests, 576 relative entropy tests,
12 actual singular-hole tests, four actual alpha2 O(m) profitable lower
states and four losing same-head above-band states. It explicitly rejects
an uncanceled extensive approximation that produces a false winner. The
earlier successful nonsingular script/report remain preserved; the actual
11-line script addition and exact equality of every old report field were
checked. No failed result was concealed. These remain finite controls,
not the proof of the full eventual mathematical quantifiers.

Supplementary provenance statements agree with the current primary
[Tran metadata and abstract](https://arxiv.org/abs/2609.18568) and the
bounded [AAW Section 6.2 statement and numerical notes](https://arxiv.org/html/2608.03390v2#S6.SS2).
The reads covered their disclosed outer/qubit and inscribed-polytope scopes.
No full external paper audit, historical priority claim, or complete
literature certification is asserted. The earlier sufficient purity region
was checked only in EXACT_RECTANGULAR.md 1-80; its audit was not expanded.

''')
(HERE / 'REVIEW.md').write_text(md, encoding='utf-8')
print(json.dumps({'verdict': review['verdict'],
                  'review_json': str(HERE / 'REVIEW.json'),
                  'review_md': str(HERE / 'REVIEW.md'),
                  'review_json_lines': len((HERE / 'REVIEW.json').read_text().splitlines()),
                  'review_md_lines': len((HERE / 'REVIEW.md').read_text().splitlines()),
                  'json_sha256': sha(HERE / 'REVIEW.json'),
                  'md_sha256': sha(HERE / 'REVIEW.md')}, indent=2))
