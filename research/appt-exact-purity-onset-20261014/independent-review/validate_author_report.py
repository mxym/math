"""Parse every author-control row; do not rerun author tests or claim line reading."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json

here = Path(__file__).resolve().parent
report_path = here / 'AUTHOR_INITIAL_author_checks.json'
report = json.loads(report_path.read_text(encoding='utf-8'))
assert report['status'] == 'PASS_AUTHOR_FINITE_CONTROLS'
files = {
    'PAPER.md': here / 'SNAPSHOT_PAPER.md',
    'THEOREM_MAP.md': here / 'SNAPSHOT_THEOREM_MAP.md',
    'check_onset.py': here / 'AUTHOR_INITIAL_check_onset.py',
}
for name, path in files.items():
    assert report['files'][name]['sha256'] == hashlib.sha256(path.read_bytes()).hexdigest()
    assert report['files'][name]['lines'] == len(path.read_text(encoding='utf-8').splitlines())
for row in report['actual_single_head_lower']:
    assert Fraction(row['purity_minus_bulk']) > 0
    assert Fraction(row['integer_trace_loss']) >= 0
for row in report['same_family_above_threshold_controls']:
    assert Fraction(row['purity_minus_bulk']) < 0
    assert Fraction(row['integer_trace_loss']) >= 0
for row in report['parity_controls']:
    assert Fraction(row['fraction_B']) in [Fraction(1, 4), Fraction(3, 4)]
    assert row['body_formula_exact'] is True
for row in report['all_finite_head_slot_patterns']:
    assert Fraction(row['rank_one_slack']) >= 0
for row in report['tiny_tail_relative_controls']:
    assert Fraction(row['profit_penalty_per_tau']) > Fraction(1, 4)
assert Fraction(report['false_all_m_extension']['pole']) > Fraction(report['false_all_m_extension']['bulk'])
for row in report['small_family_results_retained']:
    # Keep these signs as data; neither asserts the eventual theorem for small m.
    Fraction(row['actual_profit'])
counts = {name: len(report[name]) for name in [
    'symbolic_groups', 'actual_single_head_lower', 'same_family_above_threshold_controls',
    'parity_controls', 'all_finite_head_slot_patterns', 'tiny_tail_relative_controls',
    'small_family_results_retained']}
output = {'status': 'PASS_AUTHOR_REPORT_STRUCTURAL_VALIDATION',
          'scope': 'complete JSON parsed and every result row structurally checked; no author script rerun; no claim to sequential reading of 2429 lines',
          'author_report_sha256': hashlib.sha256(report_path.read_bytes()).hexdigest(),
          'counts': counts,
          'initial_source_hashes_match': True,
          'false_extension_and_small_family_results_preserved': True}
destination = here / 'AUTHOR_REPORT_STRUCTURAL_VALIDATION.json'
destination.write_text(json.dumps(output, indent=2) + '\n', encoding='utf-8')
print(json.dumps(output))
