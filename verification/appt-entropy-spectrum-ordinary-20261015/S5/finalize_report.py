"""Bind this completed ordinary review, excluding its own binding to avoid recursion."""
from pathlib import Path
import datetime as dt
import hashlib
import json

HERE = Path(__file__).resolve().parent
SRC = HERE / 'owner-snapshot/worktree/research/breadth-tcs-20261015/phase-5-sublinear-rigidity'
RUN = HERE / 'runs/20261015T133349.443900Z'

def digest(p):
    data = p.read_bytes()
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(name, value):
    dest = HERE/name
    assert not dest.exists(), 'Keep all earlier report metadata intact.'
    dest.write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n')

def main():
    now = dt.datetime.now(dt.timezone.utc).isoformat()
    source_map = json.loads((SRC/'SOURCE_INPUTS.json').read_text())
    verification = json.loads((HERE/'INPUT_VERIFICATION.json').read_text())
    assert verification['status'] == 'PASS'
    run = json.loads((RUN/'RESULT.json').read_text())
    assert run['status'] == 'PASS' and len(run['all_jobs']) == 8
    positives = [x for x in run['all_jobs'] if not x['negative_control']]
    negatives = [x for x in run['all_jobs'] if x['negative_control']]
    assert len(positives) == 2 and len(negatives) == 6
    assert all(x['returncode'] == 0 for x in positives)
    messages = {
        'branch_minimum': 'zero peak defect alone does not saturate the weighted sum',
        'omit_J': 'width and mean do not remove the positive J loss',
        'omit_mean_square': 'actual middle mean is not exactly one',
        'unweighted_W2': 'a negligible bulk weight does not require the full beta W2 law',
        'entropy_requires_moment': 'relative entropy tolerates h=o(chi), unlike moment excess',
        'log_coarse_error': 'o(optimum peak) error need not be small after logging a much smaller actual moment',
    }
    for row in negatives:
        assert row['returncode'] == 1
        stderr = (RUN/(row['name']+'.stderr')).read_text()
        assert 'AssertionError: False: '+messages[row['name']] in stderr
    ledger = {'utc': now, 'scope': 'Current phase-5 full ordinary read and dependency/range reading only',
              'paper_full_lines': 410, 'full_current_mathematical_and_map_read': True,
              'scientific_inputs': [{**row, 'reviewer_actual_scope': 'Entire captured scientific text read; used for current dependency assumptions and local range/collision comparison. This does not newly certify all older theorem scopes.'} for row in source_map['inputs']],
              'additional_complete_reads': ['PAPER.md', 'THEOREM_MAP.md', 'LOCAL_COVERAGE_MAP.md', 'README.md',
                    'SOURCE_INPUTS.json', 'AUTHOR_V1_MANIFEST.json', 'TARGET.json', 'PRIMARY_SCREEN.json',
                    'ATTEMPT_LEDGER.json', 'author_exact_controls.py', 'AUTHOR_EXACT_CONTROLS.json',
                    'freeze_author_scope.py', 'initialize_sublinear_rigidity.py'],
              'important_dependency_roles': {'G': 'Uniform all-aspect growing-sublinear optimized value and all-state physical estimates',
                   'L': 'Actual all-global-unitary finite peak/width coupling L7 and physical integer-rank SOS family',
                   'S': 'Exact inclusive actual middle definitions and nonnegative-spread notation',
                   'other_sources': 'Full scientific-text range/collision comparison, not automatic scope inheritance'},
              'phase4_dependencies': False, 'external_search_rerun': False,
              'external_author_screen_is_not_independent_priority_certificate': True}
    dump('READ_LEDGER.json', ledger)
    findings = {'utc': now, 'mathematical_source_findings': [], 'source_corrections_required': False,
                'unexpected_reviewer_execution_failures': [],
                'actual_expected_false_variant_failures': negatives,
                'expected_failure_tracebacks_individually_read_and_matched': True,
                'author_history_preserved': {'read_only': True, 'nonmathematical_failures': 2,
                     'source': 'owner-snapshot/worktree/research/breadth-tcs-20261015/phase-5-sublinear-rigidity/ATTEMPT_LEDGER.json'},
                'no_old_report_extended_or_overwritten': True}
    dump('FINDINGS.json', findings)
    scope = 'Every sequence of actual complex PSD trace-one all-global-unitary APPT matrices, integers 2<=m<=n, m->infinity, real alpha->infinity, alpha/m->0; all aspects and oscillations.'
    report = {'status': 'PASS', 'decision': 'PASS', 'utc': now,
              'reviewer_role': 'Different internal AI-agent ordinary full mathematical read; not external human review, Lean, priority or a major-problem count.',
              'scope': scope, 'input': {'PAPER.md': digest(SRC/'PAPER.md'), 'THEOREM_MAP.md': digest(SRC/'THEOREM_MAP.md'),
                    'AUTHOR_V1_MANIFEST.json': digest(SRC/'AUTHOR_V1_MANIFEST.json'), 'SOURCE_INPUTS.json': digest(SRC/'SOURCE_INPUTS.json'),
                    'owner.zip': digest(HERE/'owner.zip')},
              'source_base': source_map['root_capture_commit'],
              'decisions': {'A': {'status': 'PASS', 'claim': 'Sharp actual moment-EXCESS iff weighted SUM of capped actual peak and L/theta/J body defects vanishes.'},
                 'B': {'status': 'PASS', 'claim': 'Relative entropy DEFICIT iff analogous weighted sum with h/(1+chi_plus) vanishes; separate actual-peak-relative large-log proof.'},
                 'C': {'status': 'PASS', 'claim': 'On liminf wb>0 subsequences, db->0 iff full actual scaled empirical W2 convergence to equal atoms at -1,+1; capped weighted replacement on arbitrary paths.'},
                 'D': {'status': 'PASS', 'claim': 'Both weights bounded below and either nearoptimality imply alpha eta_m->0 and (m/alpha)(2-L)->infinity; necessary compatibility only.'}},
              'proof_gates': ['Original all-global-unitary quantum definition and exact positive pivot',
                    'Exact inclusive N=D-m^2+2, zero-width theta convention, actual h>=0',
                    'State-uniform centered-kernel identity at U+V scale',
                    'Controlled weighted variance overshoot before nonnegative loss extraction',
                    'Retained-bulk gamma->infinity and exact trace/Cauchy centering',
                    'Nonnegative full L/theta/J variance loss and exceptional second-moment integrability',
                    'Both W2 directions and capped weighted arbitrary-subsequence replacement',
                    'Bounded-log scalar compactification at vanishing moment increment',
                    'Large-log physical y1->3 necessity before state-relative logarithm',
                    'All oscillating path quantifiers and necessary actual peak/width margin',
                    'Actual all-unitary counterexamples with integer multiplicities and normalization'],
              'read_ledger': {'path': 'READ_LEDGER.json', **digest(HERE/'READ_LEDGER.json')},
              'findings': {'path': 'FINDINGS.json', **digest(HERE/'FINDINGS.json')},
              'full_report': {'path': 'REVIEW.md', **digest(HERE/'REVIEW.md')},
              'independent_execution': {'run': RUN.relative_to(HERE).as_posix(), 'RESULT.json': digest(RUN/'RESULT.json'),
                    'reviewer_helper': digest(HERE/'independent_checks.py'), 'reviewer_harness': digest(HERE/'run_independent_checks.py'),
                    'positive_jobs': 2, 'symbolic_identities': 4, 'exact_actual_state_cases': 32,
                    'real_order_cases': 9, 'actual_reduced_pole_separation_cases': 3, 'state_relative_log_cases': 12,
                    'expected_actual_AssertionError_children': 6, 'unexpected_failures': 0,
                    'no_author_import_execution_or_AST_reuse': True,
                    'runtime': {'Python': '3.10.12', 'SymPy': '1.9', 'mpmath': '1.2.1', 'mp_decimal_precision': 180},
                    'finite_diagnostics_do_not_prove_universal_claim': True},
              'author_controls': {'authored_by': 'Depth author agent', 'reported_finite_cases': 18,
                    'reviewer_read': True, 'reviewer_executed': False, 'original_utc': '2026-10-15T13:16:32.941162+00:00',
                    'source': digest(SRC/'author_exact_controls.py'), 'result': digest(SRC/'AUTHOR_EXACT_CONTROLS.json')},
              'not_covered': ['Future X all-dimension value synthesis', 'Any other new manuscript', 'Future metadata/index/layout/transport',
                    'Fixed-m synthesis', 'Other positive finite/zero-order unrestricted-aspect spectral ranges',
                    'Positive finite or infinite limiting alpha/m scope', 'Exact finite optimizers or eigenbasis rigidity',
                    'APPT=ASEP', 'All-order value novelty', 'Lean/audit expansion', 'External peer review or priority'],
              'mutations': 'Only new reviewer-owned directory; no author/root/old-report edits, Git mutation, push, publication or subagents.'}
    dump('REVIEW.json', report)
    files = []
    for path in sorted(HERE.rglob('*')):
        if path.is_file() and path.name != 'REPORT_BINDINGS.json':
            files.append({'path': path.relative_to(HERE).as_posix(), **digest(path)})
    dump('REPORT_BINDINGS.json', {'status': 'PASS', 'decision': 'PASS', 'utc': now,
        'role': 'Exact bytes of completed private phase-5 review and immutable inputs; not publication/status/layout approval.',
        'exclusions': ['REPORT_BINDINGS.json itself, to avoid self-reference', 'Any files created after this manifest', 'Future copied publication layout/transport'],
        'files': files})
    print(json.dumps({'status': 'PASS', 'decision': 'PASS',
         'REVIEW.md': digest(HERE/'REVIEW.md'), 'REVIEW.json': digest(HERE/'REVIEW.json'),
         'REPORT_BINDINGS.json': digest(HERE/'REPORT_BINDINGS.json')}, indent=2))

if __name__ == '__main__':
    main()
