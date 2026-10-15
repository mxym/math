"""Source-bound X report metadata; no mathematical/author code execution."""
from pathlib import Path
import datetime as dt
import hashlib
import json
import platform

HERE = Path(__file__).resolve().parent
V1 = HERE/'owner-snapshot/all-dimension-positive-entropy-20261015'
V2 = HERE/'owner-v2-snapshot/all-dimension-positive-entropy-20261015-author-v2'
GOOD = HERE/'runs/20261015T135326.461037Z'
BAD = HERE/'runs/20261015T135229.946566Z'

def digest(p):
    b = p.read_bytes()
    return {'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}

def dump(name, value):
    p = HERE/name
    assert not p.exists(), 'Preserve prior metadata versions and executions.'
    p.write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n')

def main():
    now = dt.datetime.now(dt.timezone.utc).isoformat()
    assert json.loads((HERE/'VERSION_VERIFICATION.json').read_text())['status'] == 'PASS'
    good = json.loads((GOOD/'RESULT.json').read_text())
    bad = json.loads((BAD/'RESULT.json').read_text())
    assert good['status'] == 'PASS' and bad['status'] == 'FAIL'
    assert [r['name'] for r in bad['jobs'] if not r['checked']] == ['uniform_scalars']
    positive = json.loads((GOOD/'symbolic_and_qubit.stdout').read_text())
    scalars = json.loads((GOOD/'uniform_scalars.stdout').read_text())
    messages = {
        'v1_derivative_sign_at_theta_zero': 'the omitted theta factor vanishes at theta=0.',
        'omit_hole_floor': 'a bulk-only profile misses an actual hole deficit at tiny order.',
        'replace_finite_m_bulk': 'the growing-m coefficient is not the exact fixed-m tiny-order coefficient.',
        'replace_sum_by_max': 'the balanced first-order coefficient needs the additive head and surplus.',
        'omit_surplus': 'the balanced first-order coefficient needs the additive head and surplus.',
        'continuous_rank_is_exact': 'physical integer ranks do not attain every continuous optimum exactly.',
        'operator_convexity_substitute': 'scalar convex x^3 is not operator convex; its trace convexity is sufficient.',
        'extend_C_outside_domain': 'enlarging the C interval can violate the original qubit APPT criterion.'}
    inspected = []
    for run in (BAD, GOOD):
        for name, message in messages.items():
            text = (run/(name+'.stderr')).read_text()
            assert 'AssertionError: False: '+message in text
            assert 'wrong(args.name)' in text
            inspected.append({'run': run.relative_to(HERE).as_posix(), 'name': name,
                              'error': 'AssertionError: False: '+message,
                              'stderr': digest(run/(name+'.stderr')), 'stdout': digest(run/(name+'.stdout'))})
    dump('TRACEBACK_INSPECTION.json', {'status': 'PASS', 'actual_expected_failures': len(inspected),
         'intended_false_variant_messages_verified': inspected,
         'unexpected_first_positive_job_failure_is_separate': True})
    primary = {'kind': 'Bounded official external statement/context read, not a whole-paper proof audit or priority certificate',
               'utc': now, 'sources': [
                  {'url': 'https://arxiv.org/html/2409.14347v1',
                   'scope': 'Theorems 7, 9, 10 complete displayed statements and immediate context, Section III opening qubit iff criterion; surrounding definitions/compact-convex context visible in retrieved excerpt. Appendix proofs and complete remaining paper not reconstructed.'},
                  {'url': 'https://arxiv.org/abs/2409.14347', 'scope': 'Official title/authors, abstract, v1 submission/version, journal reference and DOI record.'},
                  {'url': 'https://journals.aps.org/pra/abstract/10.1103/7pnp-qgrq',
                   'scope': 'Official publication title/authors, abstract, Phys Rev A112 022409 and publication date. Authenticated journal full text not accessed.'}],
               'private_raw_retrieval': {'path': 'private-primary-evidence/official-retrieval.json',
                                        **digest(HERE/'private-primary-evidence/official-retrieval.json')},
               'redistribution': 'Private tool-result excerpt retained; excluded from automatic public copying. Public-safe URL/hash/scope ledger only.',
               'external_theorem_assumed_as_ordinary_input': True,
               'own_new_general_search_or_full_external_absence_certificate': False,
               'other_author_PRIMARY_SCOPE_reads_not_claimed_as_reviewers_fresh_reads': True}
    dump('PRIMARY_READ_LEDGER.json', primary)
    credited = json.loads((V2/'CREDITED_INPUTS.json').read_text())
    capture = json.loads((HERE/'INPUT_CAPTURE_CHECK.json').read_text())
    scientific = []
    reviews = []
    for name, row in credited['files'].items():
        if name.endswith('.md') and 'REVIEW' not in name:
            mode = 'Complete scientific text from immediately completed S5 read reused after byte-for-byte equality verification' if name in capture['reused_same_bytes'] else 'Entire scientific manuscript read in this X review'
            scientific.append({'path': name, **row, 'actual_read_scope': mode,
                               'purpose': 'Dependency hypotheses/proof use and local range comparison; not re-certification of all predecessor scopes.'})
        else:
            reviews.append({'path': name, **row,
                            'actual_read_scope': 'Complete all-order REVIEW.md; for review JSONs, relevant source/theorem/decision/correction/read-range/limit fields inspected. Not a claimed full fresh read of every JSON hash inventory.'})
    assert len(scientific) == 13 and len(reviews) == 7
    dump('READ_LEDGER.json', {'utc': now, 'full_v1_paper_lines': 514,
         'final_read_mode': 'Full v1 plus full single v2 delta/context, exact whole reverse-patch restoration and byte identity of all other original inputs. Not a second complete 518-line reread.',
         'full_current_map_read': True, 'scientific': scientific, 'review_records': reviews,
         'full_scientific_sources': 13, 'reused_whole_scientific_reads': 8, 'new_whole_scientific_reads': 5,
         'author_helpers': 'Current checks.py and endpoint_derivative_control.py plus stored results read, hash-verified and not executed/imported. Capture/freeze script bytes verified, not claimed wholly scientifically audited or executed.',
         'external': 'See PRIMARY_READ_LEDGER.json; external theorem accepted with explicit statement/context limits.',
         'aggregate_output_truncation_recovered': 'Oversized combined report outputs truncated; focused separate scientific and relevant review-scope reads recovered needed content. No full read of every large supporting JSON is claimed.'})
    failure = json.loads((HERE/'FIRST_REVIEWER_CONTROL_FAILURE.json').read_text())
    dump('FINDINGS.json', {'utc': now,
         'source_findings': [{'id': 'F1', 'severity': 'nonblocking endpoint derivative wording',
              'original_paper': digest(V1/'PAPER.md'), 'status': 'RESOLVED_IN_V2',
              'witness': {'alpha': 2, 'kappa': 1, 'theta': 0, 'actual_derivative': 0, 'old_proxy': 1},
              'resolution': 'Write the full nonnegative derivative including theta, and theta=0/1 zero endpoints. Required monotonicity and all theorem targets were already correct; no quantifier changed.',
              'author_delta': digest(V2/'AUTHOR_V1_TO_V2.diff'), 'final_paper': digest(V2/'PAPER.md')}],
         'unresolved_mathematical_findings': [],
         'reviewer_control_failures': [{'id': 'C1', 'status': 'RESOLVED_WITH_VALID_DERIVED_CONTROL_BOUND',
              'original_run': BAD.relative_to(HERE).as_posix(), 'diagnosis': digest(HERE/'FIRST_REVIEWER_CONTROL_FAILURE.json'),
              'm': failure['m'], 'D': failure['D'], 'alpha': failure['alpha'],
              'actual_value': failure['pole_times_D_over_alpha'], 'wrong_checker_constant': 10,
              'resolution': failure['derivation'], 'source_math_changed_for_this_failure': False}],
         'reproduced_same_control_failure': True, 'distinct_expected_false_variants': 8,
         'actual_expected_negative_children_across_two_runs': 16,
         'old_runs_versions_utc_and_prior_reports_preserved': True})
    scope = 'One total-dimension threshold: uniformly over every integer2<=m<=n with D=mn->infinity and every extended real0<=alpha<=infinity, actual complex all-global-unitary APPT entropy deficit divided by the specified positive profile tends to one.'
    report = {'status': 'PASS', 'decision': 'PASS', 'utc': now,
         'kind': 'Complete independent internal AI-agent ordinary mathematical read of final v2; not Lean/external human/priority/major count',
         'scope': scope, 'source_base_of_credited_inputs': credited['source_commit'],
         'initial_source': {'PAPER.md': digest(V1/'PAPER.md'), 'manifest': digest(V1/'AUTHOR_V1_MANIFEST.json'), 'owner_zip': digest(HERE/'owner.zip')},
         'final_source': {'PAPER.md': digest(V2/'PAPER.md'), 'THEOREM_MAP.md': digest(V2/'THEOREM_MAP.md'),
                          'manifest': digest(V2/'AUTHOR_V2_MANIFEST.json'), 'owner_zip': digest(HERE/'owner-v2.zip')},
         'final_mathematical_read': 'Complete initial514 lines plus complete single final delta/context and byte-exact inverse patch; not second complete final518-line reread',
         'decisions': {'X1': 'PASS: uniform relative small-width bulk kernel for every0<alpha<=sqrt(m), with correct signs, removable1 and alpha factor at0',
                       'X2': 'PASS: joint analytic g/alpha, positive fixed-m coefficient, bounded theta Hessian and legitimate nearest integer O(alpha/D^2)',
                       'qubit_value': 'PASS as explicit corollary of external Song-Chen Theorem10/iff qubit criterion, complete three-family algebra and trace-extreme principle; not a new classification',
                       'growing_m': 'PASS comparison to credited V2 with additive head/surplus and exact positive-increment logs; not first closure',
                       'fixed_m': 'PASS all positive orders uniformly at each fixedm>=3; tiny-order relative lattice estimate and bounded/unbounded higher-order split',
                       'X': 'PASS one total-D threshold all dimensions and every extended order, including arbitrary oscillations and separately exact endpoints'},
         'independent_execution': {'first_run': {'path': BAD.relative_to(HERE).as_posix(), 'RESULT.json': digest(BAD/'RESULT.json'), 'status': 'FAIL'},
              'second_run': {'path': GOOD.relative_to(HERE).as_posix(), 'RESULT.json': digest(GOOD/'RESULT.json'), 'status': 'PASS'},
              'reviewer_helper_current': digest(HERE/'independent_checks.py'), 'harness': digest(HERE/'run_independent_checks.py'),
              'diagnosis': digest(HERE/'diagnose_first_failure.py'), 'positive_jobs_final': 2,
              'counts': {'symbolic_assertions': positive['symbolic_assertions'], 'exact_qubit_cases': positive['exact_qubit_conditions_cases'],
                         **{k: len(v) for k,v in scalars.items() if isinstance(v, list)},
                         'distinct_false_variants': 8, 'actual_expected_negative_children': 16, 'distinct_unexpected_failure_conditions': 1},
              'runtime': {'Python': platform.python_version(), 'SymPy': positive['sympy_version'], 'mpmath': scalars['mpmath_version'], 'decimal_precision': scalars['decimal_precision']},
              'no_author_execution_import_or_AST_reuse': True,
              'finite_checks_are_not_universal_proof': True},
         'author_execution_read_only': ['v1 eight-group132659', 'v2 eight-group134507.331566', 'v2 six-assertion endpoint134507.331718'],
         'findings': {'path': 'FINDINGS.json', **digest(HERE/'FINDINGS.json')},
         'read_ledger': {'path': 'READ_LEDGER.json', **digest(HERE/'READ_LEDGER.json')},
         'primary_read_ledger': {'path': 'PRIMARY_READ_LEDGER.json', **digest(HERE/'PRIMARY_READ_LEDGER.json')},
         'full_report': {'path': 'REVIEW.md', **digest(HERE/'REVIEW.md')},
         'not_covered': ['Future publication/source-status/index/transport layouts', 'Entire external Song-Chen proof or whole current primary papers',
              'Effective total-D thresholds', 'Every finite optimizer/equality spectrum for generalm>=3',
              'Complete changing-order spectral rigidity', 'New all-order growing-m/fixed-m range closure', 'APPT=ASEP', 'Lean or audit expansion', 'Priority/human peer review/new major count'],
         'actions': 'Only new private reviewer directory written; no author/root/old review edit, Git mutation, publication or subagents.'}
    dump('REVIEW.json', report)
    files = [{'path': p.relative_to(HERE).as_posix(), **digest(p),
              'private_external_raw_excluded_from_automatic_public_copy': p.relative_to(HERE).as_posix().startswith('private-primary-evidence/')}
             for p in sorted(HERE.rglob('*')) if p.is_file() and p.name != 'REPORT_BINDINGS.json']
    dump('REPORT_BINDINGS.json', {'status': 'PASS', 'decision': 'PASS', 'utc': now,
         'scope': 'Exact completed private mathematical-review bytes, not future metadata/publication approval.',
         'exclusions': ['REPORT_BINDINGS.json itself to avoid recursion', 'Later-created files or future copied layout'],
         'private_external_redistribution_exclusions': ['private-primary-evidence/; keep privately and publish only URL/hash/scope ledger if needed'],
         'files': files})
    print(json.dumps({'status': 'PASS', 'decision': 'PASS', 'REVIEW.md': digest(HERE/'REVIEW.md'),
                     'REVIEW.json': digest(HERE/'REVIEW.json'), 'REPORT_BINDINGS.json': digest(HERE/'REPORT_BINDINGS.json')}, indent=2))

if __name__ == '__main__':
    main()
