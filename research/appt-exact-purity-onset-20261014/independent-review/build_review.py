"""Bind the independent review to the initial full text and actual final changes."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent


def sha(data):
    return hashlib.sha256(data).hexdigest()


def info(path):
    data = path.read_bytes()
    return {'sha256': sha(data), 'bytes': len(data),
            'lines': len(data.decode('utf-8').splitlines())}


initial_names = {'PAPER.md': 'SNAPSHOT_PAPER.md',
                 'THEOREM_MAP.md': 'SNAPSHOT_THEOREM_MAP.md',
                 'README.md': 'AUTHOR_INITIAL_README.md'}
expected_initial = {
    'PAPER.md': 'ad4059967adde63692ff5507a72caa3777fd97e29779aa128c4ef43da594085d',
    'THEOREM_MAP.md': '2324fadc329231142c6ddf7539ba27961aa4eb4abcbb49b4cd068ca37d007a5f',
    'README.md': '899f42f8811d6157e75ac07c1542e208aa9dac937f0819d67b2fc169f5dac5f8'}
expected_changed = {'PAPER.md': [3, 360, 361], 'THEOREM_MAP.md': [3, 37],
                    'README.md': [3, 15, 16]}
deltas_path = PACKET / 'FINAL_STATUS_DELTAS.json'
deltas = json.loads(deltas_path.read_text(encoding='utf-8'))
source_binding = {}
for name, snapshot in initial_names.items():
    initial = (HERE / snapshot).read_bytes()
    final = (PACKET / name).read_bytes()
    delta = deltas[name]
    assert sha(initial) == expected_initial[name] == delta['initial_sha256']
    assert sha(final) == delta['final_sha256']
    initial_lines = initial.decode('utf-8').splitlines()
    final_lines = final.decode('utf-8').splitlines()
    assert len(initial_lines) == len(final_lines)
    changed = [i + 1 for i, pair in enumerate(zip(initial_lines, final_lines)) if pair[0] != pair[1]]
    assert changed == expected_changed[name]
    restored = final.decode('utf-8')
    for change in reversed(delta['changes']):
        assert restored.count(change['new']) == 1
        restored = restored.replace(change['new'], change['old'], 1)
    assert restored.encode('utf-8') == initial
    assert (PACKET / ('INITIAL_' + name)).read_bytes() == initial
    (HERE / ('FINAL_' + name)).write_bytes(final)
    diff_name = 'FINAL_STATUS_' + name + '.diff'
    (HERE / diff_name).write_bytes((PACKET / diff_name).read_bytes())
    source_binding[name] = {'initial': info(HERE / snapshot), 'final': info(PACKET / name),
                            'full_initial_read_ranges': [[1, len(initial_lines)]],
                            'actual_final_changed_lines_read': changed,
                            'inverse_status_reconstruction_sha256': sha(restored.encode('utf-8')),
                            'mathematical_changes': 0,
                            'no_second_complete_final_read_claimed': True,
                            'initial_snapshot': snapshot,
                            'final_snapshot': 'FINAL_' + name,
                            'diff': {'path': diff_name, **info(HERE / diff_name)}}
(HERE / 'FINAL_STATUS_DELTAS.json').write_bytes(deltas_path.read_bytes())
support = {}
for name in ['LITERATURE.md', 'check_onset.py', 'author_checks.json']:
    initial_path = HERE / ('AUTHOR_INITIAL_' + name)
    assert initial_path.read_bytes() == (PACKET / name).read_bytes()
    support[name] = info(initial_path)
    support[name]['reading_method'] = (
        'entire JSON parsed and every result row structurally checked; not sequential line-by-line reading'
        if name == 'author_checks.json' else 'complete sequential reading')
    if name != 'author_checks.json':
        support[name]['read_ranges'] = [[1, support[name]['lines']]]
dependencies = {}
for name, location, expected in [
    ('C0-C4', 'DEPENDENCY_C0_C4_PAPER.md', 'a2e940d320950c258d2aed13bb5afa81ea3bc41efa74acc09dca703d0a817449'),
    ('E0-E4', 'DEPENDENCY_E0_E4_PAPER.md', '02143109991a9f6fba342d9f51d672b32e14fbec70a0b3c81bf24714d09ee21c')]:
    metadata = info(HERE / location)
    assert metadata['sha256'] == expected
    dependencies[name] = {**metadata, 'read_ranges': [[1, metadata['lines']]],
                          'snapshot': location,
                          'scope': 'complete ordinary manuscript read to verify correct invocation; inherits its credited earlier ordinary inputs; no Lean/audit rerun'}
run_paths = sorted(HERE.glob('RUN_*.json'))
assert len(run_paths) == 1
run_path = run_paths[0]
run = json.loads(run_path.read_text(encoding='utf-8'))
assert run['status'] == 'PASS_INDEPENDENT_FINITE_CONTROLS'
assert run['script_sha256'] == sha((HERE / 'check_independent.py').read_bytes())
assert run['counts'] == {'symbolic': 19, 'full_slots': 9, 'boundary_PSD': 76,
                         'exhaustive_q_rank': 72, 'actual_integer_single': 22,
                         'rejected_false_extension': 2, 'compact_scalar_maximum': 5}
for event in run['events']:
    assert event['kind'] in run['counts']
author_validation_path = HERE / 'AUTHOR_REPORT_STRUCTURAL_VALIDATION.json'
author_validation = json.loads(author_validation_path.read_text(encoding='utf-8'))
assert author_validation['status'] == 'PASS_AUTHOR_REPORT_STRUCTURAL_VALIDATION'
author_report = json.loads((HERE / 'AUTHOR_INITIAL_author_checks.json').read_text(encoding='utf-8'))

findings = [
    {'paper_lines': [52, 96], 'topic': 'exact signed comparison',
     'conclusion': 'PASS', 'reason': 'The clipped chord and real trace maximization yield the exact V identity, including kappa*T and the finite quadratic budget correction. The real q body is used only as an upper comparison.'},
    {'paper_lines': [98, 138], 'topic': 'full actual critical localization',
     'conclusion': 'PASS', 'reason': 'E0 coercivity bounds c for every potentially profitable state. Its relative error remains O(c/m), so arbitrarily small c>0 is excluded uniformly. C0 squeezes profit to zero and C4 then gives l1/c proximity to the full critical set. The empty branch is excluded by c>1/4. Sequential contradiction gives a single large-m bound over the whole band.'},
    {'paper_lines': [140, 181], 'topic': 'all physical tail mass charged',
     'conclusion': 'PASS', 'reason': 'Original all-unitary necessity gives each fully assigned witness PSD. Positive kappa makes aI-P positive definite. Its nonnegative resolvent walks retain every primary-edge walk plus exactly 2*tau/a^2 in the first remaining walk, including overlap and all growing slots. The implicit cost function is strictly increasing and has uniformly bounded derivative, yielding c-c0>=1.6*tau.'},
    {'paper_lines': [183, 200], 'topic': 'strict unrestricted head domination',
     'conclusion': 'PASS', 'reason': 'C4 first makes every other head at most eta. Exact subtraction then charges its squared gain by eta*tau while the protection budget costs at least 0.24*0.9*1.6*tau. Since eta+kappa<=0.02 eventually, V<=V0-tau/4 has a strict uniform margin. No additive error independent of tau appears.'},
    {'paper_lines': [202, 250], 'topic': 'scalar finite crossing and constant term',
     'conclusion': 'PASS', 'reason': 'The z parametrization solves the exact implicit cost equation. The [1,3] restriction follows from prior unrestricted localization. Uniform C2 rational expansion, the isolated nondegenerate maximizer at z=2, and the implicit function theorem give displacement 8/m and the constant 7/4. The rational lower displacement has the displayed positive exact remainder.'},
    {'paper_lines': [252, 280], 'topic': 'lattice locking and all larger n',
     'conclusion': 'PASS', 'reason': 'B_m has fractional part 1/4 or 3/4, so the integer lattice gap dominates the O(1/m) crossing remainder. Every c>0 profitable state in the entire critical band would have negative purity margin of order m^-8, stronger than the O(m^-11) integer q loss. The credited coarse theorem covers every larger n beyond the band.'},
    {'paper_lines': [282, 294], 'topic': 'unique rank and every equality matrix',
     'conclusion': 'PASS', 'reason': 'The scalar loss formula and one sign change restrict winning ranks to floor/ceil. For a half-integer optimum, ceil has strictly smaller loss due to its larger normalization denominator. The exact cube-vertex equality theorem gives all normalized projection matrices and excludes interior mixtures.'},
    {'paper_lines': [296, 320], 'topic': 'original all-global-unitary boundary sufficiency',
     'conclusion': 'PASS', 'reason': 'Endpoint counts make the adverse spectral rearrangement exactly the single-edge witness. Its aI-P is positive definite and kappa*1^T(aI-P)^-1*1=1 makes the witness positive semidefinite. Every edge is permutation-congruent, so every Schmidt vector and global unitary is covered, including zero Schmidt coordinates.'},
    {'paper_lines': [322, 343], 'topic': 'actual integer state below onset and minimality',
     'conclusion': 'PASS', 'reason': 'The proposed lower state uses its actual trace and integer rank nearest the real trace optimum. Its exact loss is O(m^-11), while its gain over even the continuous q body is of order m^-8 at N-1. Its endpoint counts are strictly sufficient eventually. A counterexample at N-1 and equality for every n>=N establish the minimal eventual onset.'},
    {'paper_lines': [345, 361], 'topic': 'scope and false small-m extension',
     'conclusion': 'PASS', 'reason': 'The m=3,n=8 pole is actual all-unitary APPT and beats the bulk, rejecting an all-small-m claim. The result is ordinary, eventual in m, without an effective M, additional entropy orders, ASEP, Lean theorem, new audit scope, or priority certification.'}
]

review = {
    'verdict': 'PASS_COMPLETE_INDEPENDENT_ORDINARY_REVIEW',
    'reviewer': '/root/ordinary_review_purity_onset',
    'utc_completed': datetime.now(timezone.utc).isoformat(),
    'target': 'Q0-Q3: original all-global-unitary APPT purity; exact minimal eventual onset ceil((m^2+5m+7)/4), all larger n, every equality matrix, and actual integer-rank lower at N-1',
    'review_kind': 'independent AI subagent ordinary mathematical review; not external human peer review or formal certification',
    'mathematical_issues': [], 'required_mathematical_changes': 0,
    'full_initial_mathematical_source_lines_read': 398,
    'support_lines_sequentially_read': 284,
    'dependency_ordinary_lines_read': 838,
    'actual_final_status_lines_read': 8,
    'source_binding': source_binding,
    'unchanged_support': support,
    'credited_dependency_binding': dependencies,
    'status_delta_manifest': info(HERE / 'FINAL_STATUS_DELTAS.json'),
    'findings': findings,
    'independent_controls': {
        'executions': 1, 'script': {'path': 'check_independent.py', **info(HERE / 'check_independent.py')},
        'raw_report': {'path': run_path.name, **info(run_path)},
        'status': run['status'], 'counts': run['counts'], 'versions': run['versions'],
        'high_precision_digits': 180,
        'scope': 'finite algebra and exact witness controls complement the complete written argument; no finite experiment is presented as a whole-domain proof',
        'author_code_imported_or_rerun': False,
        'failures_or_invalid_runs': [],
        'raw_failed_or_invalid_record_deletion': False},
    'author_controls': {
        'reading': 'complete structured JSON parse and every row structural validation; no claim to sequential reading of 2429 lines',
        'status': author_report['status'],
        'counts': author_validation['counts'],
        'report_binding': info(HERE / 'AUTHOR_INITIAL_author_checks.json'),
        'validation': {'path': author_validation_path.name, **info(author_validation_path)},
        'script_rerun_by_reviewer': False,
        'source_hashes_bind_initial_text': True,
        'small_m_positive_family_examples_retained_as_data': True},
    'scope_exclusions': ['no new Lean/Lake/kernel execution', 'no original audit-scope expansion',
                         'no independent full primary-literature or historical-priority certification',
                         'no effective M or all-small-m theorem', 'no ASEP or other entropy order',
                         'no audit of subsequent W0-W3 research', 'no git mutation or publication by reviewer']
}
(HERE / 'REVIEW.json').write_text(json.dumps(review, indent=2) + '\n', encoding='utf-8')

text = '''# Independent complete ordinary review of Q0-Q3

**PASS.** The full proposed mathematical proof and whole-target map were independently
read and checked. No mathematical gap or required mathematical correction was found.
This is an independent AI subagent ordinary review, not external human peer review,
Lean verification, or a new audit of the inherited formal declarations.

The reviewed theorem is the exact minimal EVENTUAL purity onset

    N_2(m)=ceil((m^2+5m+7)/4)

for every sufficiently large integer m, over the original complex density matrices
remaining PPT after EVERY global unitary. The review covers all larger n, every
optimizing projection matrix, its unique integer rank and parity-dependent purity,
and a genuine APPT integer-rank state beating the bulk at n=N_2(m)-1.
It does not provide an effective starting m or assert the formula for all small m.

## Actual source coverage and final-change binding

The initial `PAPER.md` was read in full, lines 1-361, SHA-256
`ad4059967adde63692ff5507a72caa3777fd97e29779aa128c4ef43da594085d`.
The initial `THEOREM_MAP.md` was read in full, lines 1-37, SHA-256
`2324fadc329231142c6ddf7539ba27961aa4eb4abcbb49b4cd068ca37d007a5f`.
Together these are 398 mathematical source/map lines.

The support README 1-36, literature note 1-41, and author script 1-207 were
also read completely: 284 support lines. The entire 2,429-line author JSON was
parsed and every result row structurally checked; sequential reading of all its
raw lines is NOT claimed. The author script was not imported or rerun.

The immutable cited ordinary C0-C4 paper 1-461 and E0-E4 paper 1-377 were
read completely to verify their correct invocation: 838 dependency lines.
Their credited earlier mathematical inputs remain credited; no earlier Lean
certificate or original broader audit has been rerun or expanded.

Only final review-status text changed. Actual final changed lines were read:
PAPER 3,360,361; map 3,37; README 3,15,16. Exact reverse replacements reconstruct
the already fully read initial bytes and original hashes for all three files.
There are ZERO mathematical changes, and no second complete final-text reading
is claimed. The final hashes are:

- PAPER: `41edf08c0ed2d8cd9d6e15f9eeeba0c4814cab2c9a0e81565af7eab39b090d6e`.
- Map: `23ff66d7abdce792e3575d6f0d624a79cb9f98392a7e689d82fdf803015db1e0`.
- README: `541f85f47fe609b03a395d6c88090770f2fde2aa38ad581a270da3d503868961`.

Snapshots, literal status differences, exact reverse checks, supporting hashes,
and per-source line scopes are recorded in `REVIEW.json`.

## Mathematical checks on the complete physical domain

The exact clipped chord yields the signed purity comparison with both the
kappa*T term and finite quadratic budget correction retained. Continuous rank
is used as a comparison bound, with actual integer states handled separately.

For EVERY potentially profitable actual spectrum, E0 coercivity bounds the
budget c. The relative O(c/m) estimate excludes even arbitrarily tiny nonzero
budgets near the empty profile. C0 then squeezes its correction to zero, and
C4's full l1/c compactness localizes the ENTIRE actual list to the nonempty
critical branch. Sequential contradiction makes this uniform throughout the
whole relevant dimension band; no finite-head ansatz enters this step.

Every original anomaly is filled into an actual Schmidt-witness slot. The
nonnegative resolvent walk bound keeps every walk from the main edge and the
first walk from ALL remaining mass, including overlapping slots and a growing
tail. The resulting exact cost implies c-c0>=1.6*tau. Subtracting actual profits
then yields V<=V0-tau/4 with a strict uniform margin and no additive error
independent of tau. Only after this unrestricted argument is the upper scalar.

The exact one-head parametrization solves the finite implicit cost equation.
Its uniform C2 expansion on [1,3] gives the displacement 8/m and constant term
7/4. This compact interval is justified by the prior whole-spectrum localization.
The rational lower displacement 2+8/m has the displayed positive exact remainder.

Integer locking is valid because B_m has fractional part 1/4 or 3/4. That fixed
margin dominates the O(1/m) scalar remainder. The strict upper purity margin
has order m^-8, versus the exact q integer-rounding loss of order m^-11.
The coarse E0 theorem covers every larger n beyond the critical band.
The exact interval equality theorem and scalar integer optimization give every
optimizing matrix and the strictly unique ceiling rank, including half integers.

The lower single-edge witness is genuinely boundary PSD, with aI-P positive
definite and exact rank-one product equal to one. Spectral rearrangement and
edge permutation congruence cover every Schmidt vector and global unitary.
Its actual trace is optimized and then rounded to an INTEGER rank; the exact
loss remains order m^-11 while its gain at N-1 is order m^-8. The endpoint
counts are sufficient eventually. Thus the lower proves minimality for ALL
larger n, rather than just a crossing within the trial family.

The actual m=3,n=8 pole beats the bulk and correctly rejects an indiscriminate
all-small-m extension. Literature disclosures are bounded and partial; this
review provides no independent historical-priority or exhaustive primary-paper
audit. Subsequent W0-W3 research is outside this review.

## Independent finite controls and preserved evidence

`check_independent.py` was written independently and executed once, with every
control passing. It imports or reruns no author verification code. It includes:

- 19 exact symbolic identities, expansions, rank-loss and trace-loss formulas.
- 9 exact Fraction witnesses filling ALL R+K slots and retaining the entire tail.
- 76 exact single-edge boundary PSD matrices, of rank m-1; strict PD fails there.
- 72 exhaustive integer q-rank problems, with strictly unique ceiling winners.
- 22 genuine all-unitary single-head states with actual integer ranks, on both
  sides of the proposed eventual threshold.
- 5 compact scalar maxima checked by exact Sturm root counts and 180-digit
  evaluation, separate from the whole-domain applicability proof.
- 2 rejected false extensions: all-small-m universality and dropping the 7/4
  constant from the onset. The raw evidence is retained.

The raw execution report is `RUN_20261014T085613.824211Z.json`, with SymPy 1.9
and mpmath 1.2.1. There were no failed or invalid independent executions, and
no records were deleted. Author controls were parsed separately: 8 symbolic
groups, 26 lower and 26 same-family upper cases, 26 parity cases, 126 finite
patterns, and 60 tiny-tail cases. The author's m=8 and m=16 positive small-m
family profits remain as data rather than being relabeled as theorem violations.

Finite controls complement the complete ordinary proof. Neither author nor
reviewer finite experiments are described as whole-domain certificates.
'''
(HERE / 'REVIEW.md').write_text(text, encoding='utf-8')
print(json.dumps({'verdict': review['verdict'], 'initial_math_lines': 398,
                  'mathematical_changes': 0, 'review_json': info(HERE / 'REVIEW.json'),
                  'review_md': info(HERE / 'REVIEW.md')}))
