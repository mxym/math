#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent
ROOT = Path('/home/mxym/math-appt-multiscale-20261013')

def binding(path, ranges, **extra):
    data = path.read_bytes()
    return {"path": str(path), "sha256": hashlib.sha256(data).hexdigest(),
            "total_lines": len(data.decode('utf-8').splitlines()),
            "actual_read_ranges": ranges, **extra}

expected_paper = 'ae5f04557e63a4af6f1d4329448f81d7ca30ea41099770b88a748bba68ce4927'
expected_map = '5e36d29cefa57f69dddccff7337db73bb633805983565ab7eb7b273b0cabb6c3'
for name, expected in [('INITIAL_PAPER.md', expected_paper),
                       ('INITIAL_THEOREM_MAP.md', expected_map)]:
    assert hashlib.sha256((PACKET / name).read_bytes()).hexdigest() == expected

coverage = {
    'INITIAL_PAPER.md': binding(PACKET / 'INITIAL_PAPER.md', [[1, 377]]),
    'INITIAL_THEOREM_MAP.md': binding(PACKET / 'INITIAL_THEOREM_MAP.md', [[1, 18]]),
    'initial_current_PAPER.md': binding(PACKET / 'PAPER.md', [[1, 377]],
                                      expected_initial_sha256=expected_paper),
    'initial_current_THEOREM_MAP.md': binding(PACKET / 'THEOREM_MAP.md', [[1, 18]],
                                            expected_initial_sha256=expected_map),
    'inherited_cubic_PAPER.md': binding(ROOT / 'research/appt-cubic-entropy-20261014/PAPER.md', [[1, 461]],
                                      use='Exact original physical anomaly, graph, rank-one, and all-unitary sufficient construction inputs; no expansion of prior formal audit.'),
    'inherited_cubic_REVIEW.md': binding(ROOT / 'research/appt-cubic-entropy-20261014/REVIEW.md',
                                       [[1, len((ROOT / 'research/appt-cubic-entropy-20261014/REVIEW.md').read_text().splitlines())]]),
    'inherited_cubic_REVIEW.json': binding(ROOT / 'research/appt-cubic-entropy-20261014/REVIEW.json', [[1, 140]],
                                         whole_raw_json_reread_claimed=False),
    'inherited_SHARP_ASYMPTOTIC.md': binding(ROOT / 'research/appt-multilevel-counterexample/SHARP_ASYMPTOTIC.md', [[1, 259]],
                                           use='Only paired-gap arbitrary-edge, row/star residual bound, normalization, lambda1 and q-projection inputs are credited. Reading does not certify every inherited theorem afresh.'),
    'inherited_fixed_m_PAPER.md': binding(ROOT / 'research/appt-all-order-exact-20261014/PAPER.md', [[1, 115], [319, 387]],
                                        use='Fixed-m eventual entropy family theorem and low/high crossing behavior give existence of N_alpha(m); the unread middle proof is credited, not independently rereviewed here.'),
    'independent_controls_script': binding(HERE / 'check_exact_bulk_review.py',
                                         [[1, len((HERE / 'check_exact_bulk_review.py').read_text().splitlines())]],
                                         created_and_executed_by_this_reviewer=True),
    'independent_controls_report': binding(HERE / 'INDEPENDENT_CONTROLS.json', [],
                                         inspection='Complete generated structured report and every asserted result inspected; raw full-line reread not claimed.')
}

blocks = [
    ([1, 58], 'PASS', 'Original all-unitary complex APPT domain, every fixed finite alpha>0, exact entropy and integer ranks retained. Both critical ratios attain positive interior maxima; direct alpha2 calculation yields d2=1/4.'),
    ([60, 117], 'PASS', 'Trace-reweighted cube decomposition proves exact interval maximum and strict vertex equality for every positive order. Unique real optimum confines integer winners to adjacent ranks. Finite maximum absolute continuity and active-branch uniform Taylor derivatives justify integration across all ties.'),
    ([119, 147], 'PASS', 'Maximally entangled necessary test gives exact trace budget including all R+K anomalies. Inherited l2 residual and lambda1 bounds apply before bounded-c assumptions; clipping has the stated exact signed trace increment.'),
    ([149, 199], 'PASS', 'Exact raw power increment and trace logs are subtracted before expansion. The identity for W-s0 cancels the linear trace term; positive kernel mixed derivatives give O(kappa T), and log remainders give O(T^2/D). Alpha1 identity is exact. No derivative of a singular negative endpoint is used.'),
    ([201, 217], 'PASS', 'Bounded head gain and global active-branch derivative lower bound force c bounded for every potentially winning state uniformly in all D>=delta0 m^3. Only afterward are relative error bounds proportional to c used; no bounded-aspect restriction or tiny-anomaly cutoff is introduced.'),
    ([219, 282], 'PASS', 'Every slot assignment is a genuine necessary global-unitary Schmidt test. Nonpositive off-diagonal entries make copositivity equivalent to PSD. Exact rank-one prefactor, positive definiteness and protected Perron gap are noncircular. Floor(m/3) disjoint prefix fits all slots; every omitted mass enters the first walk term, and relative prefix errors have no factor L. Sorted tails give O(c/m) gain. Both signs are included for alpha<2.'),
    ([284, 306], 'PASS', 'Relative protection minus entropy-gain bracket is strictly positive above d+A/m with constants independent of n, including unbounded delta. Every c>0 state loses strictly; c=0 forces all anomalies zero. Strict interval equality classifies every matrix orbit and all integer rank ties.'),
    ([308, 363], 'PASS', 'Either maximizing single sign has a fixed finite protected pattern. Fixed budget interval bounds exact finite costs before choosing B; every pattern is sufficient for actual all-global-unitary APPT. Exact maximizing clipped integer rank removes rounding remainder. Uniform expansion before choosing A gives a strictly profitable actual state at floor(d m^2-A m), proving the O(m) lower band. For any fixed positive delta<d the same single-profile construction gives strictly positive limiting profit, proving E1. Fixed-m credited crossings prove onset existence for each m>=3.'),
    ([365, 377], 'PASS', 'New exact equality/onset statements are separated from earlier zero limiting correction, growing orders, every finite pair, exact minimum threshold coefficient, ASEP, and formal audits. Alpha2 entropy/purity equivalence is correct.')
]

controls = json.loads((HERE / 'INDEPENDENT_CONTROLS.json').read_text())
review = {
    'reviewer': '/root/ordinary_review_exact_bulk',
    'created_utc': datetime.now(timezone.utc).isoformat(),
    'verdict': 'PASS: complete independent ordinary mathematical proof review of initial E0-E4',
    'scope': 'Every fixed finite alpha>0, original all-global-unitary complex APPT set; exact integer-q bulk for all large m and all larger n above d_alpha m^2+A_alpha m; all matrix/rank equalities; minimal eventual onset d_alpha m^2+O_alpha(m).',
    'not_claimed': ['Lean or kernel certification', 'new historical audit roots', 'external human peer review', 'historical novelty certificate', 'varying-order theorem', 'all finite dimension pairs', 'exact O(m) coefficient', 'independent major-conjecture count'],
    'coverage': coverage,
    'mathematical_review_blocks': [{'lines': lines, 'result': result, 'reason': reason}
                                   for lines, result, reason in blocks],
    'mathematical_defects_found': [],
    'manuscript_mathematical_revisions_requested': [],
    'initial_bytes_preserved': True,
    'complete_second_final_reread_claimed': False,
    'author_supporting_file_review': 'Not yet provided/read at this initial mathematics verdict; will be reported separately if received.',
    'independent_supporting_controls': {
        'symbolic_checks': controls['symbolic']['checks'],
        'exact_all_slot_omitted_mass_checks': controls['all_omitted_mass']['checks'],
        'actual_alpha2_O_m_lower_band_checks': controls['O_m_lower_band']['checks'],
        'high_precision_relative_identity_checks': controls['relative_subtraction']['checks'],
        'relative_identity_max_scaled_residual': controls['relative_subtraction']['max_scaled_residual'],
        'wrong_unsubtracted_baseline_extension': controls['wrong_extension'],
        'scope': 'Finite supporting checks, not the proof of infinite eventual quantifiers. All-slot tests are algebraic matrix controls, not a claim that their arbitrary all-slot profiles are actual spectra. Relative identity raw controls likewise make no APPT feasibility claim.'
    },
    'actions_not_performed': ['Lean/Lake/kernel execution', 'audit expansion', 'edits outside independent-review', 'Git commit or catalogue edits', 'publication or submission', 'breadth redirection']
}
(HERE / 'REVIEW_INITIAL.json').write_text(json.dumps(review, indent=2) + '\n', encoding='utf-8')
md = '''# Independent ordinary mathematical review: exact cubic APPT bulk onset

Verdict: **PASS for the complete initial E0-E4 mathematical statements.**
The original all-global-unitary complex APPT set and every fixed finite
alpha>0 are retained. This review is ordinary written mathematics; it is
not Lean/kernel verification, external peer review, or a novelty certificate.

The complete initial PAPER.md was read at lines 1-377, SHA256
`ae5f04557e63a4af6f1d4329448f81d7ca30ea41099770b88a748bba68ce4927`.
The complete initial THEOREM_MAP.md was read at lines 1-18, SHA256
`5e36d29cefa57f69dddccff7337db73bb633805983565ab7eb7b273b0cabb6c3`.
Their immutable INITIAL copies have those exact hashes. No mathematical
defect or manuscript mathematical revision was found. A second complete
final reread is not claimed. Any later change requires a separate delta binding.

The exact interval argument normalizes each cube vertex before mixing and
uses the actual trace weights. Strict power convexity/concavity or von Neumann
convexity yields only winning endpoint spectra. Integer winners lie at the
two neighbors of the unique real optimum. The finite maximum is absolutely
continuous, so its active-branch derivative estimate integrates across every
rank switch and tie, uniformly through arbitrarily small positive kappa.

The raw power and trace logarithms are subtracted exactly before expansion.
Their linear trace discrepancy cancels using the displayed W-s0 identity.
Positive kernel differences cost O(kappa T), while the log remainder costs
O(T^2/D). Negative endpoint increments, including zero and small positive
orders, are kept exact. The von Neumann formula separately has the same bound.
Thus no uncanceled error proportional to D/m^4 enters the large-n argument.

Coercivity uses the inherited finite l2 residual bound first; bounded c is
a consequence for potentially winning states over all D>=delta0 m^3. The
later errors are proportional to c/m, also for arbitrarily tiny anomalies.
The rank-one condition has the exact stated finite prefactor. Its Perron
walk lower bound keeps all assigned matrices away from their inverse
singularities before relative prefix estimates are used.

The disjoint prefix occupies at most 3 floor(m/3) vertices. All remaining
positive and negative witness slots can be filled, and every omitted mass
is counted by the first rest walk term. The prefix error is relative to its
cost, with no L factor. Sorted tail gains are O(c/m). This proves the full
head bound for both signs at every fixed alpha>0, including alpha<2.

The strict final profit bracket has constants independent of n. All c>0
states lose above the certified upper band, while c=0 forces T=0 and kappa=t.
Strict interval equality then gives every matrix (I+t Pi)/(D+tk), with Pi
arbitrary and k every exact winning integer. Rank ties produce no extra
positive-order mixtures.

The single maximizing sign has finitely many genuine physical patterns.
Its exact cost error is bounded on a fixed c interval before selecting the
1/m slack, so the construction is not circular. The same every-pattern PSD
argument is sufficient for every global unitary. Exact maximizing clipped
rank removes any rounding loss. Uniform profit errors are bounded before
choosing the lower-band margin. An actual state therefore beats bulk at
floor(d_alpha m^2-A_alpha m), proving the matching O(m) lower onset bound.
For any fixed positive delta<d_alpha the same construction has positive
limiting profit. The credited fixed-m two-crossing theorem supplies onset
existence for each m>=3. At alpha2, direct single-ratio maximization gives
d2=1/4, and entropy/purity optimizers coincide.

Actual inherited reads: cubic PAPER.md complete 1-461; cubic REVIEW.md
complete; cubic REVIEW.json 1-140; SHARP_ASYMPTOTIC.md complete 1-259;
fixed-m all-order PAPER.md 1-115 and 319-387. Their exact source hashes and
the limited inputs credited are recorded in REVIEW_INITIAL.json. These
reads do not widen any historical Lean audit or claim a fresh audit of
every old theorem.

Independent supporting calculations passed: nine symbolic identities and
Taylor terms; seven exact rational all-slot omitted-mass controls; five
exact rational actual single-positive alpha2 lower constructions at
n=m^2/4-16m; and 168 subtraction controls at 320 digits, including 1e-80
anomalies, beta=1, and unbounded D/m^3. The erroneous uncanceled baseline
approximation was rejected with error greater than 5000. These finite
checks support the manuscript analysis and do not prove its infinite
eventual quantifiers. Arbitrary all-slot and raw identity control profiles
are not represented as actual APPT states.

Author supporting files have not yet been provided/read at this initial
mathematics verdict. Their inspection will be reported separately.
No Lean execution, audit expansion, edits outside this review directory,
catalogue edit, Git commit, publication, submission, or breadth redirection
was performed.
'''
(HERE / 'REVIEW_INITIAL.md').write_text(md, encoding='utf-8')
print(json.dumps({'verdict': review['verdict'], 'review_json': str(HERE / 'REVIEW_INITIAL.json'),
                  'review_md': str(HERE / 'REVIEW_INITIAL.md'),
                  'json_sha256': hashlib.sha256((HERE / 'REVIEW_INITIAL.json').read_bytes()).hexdigest(),
                  'md_sha256': hashlib.sha256((HERE / 'REVIEW_INITIAL.md').read_bytes()).hexdigest()}, indent=2))
