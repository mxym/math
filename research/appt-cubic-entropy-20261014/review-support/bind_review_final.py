from pathlib import Path
from datetime import datetime,timezone
import json,hashlib

out=Path('/mnt/d/math/tmp/appt-cubic-entropy-20261014/independent-review')
source=out.parent
inherited=Path('/home/mxym/math-appt-multiscale-20261013/research/appt-multilevel-counterexample/SHARP_ASYMPTOTIC.md')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks=json.loads((out/'independent_controls.json').read_text())
initial_hash='9bc18d7f5b45cb2c9522425a9a162febb25f9a1ea6d582391b510d82c0fab2e0'
assert sha(source/'INITIAL_PAPER.md')==initial_hash
final_hash='a2e940d320950c258d2aed13bb5afa81ea3bc41efa74acc09dca703d0a817449'
assert sha(source/'PAPER.md')==final_hash
paper_final=(source/'PAPER.md').read_bytes()
new_status=b'Ordinary written proof, 14 October 2026. Independently reviewed. All orders are fixed'
old_status=b'Private research draft, 14 October 2026. Unreviewed. All orders below are fixed'
assert paper_final.count(new_status)==1
assert hashlib.sha256(paper_final.replace(new_status,old_status)).hexdigest()==initial_hash
assert sha(source/'INITIAL_THEOREM_MAP.md')=='345a73ef453836b9d57137b2bfc1995f16c3662b483074527df4ea43f2e1a1fb'
assert sha(source/'THEOREM_MAP.md')=='50dd9a5c171e0efcd65848f5c6e9fca3065d31f9c99b38382ca70d7c0484c693'
map_final=(source/'THEOREM_MAP.md').read_bytes()
map_reversed=map_final.replace(b'14 October2026. This map preceded the manuscript. C0-C4 now have a complete\nordinary written proof and independent mathematical review; no Lean claim.',b'14 October2026. Private active research map; unreviewed, no README or Lean claim.')
map_reversed=map_reversed.replace(b'C2/C3 are now proved with the complete actual upper. Atalpha2 the full\ndelta_crit=1/4. Foralpha<2 the unrestricted graph formula is retained;\none positive anomaly is insufficient already atalpha1. Existing growingm first-nonzero laws,',b'Candidates C2/C3 are not yet proved. Atalpha2 the one-positive trial gives\ndelta_crit=1/4, but a complete actual upper is required. Foralpha<2 one\nexception is not presumed sufficient. Existing growingm first-nonzero laws,')
assert hashlib.sha256(map_reversed).hexdigest()==sha(source/'INITIAL_THEOREM_MAP.md')

now=datetime.now(timezone.utc).isoformat()
blocks=[
 {'lines':[1,24],'result':'PASS','reason':'Original complex density/APPT definition and every fixed alpha>0 are retained. Kernel identity extends continuously to alpha=1 and y=0.'},
 {'lines':[26,72],'result':'PASS','reason':'Positive and negative edge directions are different Schmidt witness slots; all coincidences are included. Nonnegative walk expansion gives the single-anomaly and omitted-mass bounds.'},
 {'lines':[74,124],'result':'PASS','reason':'C0-C4 are the complete predeclared target; below two the unrestricted formula is retained. Limiting pure-bulk onset is not exact finite optimization.'},
 {'lines':[126,181],'result':'PASS','reason':'Maximally entangled witness gives the l1 budget; inherited arbitrary-gap row/star bounds give dimension-independent l2 control before any bounded-c assumption. Clipping and normalization preserve O(1) head residuals and O(m) full kernel sum.'},
 {'lines':[183,234],'result':'PASS','reason':'Interval endpoint maximum, theta formula, and Taylor coefficient give coercivity before compactness. Single-diagonal finite graph constraint protects beta1 before small-order derivatives are used. Actual centered entropy gives the additive kernel identity and exact nonnegative body loss.'},
 {'lines':[236,280],'result':'PASS','reason':'Every eigenbasis slot assignment is an actual global unitary. Matrix with nonpositive off-diagonal entries is copositive iff PSD. Exact finite rank-one criterion and uniformly protected Perron gap yield every prefix cost and retain all omitted l1 mass.'},
 {'lines':[282,345],'result':'PASS','reason':'For finite profiles every adverse unitary trace reduces by spectral rearrangement to one of finitely many patterns, and strict cost slack makes all witness matrices PSD. Full trace normalization/rank rounding yield the lower bound. Upper coercivity, prefix resolvent bounds, tail gain, and omitted-mass penalty establish both finite approximation and l1 compact attained infinite maxima.'},
 {'lines':[347,406],'result':'PASS','reason':'Disjoint single costs give exact bulk onset; strict interactions exclude multiple critical anomalies. Shifted-star inverse, positive squared difference, combined head energy, and superquadratic/subquadratic kernels prove full scalar reduction for alpha>=2. Alpha=2 stationary equation and all critical ties check out.'},
 {'lines':[408,448],'result':'PASS','reason':'Actual tail-mass penalty and exact nonnegative J_m force l1 convergence to the feasible full maximizing compact set, including the budget. Conversely these two criteria recover the additive maximum via the exact asymptotic kernel identity; branch alternation is allowed.'},
 {'lines':[450,461],'result':'PASS','reason':'Provenance and limits are stated accurately: fixed orders, cubic scaling, ordinary proof only; no varying-order uniformity, finite optimizer identity, effective threshold, absolute separability, or Lean claim.'}
]
record={
 'reviewer':'/root/ordinary_review_cubic','created_utc':now,
 'verdict':'PASS: independent ordinary mathematical proof review of all C0-C4',
 'scope':'Complete actual global-unitary APPT set, fixed alpha>0, m->infinity, D/m^3->delta>0. This is ordinary written proof review, not Lean/kernel certification or a historical-novelty verdict.',
 'coverage':{
   'INITIAL_PAPER.md':{'actual_read_ranges':[[1,461]],'total_lines':461,'sha256':initial_hash},
   'INITIAL_THEOREM_MAP.md':{'actual_read_ranges':[[1,18]],'total_lines':18,'sha256':sha(source/'INITIAL_THEOREM_MAP.md')},
   'PAPER.md':{'complete_second_final_reread_claimed':False,'final_sha256':sha(source/'PAPER.md'),'mathematical_line_changes_from_initial':[],'actual_nonmathematical_changed_lines':[[3,3]],'actual_delta_context_read':[[1,6]],'binding':'Reversing the sole disclosed status line restores the exact SHA256 of the fully read initial file; no second complete final reread claimed.'},
   'check_cubic.py':{'actual_read_ranges':[[1,209]],'total_lines':209,'sha256':sha(source/'check_cubic.py'),'author_script_rerun':False},
   'FINITE_CONTROLS.json':{'raw_line_read_ranges':[[1,100]],'total_lines':1810,'sha256':sha(source/'FINITE_CONTROLS.json'),'additional_actual_inspection':'Complete JSON parsed; every key, all eight exact profiles, all finite Schur flags, all six entropy targets and final errors per profile, all wrong-extension controls inspected in structured output. Not a claim of a raw 1810-line reread.'},
   str(inherited):{'actual_read_ranges':[[1,259]],'total_lines':259,'sha256':sha(inherited),'inputs_used':'Sections 2-5 arbitrary edge graph, row/star residual energy, normalization; Section 8 lambda1<=3b and physical q-projection construction. Context reading is not a new review claim for every old theorem.'}
 },
 'mathematical_review_blocks':blocks,
 'critical_obligations':{
   'physical_sufficiency':'For fixed Schmidt witness W, arbitrary global-unitary trace equals sum(lambda_i*w_j*|U_ji|^2). The squared-modulus matrix is doubly stochastic, so spectral rearrangement bounds it below by an adverse permutation. Such a permutation assigns top R to negative slots and bottom K to positive slots, hence is included among the pattern matrices. This also covers Schmidt vectors with zero coordinates.',
   'precompactness_coercivity':'Clipping residual is controlled by actual l2 bound independently of c. Interval deficit gap D[B(t)-B(kappa)] is at least a positive multiple of c_m. Therefore bounded-below correction forces bounded c_m before prefix compactness or singular derivatives are invoked.',
   'small_order_non_circularity':'For bounded c, (19) applied to a pattern containing beta1 on a diagonal forces its Perron root uniformly below two; beta1 therefore stays uniformly below one. This uses the physical rank-one inequality, not the asymptotic entropy identity (17).',
   'no_escaped_mass':'First walk term for every omitted slot contributes exactly 2T_tail/a^2, without requiring disjoint remaining physical slots. It yields c>=C(prefix)+2 liminf T_tail. Tail gain is O(1/L), so optimality forces uniformly vanishing l1 tail mass.',
   'infinite_profile_equality':'All star and strict-interaction arguments are first valid on finite prefixes. At bounded cost their resolvent gaps are uniform, and summability lets U,S and gains pass to the limit; finite-prefix cost supremum defines the infinite cost. Critical multi-anomaly profiles retain a strict positive interaction from two fixed nonzero entries.',
   'all_near_maximizers':'Loss estimates imply both J_m->0 and uniform l1 tail control. Any subsequence has an l1/c convergent subsubsequence satisfying C<=c and (27). Equality forces c=C. Compactness gives the distance criterion for the entire sequence; converse follows by gain/penalty continuity and (17).'
 },
 'defects':[],'required_mathematical_corrections':[],
 'independent_finite_controls':{'script_sha256':sha(out/'independent_controls.py'),'report_sha256':sha(out/'independent_controls.json'),'fixed_label_assignments':10894,'exact_profiles':7,'full_matrix_LDL_checks':9,'symbolic_checks':6,'all_passed':True,'limitation':'Finite arithmetic and polynomial identities support checks; the infinite theorem is established by the independent analytic proof review, not finite examples.'},
 'author_controls_scope':{'author_report_finite_schur_checks':3440,'trace_normalized_entropy_checks':192,'shifted_star_checks':1011,'retained_failures':0,'author_report_read_as_proof':False,'numerical_control_of_alpha_less_than_2':'Two-positive alpha=1 profile rules out replacing the full graph variational problem by the positive scalar formula; no low-order exact optimizer is inferred.'},
 'not_performed':['No Lean/Lake/kernel execution','No audit-root expansion','No repository edit or commit','No publication or external submission','No author script rerun','No literature novelty endorsement','No repeated complete reread of the final mathematical file']
}
record['coverage']['THEOREM_MAP.md']={'actual_read_ranges':[[1,19]],'total_lines':19,'sha256':sha(source/'THEOREM_MAP.md'),'delta':'Initial line3 status split into final lines3-4; initial lines14-16 replaced by final15-17 outcome description. Reverse substitutions restore the exact initial-map hash. The C0-C4 target rows are unchanged.'}
record['coverage']['README.md']={'actual_read_ranges':[[1,36]],'total_lines':36,'sha256':sha(source/'README.md'),'result':'PASS: fixed-order ordinary result and finite-versus-asymptotic limits disclosed; no formal or broad major-conjecture claim.'}
record['coverage']['LITERATURE.md']={'actual_read_ranges':[[1,46]],'total_lines':46,'sha256':sha(source/'LITERATURE.md'),'result':'PASS for bounded screen/provenance statements, not priority certification.'}
record['supplemental_primary_reading']=[
 {'url':'https://arxiv.org/abs/2608.03390','scope':'Metadata/abstract and version history; v2 18 September 2026 verified.'},
 {'url':'https://arxiv.org/html/2608.03390v2','actual_rendered_context_read':[[862,954]],'scope':'Includes Theorem6.10 polytope entropy domain; not a complete paper audit.'},
 {'url':'https://arxiv.org/abs/2609.18568','scope':'Metadata/abstract and version history; v1 16 September 2026 verified.'},
 {'url':'https://arxiv.org/html/2609.18568v1','actual_rendered_context_read':[[286,373]],'scope':'Includes Section3 outer-polytope entropy statement; not a complete qubit-proof review.'},
 {'url':'https://arxiv.org/abs/2609.06617','scope':'Metadata/abstract and version history; v1 6 September 2026 verified. Ky Fan partial-transpose graph optimization domain only; no full paper audit.'}]
record['source_bindings']={n:sha(source/n) for n in ['PAPER.md','INITIAL_PAPER.md','THEOREM_MAP.md','INITIAL_THEOREM_MAP.md','README.md','LITERATURE.md','check_cubic.py','FINITE_CONTROLS.json']}
record['binding_guard_event']={'event':'Initial helper rejected the changed final PAPER hash before any review output was written. The author had meanwhile disclosed one status edit. The final helper independently reverses that single byte substitution to validate all mathematical bytes against the reviewed initial source.','mathematical_control_failure':False}
(out/'BINDING_GUARD_EVENT.json').write_text(json.dumps(record['binding_guard_event'],indent=2)+'\n')
(out/'REVIEW.json').write_text(json.dumps(record,indent=2)+'\n')
md=f'''# Independent ordinary review of the cubic-scale APPT packet

Verdict: **PASS for the complete written statements C0-C4**. Reviewed at {now}.
The result applies to the entire original all-global-unitary APPT set, every
fixed alpha>0, and all dimension sequences with m->infinity and D/m^3->delta>0.
This is mathematical manuscript review. It is not a Lean or kernel audit,
external peer review, or a historical-novelty certificate.

## Actual source coverage and binding

- INITIAL_PAPER.md: complete 1-461, SHA256 `{initial_hash}`.
- INITIAL_THEOREM_MAP.md: complete 1-18, SHA256 `{sha(source/'INITIAL_THEOREM_MAP.md')}`.
- Final PAPER.md changes only the disclosed nonmathematical status at line3.
  Its final SHA256 is `{sha(source/'PAPER.md')}`. Reversing that sole change
  restores the exact initial hash. No mathematical line changed, and no
  second complete final reread is claimed. Delta context 1-6 was read.
- Final THEOREM_MAP.md: complete 1-19, SHA256 `{sha(source/'THEOREM_MAP.md')}`.
  Only status and outcome descriptions changed. Its target rows are intact,
  and reversing the disclosed edits restores the exact initial-map hash.
- README.md: complete 1-36; LITERATURE.md: complete 1-46. Both supplementary
  sources were checked separately and are bound in REVIEW.json.
- check_cubic.py: complete 1-209, SHA256 `{sha(source/'check_cubic.py')}`.
  The author script was inspected, not rerun or substituted for proof.
- FINITE_CONTROLS.json: raw lines 1-100 plus complete structured inspection
  of all report keys, eight profiles, finite flags, entropy targets/final
  errors, and wrong-extension controls. The full JSON was parsed; a raw
  1810-line reread is not claimed. SHA256 `{sha(source/'FINITE_CONTROLS.json')}`.
- Inherited SHARP_ASYMPTOTIC.md: actually read 1-259, SHA256
  `{sha(inherited)}`. Only its stated arbitrary-edge, row/star, normalization,
  lambda1 bound, and physical q-projection inputs are used. This reading
  does not widen the historical audit scope or newly certify all old results.

## Proof findings

No mathematical defect requiring manuscript revision was found.

The physical slot reduction is exact. A positive anomaly occupies a negative
Schmidt edge direction; a negative anomaly occupies a positive diagonal or
edge direction. Both can occupy the same edge because they are different
witness eigenvectors. Arbitrary unitary traces reduce by the usual spectral
rearrangement inequality to adverse permutations: |U_ji|^2 is doubly
stochastic. Thus the sufficient construction covers arbitrary global
unitaries, not just selected eigenbases, including lower Schmidt ranks.

The exact matrix is (2+kappa)I-kappa J-P. Its nonpositive off-diagonal entries
make the nonnegative Schmidt test equivalent to PSD by taking absolute values
in Rayleigh quotients. The exact finite rank-one prefactor in (19) is correct.
Its Perron/walk gap uniformly protects every finite prefix at bounded c.
In particular the single-diagonal beta1 test keeps beta1 below one before
bounded small-order kernel derivatives are used; this is noncircular.

Coercivity precedes compactness. The inherited actual l2 residual bound gives
O(1) head kernel gain for every physical spectrum. Interval endpoint loss
then forces c_m bounded for any bounded-below correction. Only afterward is
the additive centered entropy identity (17) used. Both actual trace
normalization and integer-rank rounding are retained at additive o(1).

Every fixed finite profile with strict cost slack gives an actual all-unitary
APPT state. There are finitely many witness patterns for that profile, and
all exact rank-one inequalities converge to their graph costs. Endpoint ranks
are large enough, and trace-normalized kernel gain reaches the profile value.

The first omitted walk term records all tail l1 mass even when there are
more anomalous entries than could be placed disjointly in the physical graph.
The O(1/L) tail gain and positive mass penalty prove unrestricted finite
approximation, attained infinite profiles, and compactness. The same two
losses prove both directions of the complete near-maximizer criterion.

The onset is exactly the maximum single-anomaly gain/cost ratio. Every pair
of nonzero anomalies has a strict interacting pattern, so only the named
single families and the empty profile can tie at criticality. Above it the
empty anomaly profile is unique. These are limiting claims, not exact finite
optimizer claims.

For alpha>=2 the shifted-star inverse and square identity give a single-edge
cost lower bound at the combined head energy. The positive superquadratic and
negative subquadratic kernels then give the unrestricted scalar upper. Strict
cost equality supplies the full single-positive equality profile, including
alpha=2. The stationary equation and p=0/p=1 critical tie in (9) are correct.
For alpha<2 the full graph formula is retained; no scalar substitution is made.

## Independent supporting arithmetic

An independent fixed-label enumeration, different from the author's
vertex-creation generator, examined **10,894 slot assignments** on seven
rational profiles. All maximal graph costs matched. Nine direct full m by m
LDL checks accepted strict-cost constructions and rejected the trace-only or
unprotected-width alternatives. Six symbolic checks independently covered
the finite rank-one prefactor, two-negative strict gap, shifted-star square,
full three-vertex inverse, and the interval optimum/deficit Taylor terms.
All passed. The independent script/report are bound in REVIEW.json.

The author report separately records 3,440 finite Schur checks, 192
trace-normalized entropy checks, and 1,011 shifted-star checks, with no
retained failures. Its low-order two-positive control correctly rejects an
unrestricted alpha=1 scalar reduction. These remain finite supporting
calculations and are not the proof of C0-C4.

The supplemental literature metadata were independently checked against the
primary arXiv sources: AAW v2 (18 September 2026), Tran v1 (16 September
2026), Jiang/Qiu/Yu v1 (6 September 2026). Actual contextual reads were AAW
rendered 862-954 and Tran rendered 286-373, plus metadata/abstracts. Their
disclosed domains agree with the bounded literature screen. This is not a
full paper audit or an originality certificate.

The initial binding helper safely rejected the newly changed status bytes
before writing any review output. The final helper validated the declared
byte deltas explicitly; this was not a mathematical control failure.

No Lean execution, audit expansion, catalog edit, commit, submission,
publication, or external novelty claim was performed by this reviewer.
'''
(out/'REVIEW.md').write_text(md)
print(json.dumps({'review_json_sha256':sha(out/'REVIEW.json'),'review_md_sha256':sha(out/'REVIEW.md'),'review_json_lines':len((out/'REVIEW.json').read_text().splitlines()),'review_md_lines':len((out/'REVIEW.md').read_text().splitlines()),'verdict':record['verdict']}))