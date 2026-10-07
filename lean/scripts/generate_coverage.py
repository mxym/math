#!/usr/bin/env python3
"""Build an exhaustive paper/assumption map using the actual Lean signatures."""
from pathlib import Path
import csv
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
entries = json.loads((ROOT / 'axiom-report.json').read_text())
statements = (ROOT / 'logs/statements.log').read_text()
if 'error:' in statements:
    raise RuntimeError('Lean signature log contains errors')
fresh_statements = subprocess.check_output(
    ['lake', 'env', 'lean', 'Statements.lean'], cwd=ROOT, text=True, stderr=subprocess.STDOUT)
if statements != fresh_statements:
    raise RuntimeError('Stored signature log differs from freshly elaborated signatures')
fresh_axioms = subprocess.check_output(
    ['lake', 'env', 'lean', 'Audit.lean'], cwd=ROOT, text=True, stderr=subprocess.STDOUT)
if (ROOT / 'logs/axioms.log').read_text() != fresh_axioms:
    raise RuntimeError('Stored axiom log differs from fresh Lean output')
subprocess.run(['python3', str(ROOT / 'scripts/check_axioms.py')], cwd=ROOT, check=True)
entries = json.loads((ROOT / 'axiom-report.json').read_text())

RADE = 'entry005 v3 §6 Lemma 6.1 / (6.1); v4 §2 (2.2)'
EQUAL = 'entry005 v4 §2 Lemma 2.1'
DETER = 'entry005 v3 §6 proof of Theorem 6.2; v4 §3 (3.1)'
DEFECT = 'entry005 v3 §3 (3.1)-(3.2), finite inner-law mechanism'
TRANS = 'entry001 v5 proof of Lemma lem:minimum, eq:signed-square; entry008 v1 §2 proof of thm:interpolation'
RECUR = 'entry005 v5 §2 (2.1)-(2.2)'
OAI = 'OpenAI/math lean/OAI/Geometry/ProjectionVolume/'
FINITE = 'Finite index type, real coefficients; Fintype and DecidableEq instances as printed in the exact signature.'
WEIGHTS = 'Finite index type, real values and weights; Fintype instance. Probability normalization is not required.'
BAL = 'Every |c_i| ≤ (sum_j |c_j|)/2; all-zero and empty-index cases are included.'
POLY = 't lies in balancedPolytope: every 0 ≤ t_i ≤ 1/2 and sum_i t_i = 1.'

# Values: paper locator, coverage kind, mathematical assumptions, description.
spec = {}
def add(prefix, rows):
    for short, paper, kind, assumptions, description in rows:
        spec[prefix + short] = (paper, kind, assumptions, description)

add('Mxym.Rademacher.', [
 ('abs_sign', RADE, 'helper', 'Any Boolean b.', 'Each sign has absolute value one.'),
 ('sign_not', RADE, 'helper', 'Any Boolean b.', 'Flipping a Boolean negates its real sign.'),
 ('sign_space_card', RADE, 'helper', FINITE, 'The independent sign space has cardinality 2^N.'),
 ('mean_nonneg', RADE, 'helper', FINITE, 'Uniform sign average is nonnegative.'),
 ('mean_smul', RADE, 'helper', FINITE + ' Any real scalar a.', 'Absolute homogeneity of the sign average.'),
 ('convex_mean', RADE, 'helper', FINITE, 'The sign average is convex on the entire real coefficient space.'),
 ('continuous_mean', RADE, 'helper', FINITE, 'Continuity of the finite sign average.'),
 ('abs_pair', EQUAL, 'helper', 'Real a,z with |z| ≤ |a|.', '|a+z|+|-a+z| = 2|a|.'),
 ('mean_eq_of_dominant', EQUAL, 'proved extension', FINITE + ' A chosen k satisfies sum_i |c_i| - |c_k| ≤ |c_k|.', 'The sign average equals the absolute value of a dominant coefficient, for arbitrary N.'),
 ('compact_balancedPolytope', RADE, 'helper', 'Finite real coefficient space; no nonemptiness assumption.', 'Compactness of the normalized capped simplex.'),
 ('convex_balancedPolytope', RADE, 'helper', 'Finite real coefficient space.', 'Convexity of the normalized capped simplex.'),
 ('extreme_has_half', RADE, 'helper', FINITE + ' t is an extreme point of balancedPolytope.', 'An extreme point saturates the 1/2 cap. This uses a proved perturbation argument.'),
 ('normalized_bound', RADE, 'normalized paper statement', FINITE + ' ' + POLY, 'mean(t) ≤ 1/2, proved using the audited mathlib Krein-Milman theorem; this theorem is not assumed as a custom axiom.'),
 ('mean_abs', EQUAL, 'helper', FINITE, 'Absorbing all coefficient signs leaves the average unchanged.'),
 ('mean_zero', EQUAL, 'helper', FINITE, 'The average of the zero coefficient vector is zero.'),
 ('balanced_bound', RADE, 'complete finite paper statement', FINITE + ' ' + BAL, 'mean(c) ≤ (sum_i |c_i|)/2 for every finite family of real coefficients.'),
 ('mean_eq_half_of_half_mass', EQUAL, 'paper equality mechanism', FINITE + ' A chosen k satisfies |c_k| = (sum_i |c_i|)/2.', 'A half-mass coefficient gives equality, for arbitrary N. No separate balance assumption is needed.'),
 ('mean_reindex', EQUAL, 'helper', 'Finite types ι,κ with Fintype and DecidableEq; an equivalence e:ι≃κ; real c on κ.', 'Reindexing preserves the uniform sign average.'),
 ('mean_sum_zero', EQUAL, 'helper', 'Finite types ι,κ with Fintype and DecidableEq; real c on ι.', 'Padding a coefficient family with any finite set of zero coefficients preserves its average.'),
 ('mean_restrict', EQUAL, 'helper', FINITE + ' A decidable predicate p; c_i=0 whenever not p(i).', 'Restricting to a set containing the support preserves the average.'),
 ('sum_signs_succ', EQUAL, 'helper', 'Any n:Nat and any real function on Fin(n+1)→Bool.', 'Exact finite sign-sum recursion into the true and false first-coordinate cases.'),
 ('mean_three_nonneg', RADE + '; ' + EQUAL, 'paper three-variable identity', 'Real a,b,c ≥0 with a≤b+c, b≤a+c, c≤a+b.', 'The three-coefficient sign average equals (a+b+c)/2; signs are enumerated through proven finite equivalences.'),
 ('mean_four_quarters', EQUAL + ', strictness witness', 'paper strictness witness', 'Exactly four coefficients, each 1/4.', 'Exact kernel-checked value 3/8, without native_decide.'),
 ('normalized_strict_positive', EQUAL, 'paper strictness mechanism', FINITE + ' ' + POLY + ' All t_i>0, all t_i<1/2, and card(ι)≥4.', 'Strict inequality mean(t)<1/2 using an explicit convex mixture with the four-quarter witness.'),
 ('restrict_balanced', EQUAL, 'helper', 'Finite real family t with ' + POLY, 'Restricting to nonzero coordinates preserves the normalized constraints.'),
 ('normalized_strict', EQUAL, 'paper strictness mechanism', FINITE + ' ' + POLY + ' All t_i<1/2 and at least four nonzero coordinates.', 'Strict inequality after reduction to the support.'),
 ('normalized_small_finite', EQUAL, 'helper', 'v:Fin(n)→Real lies in balancedPolytope and n≤3.', 'Exact equality for a normalized family with at most three coordinates; impossible low-dimensional normalized cases are handled by their hypotheses.'),
 ('normalized_small_support', EQUAL, 'paper equality mechanism', FINITE + ' ' + POLY + ' At most three nonzero coordinates.', 'Exact equality for normalized families with small support.'),
 ('normalized_equality_iff', EQUAL, 'normalized paper statement', FINITE + ' ' + POLY, 'mean(t)=1/2 iff at most three coordinates are nonzero or a coordinate equals 1/2.'),
 ('balanced_equality_iff', EQUAL, 'complete finite paper statement', FINITE + ' ' + BAL, 'mean(c)=(sum_i |c_i|)/2 iff at most three coefficients are nonzero or one has half the total absolute mass. This is the full published Lemma 2.1, including the zero case.'),
])


QUANT = 'quantitative-symmetric-projection-stability supplement, Lemma 3.1 equation (3.1), mxym/math dd5c29fc50c3e0694591260f60f3030d551d304d'
add('Mxym.Rademacher.', [
 ('normalized_defect_lower_bound', QUANT, 'finite coefficient defect bound', FINITE + ' ' + POLY + ' Nonnegative real thresholds t,g; an embedding e:Fin(4)↪ι selects four distinct coefficients each at least t; every coefficient is at most 1/2-g.', 'Defect 1/2-mean(a) is at least min(t/2,g/4). Taking t to be the fourth-largest coefficient and g=1/2-max(a) recovers equation (3.1), provided the sorted-coordinate witness is supplied. No order-statistic selector, coefficient-distance estimate, determinant-law integration or geometric stability theorem is proved.'),
 ('normalized_defect_lower_bound_or_zero', QUANT, 'finite coefficient defect bound, zero-threshold extension', FINITE + ' ' + POLY + ' Nonnegative t,g; every coefficient at most 1/2-g; either t=0 or an embedding selects four distinct coefficients each at least t.', 'The same defect bound permits t=0 without a four-coordinate witness, including index types with fewer than four elements. The family is still normalized to mass one: this is not a theorem about an all-zero normalized family. No coefficient-distance estimate or geometric result is included.'),
])

add('Mxym.Determinant.', [
 ('lift_expansion', DETER, 'unconditional algebraic identity', 'Any natural d, real d×(d+1) matrix x, and real top-row vector a.', 'Laplace expansion of the lift along its first row in terms of the explicitly defined signed cofactors.'),
 ('horizontal_cofactor_relation', DETER, 'complete algebraic paper statement', 'Any natural d, real d×(d+1) matrix x, and row i:Fin(d).', 'For each row, sum_j c_j x_ij=0. All ranks and singular cases are allowed; no geometric identity is assumed.'),
 ('sign_cancellation', DETER, 'complete algebraic paper statement', 'Any natural d, real horizontal matrix x and Boolean sign vector ε.', 'The absolute lifted determinant after independent column signs equals |sum_j ε_j c_j|. The common product of signs is proved to cancel.'),
 ('sign_average_eq', DETER, 'complete algebraic paper statement', 'Any natural d and real horizontal matrix x.', 'Exact average of signed lifted determinants equals the Rademacher mean of the cofactor family.'),
 ('balanced_sign_average_bound', DETER, 'conditional pointwise corollary', 'Any natural d and real horizontal matrix x; every |cofactor_i|≤half the total absolute cofactor mass.', 'The pointwise cofactor sign-average upper bound. The balance assumption is explicit.'),
 ('balanced_sign_average_equality_iff', DETER + '; ' + EQUAL, 'conditional pointwise corollary', 'Any natural d and real horizontal matrix x; every |cofactor_i|≤half the total absolute cofactor mass.', 'Complete pointwise equality criterion under the explicit balance assumption.'),
])


NORMED = 'entry005 v4 section 3, norm argument immediately after equation (3.1); v3 section 6 proof of Theorem 6.2'
NORM_ASSUMPTIONS = 'Finite real coefficients c and vectors x in a real normed space E; sum_j c_j • x_j = 0; norm(x_j)=1 whenever c_j is nonzero. No coefficient-balance hypothesis.'
COFACTOR_NORM_ASSUMPTIONS = 'Any natural d and real d×(d+1) matrix x; a supplied real linear equivalence phi:(Fin d→Real)≃ₗE into a real normed space; norm(phi(column_j))=1 for every nonzero cofactor. No balance hypothesis, rank assumption or unit condition on zero-cofactor columns.'
add('Mxym.NormedBalance.', [
 ('coefficient_balance', NORMED, 'complete finite normed relation mechanism', NORM_ASSUMPTIONS, 'Derives |c_i|<=half the total absolute coefficient mass using the zero-sum relation, norm homogeneity and the triangle inequality. Unit normalization is required only on active coefficients.'),
 ('rademacher_bound', NORMED + '; v4 (2.2)', 'finite normed relation corollary', NORM_ASSUMPTIONS, 'The finite independent-sign upper bound follows from the derived coefficient balance.'),
 ('rademacher_equality_iff', NORMED + '; v4 Lemma 2.1', 'finite normed relation equality criterion', NORM_ASSUMPTIONS, 'The full finite equality criterion follows from derived balance: support size<=3 OR a coefficient has half the total absolute mass. It retains the half-mass branch and is not the exposed-point rigidity conclusion of v4 Lemma 3.1.'),
])
add('Mxym.Determinant.', [
 ('cofactor_vector_relation', DETER, 'unconditional vector identity', 'Any natural d and real d×(d+1) matrix; no norm, rank or coefficient normalization hypothesis.', 'The proved row-wise horizontal cofactor relation is assembled into sum_j cofactor_j • column_j=0.'),
 ('mapped_cofactor_relation', NORMED, 'unconditional linear image identity', 'Any natural d and real matrix x; a supplied real linear equivalence phi:(Fin d→Real)≃ₗE into a real normed space. No unit norm or balance assumption.', 'Linear mapping preserves the cofactor zero-sum vector relation. The normed structure is printed in the signature, although the identity uses only linearity.'),
 ('cofactor_balance_of_normalized_columns', NORMED, 'pointwise normed cofactor bridge', COFACTOR_NORM_ASSUMPTIONS, 'Derives cofactor balance from the mapped algebraic relation and unit norms on active columns. The actual convex-body Minkowski norm and boundary-point normalization are not constructed.'),
 ('normalized_sign_average_bound', NORMED + '; v4 (2.2)', 'pointwise normalized-column cofactor corollary', COFACTOR_NORM_ASSUMPTIONS, 'The signed lifted determinant average is bounded by half the total cofactor mass using derived balance; no balance inequality is assumed.'),
 ('normalized_sign_average_equality_iff', NORMED + '; v4 Lemma 2.1', 'pointwise normalized-column cofactor equality criterion', COFACTOR_NORM_ASSUMPTIONS, 'The complete finite sign-average equality criterion under active-column normalization: support<=3 OR a half-mass cofactor. Exposedness and elimination of the half-mass branch are not formalized.'),
])

add('Mxym.FiniteDefect.', [
 ('mean_decomposition', DEFECT, 'finite algebraic mechanism', WEIGHTS + ' Weights may even be signed.', 'sum_i p_i z_i=P-Q for P=sum p_i max(z_i,0), Q=sum p_i max(-z_i,0).'),
 ('absolute_decomposition', DEFECT, 'finite algebraic mechanism', WEIGHTS + ' Weights may even be signed.', 'sum_i p_i |z_i|=P+Q.'),
 ('defect_identity', DEFECT, 'finite inner-law specialization', WEIGHTS + ' Weights may even be signed.', 'sum_i p_i|z_i|-|sum_i p_i z_i|=2 min(P,Q). The outer determinant-law integral in the paper is not part of this statement.'),
 ('finite_jensen', DEFECT, 'finite inner-law specialization', WEIGHTS + ' Every p_i≥0.', 'Weighted finite triangle/Jensen inequality.'),
 ('defect_lower_bound', DEFECT, 'finite witness mechanism', WEIGHTS + ' Every p_i≥0; chosen i,j with z_i≥0 and z_j≤0.', 'Defect ≥2 min(p_i z_i,p_j(-z_j)); this is the inner-law factor in (3.2), without the outer d! product factor.'),
 ('strict_of_opposite_signs', DEFECT, 'finite strictness mechanism', WEIGHTS + ' Every p_i≥0; chosen i,j with p_i,p_j>0 and z_i>0>z_j.', 'Strict Jensen inequality whenever positive-weight values have opposite strict signs.'),
 ('positive_mass_eq_zero_iff', DEFECT, 'helper', WEIGHTS + ' Every p_i≥0.', 'P=0 iff all positive-weight values are nonpositive.'),
 ('negative_mass_eq_zero_iff', DEFECT, 'helper', WEIGHTS + ' Every p_i≥0.', 'Q=0 iff all positive-weight values are nonnegative.'),
 ('finite_jensen_eq_iff', DEFECT + '; v3 §2 sign condition after (2.2)', 'finite equality mechanism', WEIGHTS + ' Every p_i≥0.', 'Weighted finite Jensen equality iff all positive-weight values have one common weak sign; zero weights impose no restriction.'),
])

add('Mxym.Transport.', [
 ('signed_square', TRANS, 'complete scalar paper statement', 'Any real a,b with a≤b.', '(b-a)^2≤2(b|b|-a|a|).'),
 ('signed_square_eq_iff', TRANS, 'proved extension', 'Any real a,b with a≤b.', 'Equality in the scalar signed-square bound iff a=b or a=-b; the paper does not assert this extension explicitly.'),
 ('intermediate_square', TRANS + ', subsequent pointwise error bound', 'complete scalar mechanism', 'Any real a,q,b with a≤q≤b.', '(q-a)^2≤2(b|b|-a|a|). Establishing derivative/secant order analytically is outside this scalar statement.'),
 ('three_term_square', TRANS + ', three-term decomposition', 'complete scalar mechanism', 'Any real x,y,z.', '(x+y+z)^2≤3(x^2+y^2+z^2).'),
])

add('Mxym.BalancedRecursion.', [
 ('shifted_dimension', RECUR, 'complete explicitly defined scalar recurrence', 'Natural t,p,j with t≥2. p≥1 is not needed for this algebraic formula.', 'dimension_0=p, dimension_(j+1)=t^2 dimension_j+t-1; then dimension_j+1/(t+1)=(p+1/(t+1))(t^2)^j. Nat subtraction is justified in the proof.'),
 ('invariant_closed_form', RECUR, 'complete explicitly defined scalar recurrence', 'Any natural t,p,j. Division is Lean real division, including its defined zero-denominator behavior; the paper only uses t≥2,p≥1.', 'invariant_0=1/(p+1), invariant_(j+1)=invariant_j/t; then invariant_j=1/((p+1)t^j).'),
 ('dimension_binary', RECUR + ', t=2', 'scalar recurrence corollary', 'Any natural p,j.', '3 dimension(2,p,j)+1=(3p+1)4^j.'),
 ('winning_dimension_level_six', RECUR + ', (t,p,j)=(2,5,6)', 'exact scalar instance', 'No hypotheses.', 'dimension(2,5,6)=21845. The name does not certify that the pair is optimal.'),
 ('winning_invariant_level_six', RECUR + ', (t,p,j)=(2,5,6)', 'exact scalar instance', 'No hypotheses.', 'invariant(2,5,6)=1/384. The name does not certify that the pair is optimal.'),
])

add('OAI.Paper092.', [
 ('twice_sum_negative_eq_sum_abs', OAI + 'ProjectionCoefficients.lean:twice_sum_negative_eq_sum_abs', 'audited exact upstream reuse', 'Finite real family v with sum_i v_i=0.', 'Twice the total negative mass equals the total absolute mass. This is a finite cancellation identity, not a geometric volume identity.'),
 ('simplex_constant_product_ratio', OAI + 'Arithmetic.lean:simplex_constant_product_ratio', 'audited exact upstream reuse', 'Natural r,s>0; simplexConstant(d) is explicitly (d+1)d^d/d!.', 'Exact factorial/binomial scalar product ratio; no equality with an actual convex-body invariant is asserted here.'),
 ('dimension_twenty_ratio', OAI + 'Arithmetic.lean:dimension_twenty_ratio', 'audited exact upstream reuse', 'No hypotheses; the same explicit scalar definition.', 'C_10^2/C_20=22355476/22020096 by kernel-checked exact arithmetic.'),
 ('dimension_twenty_strict', OAI + 'Arithmetic.lean:dimension_twenty_strict', 'audited exact upstream reuse', 'No hypotheses; the same explicit scalar definition.', 'C_20<C_10^2. This does not itself prove a geometric product or projection-volume formula.'),
])

if set(spec) != {e['name'] for e in entries}:
    raise RuntimeError('Unreviewed or missing coverage entry: ' + repr(set(spec) ^ {e['name'] for e in entries}))

def application_gaps(name):
    if name.startswith('Mxym.NormedBalance.') or name in {
        'Mxym.Determinant.cofactor_vector_relation', 'Mxym.Determinant.mapped_cofactor_relation',
        'Mxym.Determinant.cofactor_balance_of_normalized_columns',
        'Mxym.Determinant.normalized_sign_average_bound', 'Mxym.Determinant.normalized_sign_average_equality_iff'}:
        return ['A convex body or its Minkowski functional is not constructed; the real normed space, linear equivalence where used, and active-vector unit norms are supplied.',
                'Boundary-law normalization/evenness, measure integration, exposed-point rigidity, rank/circuit classification and geometric equality/stability remain unformalized. The half-mass equality branch remains present.']
    if name in {'Mxym.Rademacher.normalized_defect_lower_bound', 'Mxym.Rademacher.normalized_defect_lower_bound_or_zero'}:
        return ['Only Lemma 3.1 equation (3.1) is proved in witness form; its additional l1-distance bound 8(N-3)D is not formalized.',
                'Construction of sorted coefficient order statistics and their witness, geometric cofactor normalization, boundary-law integration and subsequent quantitative geometric stability are not formalized.']
    if name.startswith('Mxym.Determinant.'):
        return ['The two original balanced corollaries assume balance explicitly. The new normalized-column corollaries derive it; constructing the actual convex-body Minkowski norm and proving boundary-unit normalization are not formalized.',
                'Even boundary-law sign averaging, integration, A/B identification, and convex-body equality classification are not formalized.']
    if name.startswith('Mxym.FiniteDefect.'):
        return ['General measure integrability/Fubini, determinant inner-mean identification, and the outer law integral in B-A are not formalized.',
                'The outer d! permutations/product-weight factor of (3.2), simplex rigidity, and geometric stability are not formalized.']
    if name.startswith('Mxym.Transport.'):
        return ['Convex derivative/secant monotonicity, almost-everywhere endpoint legitimacy, minimum-density integration, translation changes of variables, and transport/potential estimates are not formalized.']
    if name.startswith('Mxym.BalancedRecursion.'):
        return ['Geometric product/join dimension and invariant identities connecting these defined scalars to actual convex bodies are not formalized.',
                'R recurrence, Stirling/Robbins estimates, infinite logarithmic limit/tail bounds, rational-log/large-integer screening, Bellman work, and global uniqueness of (2,5) are not formalized.']
    if name.startswith('OAI.'):
        return ['No full upstream geometric theorem is certified here; the excerpt is independent finite/scalar algebra.',
                'Identifying simplexConstant with an actual projection-volume invariant and the geometric product/join laws is not formalized in this project.']
    return ['The finite Rademacher statement itself has no unformalized mathematical dependency beyond the compiled pinned libraries.',
            'Its application to convex-body boundary laws, exposed-point circuits, rank-two decomposition, and the full v4 equality classification is not formalized.']

out = []
for e in entries:
    name = e['name']
    start = re.search(r'^' + re.escape(name) + r'(?=[ .:])', statements, re.M)
    if start is None:
        raise RuntimeError('Missing exact signature for ' + name)
    tail = statements[start.start():]
    next_start = re.search(r'\n(?:Mxym\.|OAI\.)', tail)
    signature = tail[:next_start.start() if next_start else len(tail)].strip()
    paper, kind, assumptions, description = spec[name]
    out.append({**e, 'paper_statement': paper, 'coverage_kind': kind,
                'assumptions_summary': assumptions, 'description': description,
                'exact_lean_signature': signature,
                'unformalized_application_dependencies': application_gaps(name)})
(ROOT / 'coverage.json').write_text(json.dumps(out, indent=2, ensure_ascii=False) + '\n')
with (ROOT / 'coverage.csv').open('w', newline='') as f:
    columns = ['name', 'source', 'paper_statement', 'coverage_kind', 'assumptions_summary',
               'description', 'axioms', 'unformalized_application_dependencies', 'exact_lean_signature']
    writer = csv.DictWriter(f, fieldnames=columns, lineterminator='\n')
    writer.writeheader()
    for e in out:
        writer.writerow({k: '; '.join(e[k]) if isinstance(e[k], list) else e[k] for k in columns})

intro = '''MXym/math Lean verification report — 7 October 2026

OUTCOME
68 exported theorems successfully compile, including supporting lemmas and
four audited upstream theorems. The primary achievement is the full finite
balanced Rademacher inequality and equality criterion (entry005 v3 Lemma 6.1,
entry005 v4 Lemma 2.1), valid for arbitrary finite real coefficients including
the zero case. No geometric identity is postulated to prove those statements.

For N coefficients, sign(true)=1, sign(false)=-1 and
  mean(c) = [sum over all epsilon: index -> Bool of |sum_i sign(epsilon_i)c_i|]
            / card(index -> Bool),
and the latter cardinality is proved to be 2^N. This is exactly the independent
uniform finite sign expectation in the paper; no measure-theory bridge is needed
for this finite formulation. Balance means |c_i| <= (sum_j |c_j|)/2 for every i.
The two main Lean results are:
  Mxym.Rademacher.balanced_bound
  Mxym.Rademacher.balanced_equality_iff
Equality holds precisely when support size <=3 or a coefficient has half mass.

QUANTITATIVE FINITE EXTENSION
The two additional coefficient theorems prove the supplement's Lemma 3.1
equation (3.1) with four distinct selected coordinates or a zero t threshold.
They do not prove the same lemma's l1-distance-to-equality estimate, a sorted
order-statistic construction, or any integrated/geometric stability result.

FINITE NORMED RELATION AND COFACTOR EXTENSION
Eight new theorems derive balance from a zero-sum real vector relation and
unit norms on active coefficients. Algebraic cofactors satisfy that relation,
and a supplied real linear equivalence maps it into a supplied normed space.
The new normalized-column sign-average corollaries derive rather than assume
cofactor balance. The convex-body Minkowski norm, boundary-unit normalization,
even law and integration are still unformalized. The equality statement keeps
both the small-support and half-mass branches; it does not prove exposedness.

OTHER CERTIFIED COVERAGE
The determinant expansion, horizontal cofactor relation and independent-sign
cancellation are unconditional identities for arbitrary real d by (d+1)
matrices, including singular cases. The lift puts its added row FIRST, whereas
the paper uses the last row. Moving that row changes the determinant by (-1)^d;
the paper applications here use absolute values, so this convention has no
effect on their statements. The two balanced determinant corollaries explicitly
ASSUME the balance inequality. The new normed corollaries derive balance from
the supplied active-column unit norms. Constructing the actual convex-body
Minkowski norm, proving boundary normalization and the integrated symmetric
boundary-law bound remain unformalized.

The finite defect identity uses P=sum_i p_i max(z_i,0), Q=sum_i p_i max(-z_i,0).
It proves sum_i p_i|z_i|-|sum_i p_i z_i|=2 min(P,Q), weighted Jensen, a two-sign
witness bound, strictness, and the full finite equality criterion. The algebraic
identity even permits signed weights; the Jensen/strictness statements require
p_i>=0. No sum_i p_i=1 assumption is needed. These are the inner-law mechanisms
of entry005 v3 (3.1)-(3.2), not the entire integrated determinant identities.

The ordered signed-square estimate and intermediate-value/three-term scalar
inequalities used in entries001/008 are proved directly over the reals. An
additional scalar equality criterion is proved and labeled as an extension.

The dimension/invariant recurrences in entry005 v5 (2.1)-(2.2) are explicit Lean
recursive definitions, and their closed forms are proved by induction. Exact
binary-orbit scalar values d_6=21845 and a_6=1/384 are checked. Calling them the
invariants of the actual geometric recursion still requires the unformalized
product/join identities; this project does not certify v5 Theorem 1.1 or its
strict infinite-parameter optimality gap, or the later Bellman certificates.

REPRODUCIBILITY AND ACTUAL VALIDATION
Lean 4.34.1 (official binary), compiler commit
5045d0056413266e57c625dcd7c365b10e377c52; Lake 5.0.0-src+5045d00;
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
lean-toolchain, lakefile.toml and lake-manifest.json pin all dependencies.
scripts/bootstrap.sh installs official pinned tooling into project-local paths.
scripts/verify.sh removes the project .lake/build and compiles all active proof
modules. Dependency builds/cache are retained and not independently rebuilt.
The recorded clean compilation succeeded (2321 Lake jobs, exit status zero).
All 68 #print axioms commands and all 68 #check statements succeeded.
scripts/check_pins.py verified the compiler commit and all nine dependency
checkout commits with no tracked source modifications.

TRUST AND AXIOMS
The exact axiom list for EVERY theorem is in axiom-report.json and below.
Their union is precisely:
  propext          — propositional extensionality;
  Classical.choice — classical choice;
  Quot.sound       — quotient soundness.
These are standard Lean logical axioms, not an axiom-free proof claim.
No theorem depends on sorryAx, a custom theorem-replacing axiom, or an extra
compiler/native-evaluation axiom. Active sources have no sorry, admit, axiom,
native_decide, unsafe, or implemented_by. norm_num/ring/nlinarith and finite
enumeration construct proof terms checked by Lean's kernel. The source scan is
an additional guard, not the primary mathematical certificate. The primary
evidence is successful Lean compilation plus transitive #print axioms output.
The trust boundary includes the official Lean binary, standard library and
official pinned dependency .olean cache. We did not rebuild Lean/mathlib from
source or run an independent external kernel checker.

UPSTREAM REUSE
OpenAI/math adc7f1241b42e322a6451854ab7e4b4c146bf78a supplied the exact Arithmetic
module, the exact simplexConstant definition (with narrower imports), and the
exact twice_sum_negative_eq_sum_abs statement/proof (with narrower imports).
All four reused theorems compile afresh and pass the same transitive axiom audit.
Their full originals and Apache-2.0 license are included under vendor/openai/.
No challenge file is imported. Only the four compiled finite/scalar
upstream theorems listed above are certified here; upstream geometry is outside
this project's certified scope.

UNFORMALIZED PAPER DEPENDENCIES / REMAINING WORK
- General centered-law A<=B<(d+1)A, simplex support rigidity, support and
  Caratheodory/separation arguments, B-A's outer integral and the d! witness
  factor, arbitrary-law neighborhood arguments, and geometric stability.
- Cone-volume/surface-area/Minkowski identities, projection/cone geometry,
  geometric product/join laws, actual boundary-unit norm construction, and
  integration under even boundary laws. Thus v3 Theorem 6.2 is not fully certified.
- Exposed-point rigidity, cofactor rank arguments, rank-two decomposition and
  full convex-body product classification in v4 Theorem 1.1.
- v5's R recurrence, Robbins/Stirling estimates, infinite logarithmic limit,
  tail control, rational-log/integer global screening, uniqueness and gap.
  Any Python rational verifier in the source repository remains outside Lean.
- Convex derivative/secant order, almost-everywhere domain legitimacy,
  minimum-density integration, translation identities and all transport,
  Sobolev, regularity, moment, and optimal-map estimates in entries001/008.
- Full upstream OpenAI geometric volume/product theorems and identification
  of the explicit simplexConstant with a geometric invariant.

These are mathematical scope boundaries, not installation or build blockers.
All supplied finite/scalar identities have proofs; none is supplied merely as
an implication from an assumed geometric identity. The conditional cofactor
corollaries and geometric applications are explicitly distinguished above.

THEOREM-BY-THEOREM MAP
The following includes every exported theorem. Helpers are explicitly labeled
and are not counted as separate published paper lemmas. Every exact signature
records all formal assumptions and typeclass requirements. Paper source paths,
commits and snapshot hashes are in references/SOURCES.json; all application
gaps are also repeated per theorem in coverage.json/coverage.csv.
'''
parts = [intro]
for index, e in enumerate(out, 1):
    parts.append(f"\n{index}. {e['name']}\n"
                 f"Source: {e['source']}\n"
                 f"Paper: {e['paper_statement']}\n"
                 f"Coverage: {e['coverage_kind']}\n"
                 f"Meaning: {e['description']}\n"
                 f"Assumptions: {e['assumptions_summary']}\n"
                 f"Axioms: {', '.join(e['axioms']) or '(none)'}\n"
                 f"Exact Lean signature:\n{e['exact_lean_signature']}\n")
(ROOT / 'COVERAGE_REPORT.txt').write_text(''.join(parts))
print(f'Coverage report, CSV and JSON generated for all {len(out)} exported theorems.')
