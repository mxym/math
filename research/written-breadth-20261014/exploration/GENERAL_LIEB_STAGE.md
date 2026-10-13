# General Lieb counterexample attempt: bounded stage record

14 October 2026, Asia/Shanghai. Internal assistant `/root/written_breadth`.
Status: **exploration; no general theorem or counterexample obtained**.

The target is the complete original subgroup inequality
[
 sum_{sigmain H}chi(sigma)prod_i A_{i,sigma(i)}
 le chi(e),operatorname{per}A
]
for arbitrary order, subgroup and character, and actual Hermitian PSD matrices.
A counterexample of one finite order would refute the complete claim.
A positive result in one rank, order or subgroup would not be counted as the
requested general solution.

The conjecture statement and normalization were read in [Wanless's primary
survey](https://arxiv.org/pdf/2202.01867v1), Conjecture 1. Current original
author reports and preprints establish general order four and large ordinary
immanant ranges, while retaining the general subgroup problem. The older
permanent-on-top and Bapat–Sunder counterexamples do not themselves refute this
statement. [Current author status](https://yair-lavi.com/mincs-list/conjecture-42/index.html).

## Actual discovery work

All discovery matrices are formed as (A=XX^*), with row normalization used
only for scale-invariant ratios. The numerator uses the actual subgroup
permutation sum and divides by the character degree. No surrogate PSD
constraint, PPT relaxation or finite-state replacement is used.

1. Seven degree-one classes at order five: (C_5), (D_{10}), and
   (operatorname{AGL}(1,5)). An analytic gradient was independently checked
   by central finite differences. 168 bounded optimization starts across
   embeddings of ranks 2–5 produced no ratio above one.
2. Alternating split-hook characters for (A_5,A_7), and the standard
   (operatorname{GL}(3,2)) character rows in its actual seven-point action.
   Character orthogonality, group-order/class-size consistency and objective
   gradients were checked. 93 starts produced no ratio above one.
   Character-table consistency is not a substitute for a final proof of
   character legitimacy if a witness were found.
3. (S_2\wr S_3\le S_6) with the two trivial-top linear characters.
   The trivial-bottom row is exactly Marcus's permanent-of-block-permanents
   statement: a counterexample would also refute general Lieb. 120 bounded
   starts included small complex perturbations of the rank-three block
   equality configurations. No ratio above one was found. The current
   [Marcus author report](https://yair-lavi.com/mincs-list/conjecture-9/index.html)
   already covers the rank-two three-block case; it is excluded from new
   positive-result claims.

The three machine reports retain seeds, scopes, actual Gram rows and outcomes.
They do not prove any universal dominance inequality. The programs completed
naturally; no process was left running at stage close.

## Analytical obstacles actually checked

Diagonal normalization preserves the ratio. If dominance is already known for
all smaller orders, every principal-diagonal derivative of the defect is
nonnegative: it is the corresponding smaller-order defect for the restricted
character on the stabilizer. Subtracting a scalar identity to the PSD boundary
therefore cannot increase a negative defect. This is a conditional boundary
reduction, not an induction proof or a new solved problem.

In the three-pair Marcus equality neighborhood, take actual paired rows
(u_{a,pm}=e_apm t v_a), (a=0,1,2), with
(v_a\perp e_a). Their block polynomials are
(P_a(z)=z_a^2-t^2(v_a\cdot z)^2). The product Fischer norm is the actual
six-row permanent, and the permanent of the Fischer Gram of the three
quadratics is the actual block-permanent numerator. Writing
[
 T=sum_{a\ne b}|(v_a)_b|^4,qquad
 U=sum_a |(v_a)_b(v_a)_c|^2
]
with ({b,c}={0,1,2}\setminus{a}), direct coefficient bookkeeping gives
the first defect term
[
 operatorname{per}A-operatorname{per}G
   =t^4(32T+128U)+O(t^6).
]
The cross phase term (16\operatorname{Re}sum_{a<b}
(v_a)_b^2(v_b)_a^2) occurs on both sides and cancels.
Thus this ansatz is locally blocked in every nonzero transverse direction.
It is not a proof of Marcus or Lieb away from the equality neighborhood.

No mechanism was found that converts a high noncentral Schur-power eigenvalue
into a valid subgroup-character violation. Trace/character normalization
cannot be dropped to turn an old permanent-on-top witness into a Lieb witness.

## Excluded follow-up targets from current primary screening

The sharp nonnegative permanent critical exponent is already resolved by
[Bristiel–Caputo](https://arxiv.org/abs/2109.06009), so it is not a new target.
The full Duval–Reiner majorization assertion already has July 2026 primary
counterexample manuscripts ([2607.20051](https://arxiv.org/abs/2607.20051),
[2607.20910](https://arxiv.org/abs/2607.20910)); no attack was started.
The Dittert conjecture has public all-dimension assembled and direct proof
claims, so it is also excluded pending actual identification of a substantive
gap. These are status checks, not independent certifications of those entire
proofs.

Current screening also located public September real counterexample claims
for both the Drury permanent inequality and the first-compound eigenvalue
variant. Those would not be suitable fresh targets merely because the older
surveys called them open. Their complete prior packages have not been audited
here.

## Continuation

The automatic interruption interval is excluded from the failure-window
accounting; elapsed calendar time during that interval is not active research.
This bounded stage closes with an actual analytic obstruction and finite
discovery records, rather than a positive theorem or an importance rating.

At this natural boundary the root's growing-order APPT package will receive
the requested independent mathematical review. That review is service work,
not a new breadth direction. Substantive general-problem research continues
after it; no Lean scope, external publication or remote push is added.
