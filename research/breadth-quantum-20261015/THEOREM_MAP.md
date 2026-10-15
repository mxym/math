# NPT bound entanglement: full-target map N0

15 October 2026 (Asia/Shanghai). Author: Yongxian Zhang (张永贤), South
China University of Technology. No external funding. OpenAI AI assistants
assisted. Original material: all rights reserved. External inputs retain
their original attribution and license. Written research only; no Lean
claim, submission, priority certification, or major solution is asserted.

## Complete target

N0 asks whether there are finite integers d_A,d_B >= 2 and an actual
density matrix rho >= 0, Tr rho = 1 on C^{d_A} tensor C^{d_B} such that

  rho^{T_B} is not positive semidefinite, and
  for every integer k >= 1 and every collective Schmidt-rank-at-most-two
  vector psi in (C^{d_A})^{tensor k} tensor (C^{d_B})^{tensor k},
  <psi,(rho^{T_B})^{tensor k}psi> >= 0.

An affirmative answer must supply ONE fixed finite state and ALL copy
numbers. A negative answer must cover EVERY finite-dimensional NPT state,
with a finite-copy Schmidt-rank-two negative witness allowed to depend on
the state. A family depending on k does not supply the fixed state.

## Equivalent reductions and stronger sufficient targets

The finite-copy Schmidt-rank criterion and the NPT-to-Werner reduction
are attributed external inputs. The reduction is existential/asymptotic;
it does not preserve the same finite-copy distillability threshold.

Use the Werner state rho_{d,lambda}=(I-lambda F)/(d^2-lambda d).
The possible hard region is d >= 3 and 1/d < lambda <= 1/2.
For a coefficient operator C on (C^d)^{tensor k}, define

  Q_k(lambda,C)=sum_{J subset [k]}(-lambda)^{|J|} ||Tr_J C||_HS^2.

For each fixed d,lambda,k, this state is k-undistillable exactly when
Q_k(lambda,C) >= 0 for ALL operators of rank at most two. A proof that
Q_k(1/2,C) >= 0 for every k, C and ONE fixed d >= 3 would answer N0
affirmatively. This endpoint statement is stronger than N0: one endpoint
negative witness refutes that route, not the existence problem. A full
negative answer must instead handle all d and all lambda in the hard
region, together with the external reduction.

## Gates that a complete proof must close

N1. Current-primary collision check, including older full-domain proof
claims, and an actual reason for adopting or excluding each claim.
N2. The actual physical state, its NPT property, and correct normalization.
N3. Every k with a fixed state, including arbitrarily large k. No bounded
copy, tensor-factorized, normal, PSD, qubit-support, or rank-three substitute.
N4. Every rank-at-most-two COMPLEX coefficient operator, with collective
input/output Schmidt rank; no normality, sparse support, or product-vector
restriction silently introduced.
N5. A valid global nonnegativity certificate or a full-domain distillation
theorem. Necessary relaxations, failed shortcuts, and finite searches do
not by themselves close this gate.

## Primary collision screen before own main research

The 2026-07-23 through 2026-07-27 public manuscripts on TWO-copy Werner
distillability are prior work, not this stage's target. The 2026-07-31
three-copy manuscript arXiv:2608.02647 covers stated normal/PSD/support
sectors and explicitly leaves the general crossed-Gram obstruction.
The updated 2026-10-05 arXiv:2608.08836 refutes an all-parameter conjecture
inside a canonical two-parameter family, not full NPT bound entanglement.
It explicitly describes the original full problem as unresolved.

The old arXiv:0910.0744v2 asserts a full negative answer. Its complete
displayed mathematical argument was read. A direct physical Werner
control contradicts its asserted Eq. (25) for its own parity-projection
vector (details and exact arithmetic to be preserved in this packet).
This excludes that specific argument, without claiming a new result about
the original existence problem or priority for the gap.

Read limits, exact source versions, and searches belong in SOURCES.json.
This is a bounded primary check, not an exhaustive literature guarantee.

## Stage policy

User explicitly resumed on 2026-10-15 and authorized two breadth agents.
This quantum role does not create agents. Its isolated prefix is this
directory. Old closed stages, Gaussian changes, root indices, and Lean
audit scopes remain untouched. Budget is approximately 7200 EFFECTIVE
research seconds per complete stage. Preservation, context recovery,
disconnection and idle time are excluded. A failed shortcut or finite
non-counterexample search does not justify an early stop/switch.

Initial classification: N0 open in this packet; new major solutions = 0.
