# Final theorem-scope and verification audit

This is a source-level mathematical-scope audit of the exact checked package,
not an external human peer review or a historical-priority certificate.

## Actual domain and data

The all-rate polynomial statements use an independently given finite
SimpleGraph G with G.IsTree, an inlet/state-observer vertex o, one leak vertex
ell, and the exact original directed-edge rates plus the external leak rate.
The graph presentations are constructed from the finite cardinality and tree
hypotheses. The coefficient map uses the actual compartment matrix's unreduced
characteristic polynomial and original observed principal cofactor. Its monic
leading constants are omitted and its remaining coordinate order is fixed.

The main polynomial identities quantify ALL real rate vectors: negative and zero
rates, a zero leak coefficient, repeated spectra, zero resultants, and the
one-vertex model are included. No positivity, nonzero rate, eigenvalue simplicity
or regular-Jacobian hypothesis occurs in the final statements.

## Independent Jacobian construction

formalLocatedJacobian is the determinant of formal partial derivatives of the
actual multivariate coefficient polynomials, independently of the proposed
factorization. formalLocatedJacobian_evaluate proves equality with the actual
Frechet Jacobian for every real vector. The proposed factor polynomial is built
from actual principal matrices, edge products, and squared sibling resultants.

The positive-domain relocation identity is only an intermediate lemma. Actual
cofactor/determinant conservation removes every transformed parameter and
denominator before polynomial extensionality is used on a product of positive
half-lines. Infinite-coordinate-set extensionality proves polynomial equality;
no incorrect assertion that the positive orthant is dense in all real space is
used. Thus zero-boundary values are not obtained by division at zero.

## Exact factor, orientation and nondivisibility

The sign is exactly +1 or -1 in the chosen observation-coordinate convention,
and the same sign works for all leak sites and all real rates. The monomial
contains one rate per edge pointing toward the leak and, in each direction,
the observed-root subtree size minus one. Original graph dart coordinates,
not a substituted set of transformed rates, are used for the exact powers.

Every coordinate hyperplane admits a proved witness at which the actual sibling
residual is nonzero. The leak-root triangular order is pulled back to each
observation-root principal set; its distinct diagonal values give coprime sibling
polynomials. This witness works for every coordinate and every finite model.
Polynomial primeness and multiplicity then prove the stated power divides the
formal determinant and the next power does not. The external leak variable has
multiplicity zero. Collocated-leak specializations recover the earlier exponents.

The zero-set criterion is algebraic for signed real parameters. It is not
indiscriminately stated as a real-spectrum condition outside the positive class.

## Original full-response and ODE scope

Exact finite fiber counts require a target with as many distinct positive poles
as model vertices and positive normalized Stieltjes weights. The competing real
rates have no imposed sign or regularity restrictions; positivity and regularity
are conclusions. Finiteness is proved before cardinality, so Nat.card cannot
hide an infinite fiber. Original labels are retained, pole permutations inside
one block are not counted twice, and unknown-leak multiplicity is justified by
actual site/matrix injectivity.

ODE predicates refer to actual classical solutions for continuous real inputs.
Global existence/uniqueness is constructed. The converse history-to-transfer
proof uses explicit solutions, preventing a vacuous universal solution predicate.
Signed endpoint steering and minimum energy are proved using a genuinely
positive integral Gramian; arbitrary nonnegative-rainfall steering is not claimed.

Collocated state observation at o must not be confused with physical discharge
at a different leaking vertex ell. Off-diagonal transfer identifiability is not
silently asserted. Nonlinear catchments, noisy inference, impulsive/measurable
forcing and fewer-mode or complex-rate fiber enumeration remain outside scope.

## Boundary sanity distinction

For a two-vertex model with input/observer at 0 and leak at 1, write f for 0->1,
a for 1->0 and lambda for the leak. Then

    A=[[-f,a],[f,-a-lambda]],
    P(s)=s^2+(a+f+lambda)s+lambda*f, F_0(s)=s+a+lambda.

With coefficient order (P_0,P_1,F_0) and parameter order (lambda,a,f), the
Jacobian matrix [[f,0,lambda],[1,1,1],[1,1,0]] has determinant -f. At a=0 and
f nonzero that determinant is still nonzero although the observed fraction
cancels to 1/(s+f). This is not a full two-mode target. The formal statements
correctly distinguish an unreduced coefficient Jacobian from identifiability of
every cancelled boundary response. These elementary identities illustrate the
semantic distinction; they are not substitutes for the universal Lean proof.

## What the verification establishes

Each exact source checkpoint is built in a new Lake tree with zero owned
objects and separately compiled again. Every audited root's complete used
closure is rechecked in an empty kernel at trust level zero, rejecting unsafe,
partial and nonstandard-axiom dependencies. Only propext, Classical.choice and
Quot.sound are allowed. Root types and universe parameters are compared.
The replay metaprogram itself is not introduced as a mathematical axiom.

Negative controls are deliberate SOURCE mutations: wrong constants, exponents,
formulas, or proof-defining inputs. Their rejection means the modified source
is not accepted as a proof. It is not claimed that every altered proposition
is itself logically false; for example, changing a witness's designated zero
coordinate to one tests whether its original proof is improperly reused.
Separate exact-factorization and next-power mutations do assert false formulas.

Newly hashed scope documents and the dependency graph are bound to the same
source manifest as the proof and reproduction script. The older runs' stale
human-readable scope labels do not silently certify later sources; the final
scope-bound report and its actual root list are authoritative for this package.
No claim about novelty, external peer review or real-catchment performance follows
from a successful Lean kernel replay.
