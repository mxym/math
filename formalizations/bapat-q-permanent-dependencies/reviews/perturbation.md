# Internal semantic review of the Bapat perturbation endpoint

Date: 2026-10-08. This is an internal AI-assisted mathematical and statement review; it is not external professional peer review or a second kernel replay. I read the four final public source files listed below, with the existing actual-qPermanent definitions and the non-diagonal helper, and compared their quantified inputs and conclusions with Sections 2 and 5 of the finite complex-Hermitian counterexample.

## Source identities

- `EndpointBridge.lean`: `9792607d1ad45a4b3ae370256cb71caf324ce22599e610bc62fd3eda510444d8`
- `PositiveDefiniteViolation.lean`: `79e3552258e3a7cac502555d37a4ee88659e4fa05b864377be007a9bb81fd772`
- `CounterexampleTransfer.lean`: `6cf87f652c06bcaf1d09f04865af70c41d6d468ac55493e8eed5670c03f18e6f`
- `DimensionBounds.lean`: `009225d1042caecb6bf572a11cb4b76bdd044589fbb6635c8724f9d0c95d9fb1`

## Findings

No substantive statement mismatch or mathematical gap was found in the inspected transfer chain. `EndpointBridge` identifies the finite real polynomial with the real part of the actual inversion-weighted qPermanent, using the actual permutation weights, and identifies its derivative at one with the actual endpointDerivative. The entry bound is applied to every actual permutation product, and the perturbation estimate uses the true inverse-count bound `n.choose 2`. The exponent-zero and exponent-one cases remain in the finite polynomial theorem rather than being implicitly discarded.

`PositiveDefiniteViolation` takes an actual rectangular complex matrix V. It constructs the Gram matrix V V*, perturbs it by the positive real epsilon times the identity, and derives actual Matrix.PosDef. The hypothesis on the unperturbed actual endpoint is Re P'_1 <= -1/2. The finite-product bound makes the perturbation error at most 1/4, giving Re P'_1(B) <= -1/4. Its non-diagonal conclusion is obtained from the actual negative endpoint, not supplied as a new assumption. The interval constant K and q0=1-1/(8K) are the stated explicit ones; the proof proves 0<q0<1 and the strict reverse inequality for the actual qPermanent real parts.

`DimensionBounds` derives all two size hypotheses from n>=3 and R>=0: choose(n,2)>=3, choose(n,2)-1>=1, n!>=1, n>=1, and (R+1)^m>=1. It does not hide a positive lower-bound assumption about the witness matrix. The use of a real bound R is consistent between the unperturbed entry bound and the perturbed radius R+1.

`CounterexampleTransfer` instantiates those bounds and produces an actual positive-definite non-diagonal complex matrix, with an actual q0 in (0,1). The two arguments used to contradict MonotoneOn belong to the original Icc(-1,1), and q0<=1. The orientation of the strict reverse inequality is correct. The actual Hermitian reality result supplies the interpretation as the original real-valued qPermanent for this positive-definite matrix; taking real parts in the formal monotonicity predicate does not change its values on the real axis.

## Scope boundary

The negative input endpoint remains explicitly assumed. Neither this theorem nor the reviewed package proves that an input V satisfying that hypothesis exists. In particular, the Gram/Bargmann correspondence, the polynomial recurrence semantics, the order-200 integer calculation and the resulting negative endpoint must still be connected before claiming complete formalization of the counterexample. The reviewed statements are genuine universal transfer results, not the existence theorem in disguise.
