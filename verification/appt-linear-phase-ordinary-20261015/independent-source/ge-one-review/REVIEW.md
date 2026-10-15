# Independent ordinary review: exact pure envelope for c >= 1

Decision: **PASS for the exact source and scope below.** This is a full internal AI-agent mathematical read, with separately written diagnostics. It is not Lean verification, external human peer review, a priority certificate, or a new major-problem count. No independent mathematical finding remains open for this source.

## Bound source and actual read

The complete manuscript `PURE_ENVELOPE_GE_ONE.md` was read, including the original quantum paragraph and exclusions. Its SHA-256 is `ad1a5aabca9d3fcf2e960cbf43bcf7cfbdfd232cc58b86bbaf355229656016a9` (6535 bytes). The Windows copy and the author's WSL source were byte-compared before review; the private literal copy and `INPUT.json` retain those inputs. The historical author banner is preserved, not rewritten as a current review decision.

The mathematical dependencies are the previously fully read, unchanged L1/L20/L21 scalar-value calculation and the full actual-matrix criterion S. The credited files copied here are bound to immutable main `c4e0d9e713ba349d376469231789bb7b36915b7d`; their source hashes, prior reports and final status binding are recorded in `INPUT.json`. In particular, L is `49b33ee7edb2e326619a144f4343e78d896c47cfe4d9e524c16cd6790a0e001d`, the published S text is `6ae480fc6d67c4b138e852c68529f81b9e39923828eb0c13d15cced5e439ab54`, and V is `7b9846a394673aee0fe97a1f0b7b2c01a197ab6b3e9854fac7201e0eb562b269`. These earlier complete reads were reused after byte comparison; they are not described as newly repeated full audits. L20 and the exact S hypotheses were checked again for this transfer. V already supplies the complete all-order value scope and is credited rather than claimed anew.

The old T v2 PASS only covered the sufficient bound c >= 10. It was frozen separately and supplies no automatic validation of the new interval 1 <= c < 10. This report reviews the new argument directly. No author checker was imported or executed.

## Mathematical assessment

**Statement and boundaries.** For every real c >= 1 and every real r >= 0, the result is the exact scalar equality

    F_*(c,r) = max{b(2c), 1+r}.

For r below b(2c)-1 the only maximizing pair is (2,h_b(c)); at equality it is that pair together with the entire redundant face {0} x [0,1]; above it the face alone remains. Both mixing endpoints and both width endpoints are included. This is a scalar statement, not an exact finite-dimensional quantum optimizer theorem.

**The one-variable inequalities have the required strength.** Differentiating the explicit functions gives q'=-sq and g'=s(1-q)>0. The proposed multiplication in the proof gives exactly H(t)=(t-2)e^t+t+2. Its two initial zero values and H''(t)=t e^t>0 prove s(t)>1/2 for every t>0, rather than merely an asymptotic bound. For each fixed h, the centered Bernoulli log moment-generating function is convex in t; its pointwise maximum is g. The explicit formula is differentiable on t>0. Thus g(K)-g(k) >= (K-k)g'(k) is the correct convex tangent inequality. Neither monotonicity alone nor an interchange of arbitrary maximizers and derivatives is used.

**Interior contradiction is global and remains strict at c=1.** At r_0=b(K)-1, K=2c, any putative global maximum at 0<L<2 has h strictly between 0 and 1: at h=0 or 1, B=1 and P<1, so its value is strictly below b(K). With k=cL, u=K-k and a=2k^2/(3u), the L20 eliminated formula is valid on a neighborhood of this interior mixing maximum. Its log value is g(k)+T, T=r_0 q(k)e^{-a}>0, and width stationarity gives g'=T(s+a'). The height and tangent inequalities therefore imply 1 >= u(s+a').

I independently checked a'=2k(2K-k)/(3u^2) and the exact strict bound

    u(s+a') > K/2 + (K-u)(4K+u)/(6u) > K/2.

Every factor in the last term is strictly positive for 0<u<K. Consequently even K=2 contradicts the stationarity/height inequalities. No uniform positive numerical margin is required as k tends to zero. Compactness of the original continuous F on the closed rectangle guarantees a global maximum: any interior point at or above b(K) would be, or force, an interior global maximum. This excludes all hidden interior ties as well as larger values. The use of L20 is conditional on an actually interior mixing maximizer; the proof never applies its formal interior expression after it leaves the admissible h interval.

**All r and all equality cases.** For r<r_0, the affine interpolation between B and F at r_0 bounds the value by b(K), and equality forces the unique pure-bulk maximizer because the coefficient of B is positive. This includes r=0. For r>r_0, the identity

    F_r-(1+r) = [F_r0-b(K)] + (r-r_0)(P-1)

is nonpositive and is strictly negative at every positive width, including L=2. The zero-width face attains equality. These steps prove the complete claimed argmax, without relying on a grid or a local stationary ansatz.

**Actual quantum transfer.** The consequences retain complex PSD trace-one density matrices and PPT after every global unitary. The limiting statement is for all sequences of integers 2 <= m <= n, m -> infinity, alpha>1, alpha/m -> a fixed c >= 1 and 3^alpha/(mn) -> a finite r >= 0. L1 continuity permits approach to c=1 from either side; no eventual alpha/m>=1 restriction was added. The full S near-optimizer equivalence uses distance to the explicit *entire* argmax set and retains both the middle chord/spread loss J and the actual peak loss. The pure-bulk width 2 does not acquire an interior-width peak expansion. Nothing here substitutes a body-law condition for the positive-r physical losses.

The source does not establish a sharp c threshold, connectedness of the set of mixed c values, uniqueness of an intermediate c transition, exact finite optimizers/eigenbases, absolute separability, or all-order spectral rigidity. Those are not consequences of this PASS.

## Independent diagnostics and preserved controls

`independent_checks.py` was written for this new scope without importing or executing author code. Its sole execution is `runs/20261015T115138.015288Z`, status PASS, using Python 3.10.12, Sympy 1.9, Mpmath 1.2.1 and 500 decimal digits. The script SHA-256 is `09893a1367538855073da000d8d348fc3b0502c7d4df6c4e67cac5917eeba86a`; the result SHA-256 is `a1d1004c078eed0cba8aab2ec00953aadde6db64999ae83fba8a48b85f000506`.

The execution records eight exact symbolic identities, sixteen rational strict-bound cases including K=2, twenty-four convex-tangent diagnostics, and 900 finite profile cases that include c=1, moving widths near 0 and 2, h endpoints, and threshold ties. Numerical endpoint attainment checks are also retained. These are supporting diagnostics; the written compactness and contradiction argument proves the full real-parameter scope.

Six intentionally false assertions actually raised AssertionError and were caught and recorded with witnesses: reversing the convex tangent inequality; replacing the strict c=1 bound by equality; extending the theorem to every positive c; using the interior eliminated value for a negative formal h; dropping a' from the contradiction; and removing the positive-r physical peak loss. The c=0.01 mixed witness exceeds both pure values by about 6.20e-6. The last witness is the actual maximally mixed all-global-unitary APPT state at alpha=m and 3^alpha/D approximately 1: it has the pole body law and zero spread but peak slack approximately 1, so its moment 1 is not the pole optimum approximately 2. These countercontrols test specific wrong conclusions; they do not supply the global proof.

There was no unexpected failure in this new independent execution. The executed script and full result are retained. The earlier T v1 definition finding and the author's separate T numerical-precision failure remain in the frozen T evidence and have not been deleted, relabeled as this scope's failures, or hidden by this new PASS.

## Scope of evidence

The bounded official abstract/version-page collision screen already performed for T is not extended into a new full-text or priority audit here. No absence-of-literature conclusion is inferred. This report gives no assurance about later publication layout, figures, transport, CI, or root state. No Lean command, new audit root, submission, repository mutation, or subagent was used. Final publication metadata and index binding remain a separate task.
