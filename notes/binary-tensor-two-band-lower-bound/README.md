# Improved two-band lower family for binary tensor rigidity

Research note, 7 October 2026.

This note strengthens the lower-bound side of the binary complete-commutator
rigidity problem from
[sharp-binary-tensor-rigidity](../sharp-binary-tensor-rigidity/README.md).

For every tensor order p >= 10 we give an explicit symmetric binary tensor
whose exact orthogonal-decomposition distance and complete contraction
commutator residual can both be computed in closed form.  The resulting
asymptotic lower constant is

\[
\kappa=
\sqrt{\frac{2+\sqrt2}{2(3+\sqrt2)}}
=0.6218758237538317\ldots,
\]

strictly improving the previously published one-band constant
\(2^{-3/4}=0.5946035575\ldots\). Combined with the existing upper bound,
this note by itself gives

\[
0.6218758237\ldots
\le \liminf_{p\to\infty}\frac{C_p}{p^{1/4}}
\le \limsup_{p\to\infty}\frac{C_p}{p^{1/4}}
\le 2^{-1/2}=0.70710678\ldots .
\]

The complete proof is in [paper.md](paper.md).  It is analytic: the key
projection maximum is proved separately for even and odd p by coefficient
domination and a sign argument.  The exact checker is diagnostic rather than
a substitute for the universal proof.

## Reproduction

Python 3.10+ and only the standard library are required.

~~~~sh
python3 verify.py
~~~~

The verifier runs the checker normally and with Python optimization enabled
and requires byte-identical stdout.  The checker uses exact arithmetic in
Q(sqrt(2)), replays orders 10 through 120, checks the integer inequalities
used to pass from finite formulas to all p >= 10, and includes negative
controls.

See [PROOF_AUDIT.md](PROOF_AUDIT.md) for the claim-by-claim trust boundary and
[results/exact-checks.txt](results/exact-checks.txt) for the recorded replay.

## Scope

This note does **not** prove that \(C_p/p^{1/4}\) converges, determine its
optimal leading constant, classify all higher-order extremizers, or improve
the parent upper bound.  No novelty or priority claim is made.  There is no
external human peer review or whole-paper formalization.


## Mechanism-level optimality

The same proof now shows more than a single improved example.  Among every
fixed-width palindromic boundary-band family whose coordinate axes remain
local projection maxima, the normalized witness constant is asymptotically
at most \(\kappa\).  Equality in the limiting profile optimization forces
\(\gamma_1^2=1+\sqrt2\), \(\gamma_2=-1\), and all higher boundary-band
profiles to vanish.  The explicit tensors in this note attain that profile.
This does not rule out wider, non-palindromic, or non-axis mechanisms.

The subsequent
[boundary-profile continuation](../boundary-profile-binary-tensor-rigidity/README.md)
realizes the last route explicitly. Its three-term fixed-width palindromic
profile has
\[
 \gamma_1^2+\sqrt2\gamma_2
 =\frac{12346629}{9765625}>1,
\]
so the coordinate axis fails the necessary local-maximum condition above;
the projection maximum moves off-axis. That continuation historically raised the
repository lower endpoint to
The later [Fock-profile ceiling continuation](../fock-profile-ceiling-binary-tensor-rigidity/README.md) raises the current tensor liminf lower constant above 0.6238973 and nearly localizes the optimum of the full reflected-profile mechanism.
\(\liminf C_p/p^{1/4}>0.623586\). Thus the mechanism-optimality statement
here remains sharp on its stated axis-local class.
