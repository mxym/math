# Boundary-profile lower bounds for binary tensor rigidity

This additive continuation of the sharp-binary-tensor-rigidity note proves a
general boundary-layer limit theorem for the sharp binary constants \(C_p\) in

\[
\operatorname{dist}_F(T,\mathrm{ODeCo}_{2,p})
\le C_p\sqrt{R_p(T)}.
\]

For every finite coefficient profile \(a_0,\ldots,a_m\), the theorem turns
the asymptotic tensor quotient into the explicit one-variable quantity

\[
\frac{
2S-\sup_x e^{-x^2}(A(x)^2+A(-x)^2)}
{4\sqrt{SM_1}},
\qquad
A(x)=\sum a_kx^k/\sqrt{k!}.
\]

An exact three-term profile then proves

\[
\liminf_{p\to\infty}\frac{C_p}{p^{1/4}}>0.623586,
\]

improving the parent note's \(2^{-3/4}=0.59460\ldots\) lower constant and
the concurrently published exact two-band constant
\(\sqrt{2/7+\sqrt2/14}=0.6218758237\ldots\). The concurrent note retains
the stronger finite-order feature of an exact closed witness for every
\(p\ge10\); this note supplies the more general asymptotic profile theorem.
The upper constant \(2^{-1/2}\) remains unchanged.

Complete proof: paper.md

Exact rational checkers: checks/check_exact.py and
checks/check_independent.py

Proof audit: AUDIT.md

Reproduce with Python 3.10+:

    python3 -B checks/check_exact.py
    python3 -B -O checks/check_exact.py

The checker uses only fractions.Fraction and integer arithmetic for proof
decisions. It verifies the unique critical-point bracket, the alternating
exponential upper bound, and the final rational inequality proving
0.623586. The asymptotic passage from tensors to the profile problem is
proved analytically in paper.md; finite numerical sampling is not used as
proof.

This is AI-assisted research with model self-review, not external peer
review or proof-assistant formalization. No novelty-priority claim is made.
