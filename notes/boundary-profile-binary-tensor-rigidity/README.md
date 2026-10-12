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
\(p\ge10\). Its later mechanism-optimality theorem shows that this two-band
constant is best among fixed-width palindromic profiles whose coordinate
axes remain local projection maxima. The profile here satisfies the exact
opposite inequality
\[
 \gamma_1^2+\sqrt2\,\gamma_2
 =\frac{12346629}{9765625}>1,
\]
so it escapes that axis-local class and supplies the more general off-axis
asymptotic profile mechanism. The upper constant \(2^{-1/2}\) remains
unchanged.

A later [Fock-profile ceiling continuation](../fock-profile-ceiling-binary-tensor-rigidity/README.md) completes the natural finite-first-moment profile space, proves attainment of its variational optimum, raises the rigorous tensor lower endpoint to \(0.6238973\), and gives the mechanism ceiling \(\kappa_{\rm prof}\le\sqrt{779/2000}=0.624099351\ldots\). This ceiling is for the reflected boundary-profile mechanism only; it is not an upper bound for the true tensor constants.


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
