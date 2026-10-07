# Fock-profile ceiling for binary tensor rigidity

This note completes a substantial part of the boundary-profile program for the
sharp binary complete-commutator tensor constants.

Let

\[
S(a)=\sum_{k\ge0}a_k^2,\qquad
H(a)=\sum_{k\ge0}k\,a_k^2,
\]

and

\[
A_a(x)=\sum_{k\ge0}\frac{a_k}{\sqrt{k!}}x^k,\qquad
M(a)=\sup_{x\in\mathbb R}e^{-x^2}\bigl(A_a(x)^2+A_a(-x)^2\bigr).
\]

For nonzero profiles with \(0<H(a)<\infty\), define

\[
Q(a)=\frac{2S(a)-M(a)}{4\sqrt{S(a)H(a)}}.
\]

The preceding
[boundary-profile theorem](../boundary-profile-binary-tensor-rigidity/README.md)
shows that every finitely supported profile gives

\[
\liminf_{p\to\infty}\frac{C_p^2}{\sqrt p}\ge Q(a).
\]

This continuation proves:

- finite profiles are dense for this variational problem, and the supremum is
  attained in the square-summable finite-first-moment completion;
- the full profile optimum \(\Lambda_{\rm prof}=\sup Q(a)\) satisfies the
  exact certified window
  \[
  \left(\frac{6238973}{10^7}\right)^2
  <\Lambda_{\rm prof}\le\frac{779}{2000};
  \]
  equivalently,
  \[
  0.6238973<\kappa_{\rm prof}:=\sqrt{\Lambda_{\rm prof}}
  \le\sqrt{\frac{779}{2000}}
  =0.6240993510\ldots;
  \]
- consequently the tensor lower bound improves to
  \[
  \liminf_{p\to\infty}\frac{C_p}{p^{1/4}}>0.6238973;
  \]
- at a profile maximizer with a unique active Gaussian scale, the Euler
  equation is a number operator plus two coherent-state rank-one
  perturbations.  Under the stated nondegeneracy assumption, its even and odd
  coefficients satisfy explicit resolvent equations.

The upper endpoint above is a ceiling for the **reflected boundary-profile
mechanism**, not an upper bound for the true sharp tensor constants.  The
current general tensor upper constant \(2^{-1/2}\) is unchanged.  Thus this
note also proves that closing the full tensor gap requires either a sharper
global upper argument or lower constructions outside this boundary-profile
class.

The lower endpoint uses an explicit five-term rational Fock polynomial.  The
upper endpoint is an infinite-dimensional quadratic-form certificate reduced
to two rank-one Schur complements and 28 rational parameter intervals.  All
proof decisions in the checker use Python standard-library
\`fractions.Fraction\`; the exponential bounds are alternating Taylor
inequalities and positivity on each parameter interval is certified by exact
Bernstein coefficients.

- [Complete proof](paper.md)
- [Exact checker](checks/check_exact.py)
- [Proof audit](AUDIT.md)

Reproduce with Python 3.10+:

~~~sh
python3 -B checks/check_exact.py
python3 -B -O checks/check_exact.py
~~~

The proof is mathematical; the checker only replays the finite rational
arithmetic certificate used in the lower witness and the dual ceiling.  No
floating-point comparison, numerical optimizer, external solver, or random
search is used for any published decision.

This is AI-assisted research with model-conducted self-review.  It has not
received external human peer review or complete proof-assistant
formalization.  No first-discovery or priority claim is made.
