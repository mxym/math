# Audit: Fock-profile ceiling for binary tensor rigidity

Date: 7 October 2026

Scope: notes/fock-profile-ceiling-binary-tensor-rigidity

This audit records what was independently re-derived before publication and
what remains outside the proof.

## Statements checked from first principles

1. **Profile convention.**  The continuation uses the preceding
   finite-boundary theorem with actual profile coefficients \(a_k\) and Fock
   polynomial \(A(x)=\sum a_kx^k/\sqrt{k!}\).  In the new lower witness the
   rational polynomial coefficients \(c_k\) are converted by
   \(a_k=c_k\sqrt{k!}\).  This avoids the most likely normalization error.

2. **Uniform profile continuity.**  The coherent vectors have norm one.
   The displayed Lipschitz estimate for \(M(a)\) follows from two elementary
   differences of squares and is uniform in the real scale \(x\).

3. **Attainment of the profile supremum.**  After normalizing \(S=1\),
   \(M\ge2a_0^2\) gives
   \(Q\le\sqrt H/2\), while \(M\ge0\) gives
   \(Q\le1/(2\sqrt H)\).  A positive maximizing sequence therefore has its
   first moment bounded above and away from zero.  The first-moment bound
   gives uniform \(\ell^2\) tails.  Strong \(\ell^2\) convergence, continuity
   of \(M\), and lower semicontinuity of \(H\) close the compactness argument
   without assuming moment convergence in advance.

4. **Finite-to-infinite completion.**  Truncation converges in both
   \(S\) and \(H\), and the uniform coherent-state estimate gives convergence
   of \(M\).  Hence finite profiles and the finite-first-moment completion
   have the same supremum.

5. **Five-term witness.**  The exact checker reconstructs
   \(P(y)=E(y)^2+yO(y)^2\) from six rational polynomial coefficients.
   Every coefficient of \(P\) is nonnegative.  The critical polynomial
   \(P'-P\) has positive constant coefficient and strictly negative
   remaining coefficients, so it is strictly decreasing on
   \([0,\infty)\) and has one positive root.  Exact rational substitution
   brackets this root between 0.2957298 and 0.2957299.

6. **Exponential certification.**  All exponential decisions use alternating
   Taylor inequalities on arguments below one.  The lower witness ends at an
   even truncation, giving an upper bound for \(e^{-L}\).  The dual
   certificate uses odd/even truncations as lower/upper bounds.

7. **Dual reduction.**  The inequality
   \(K_x+2QtN\succeq(2-2Q/t)I\) implies
   \(2-M\le2Q(tH+1/t)\); setting \(t=H^{-1/2}\) gives \(Q(a)\le Q\).
   The test vector \(x\) is allowed to depend on \(t\), which is sufficient.

8. **Parity blocks.**  \(K_x=v_xv_x^\top+v_{-x}v_{-x}^\top\) splits exactly
   into one even and one odd rank-one update.  The tail diagonal is positive
   because \(d_2>0\), certified by \(8Q^2>1\).

9. **Schur complements.**  With at most one negative diagonal coordinate in
   each parity block, the exact rank-one Schur complement is
   \(d_j+2w_j^2/(1+2\sum_{k\ne j}w_k^2/d_k)\).
   Replacing each positive tail denominator by \(d_2\) or \(d_3\) gives the
   stated sufficient inequalities in the correct direction.

10. **Tail masses.**  The identities
    \(T_e=(1+e^{-2y})/2-e^{-y}\) and
    \(T_o=(1-e^{-2y})/2-ye^{-y}\) were re-derived from
    \(e^{-y}\cosh y\) and \(e^{-y}\sinh y\).

11. **Whole parameter range.**  The exact certificate covers
    \(0.47\le t\le2.10\) by 28 contiguous rational intervals.  On each
    interval, after multiplication by \(t^2\), both sufficient inequalities
    are rational polynomials of degree at most four.  Every exact Bernstein
    coefficient is strictly positive.  Outside the table, \(x=0\) works
    because \(Q(t+1/t)>1\) at both rational endpoints and \(t+1/t\) is
    monotone on the two tails.

12. **Tensor implication.**  The new mechanism ceiling is not confused with
    an upper bound for the true tensor constants.  The tensor consequence is
    only the improved lower bound obtained by taking the supremum over the
    already-proved finite-profile theorem.

## Exact replay

Run:

~~~sh
python3 -B checks/check_exact.py
python3 -B -O checks/check_exact.py
~~~

The script uses only Python's standard library.  Proof decisions use
fractions.Fraction and integer arithmetic.  No decision depends on a float,
a random seed, numerical optimization, a symbolic algebra package, an
external solver, or an assertion removable by Python optimization.

The expected summary is:

~~~text
PASS exact five-term profile witness
S = 1846350870529/500000000000
H = 1567622847647/500000000000
certified kappa_profile > 0.6238973
PASS exact full-profile dual ceiling
certified Lambda_profile <= 0.3895
certified kappa_profile <= 0.624099351065197
~~~

The last printed upper decimal is only a human-readable conversion of the
exact rational bound \(779/2000\).

## Explicit limitations

- The note does **not** prove that reflected boundary profiles contain all
  asymptotic tensor extremizers.
- It does not determine the exact value of \(\Lambda_{\rm prof}\); the
  certified interval has width about \(2.02\times10^{-4}\) after taking the
  final square root.
- The Euler resolvent equations require a unique active absolute Gaussian
  scale and nonzero even/odd coherent overlaps.  They are not claimed as an
  unconditional classification of all maximizers.
- The true asymptotic leading constant for \(C_p\), convergence of
  \(C_p/p^{1/4}\), and higher-dimensional sharp dependence remain open.
- The analytic proof is not fully formalized in Lean.
- Verification is model-conducted self-review, not external human peer
  review.
- No novelty or historical priority claim is made.
