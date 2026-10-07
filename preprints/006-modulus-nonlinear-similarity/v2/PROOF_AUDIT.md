# Proof audit — entry 006 version 2

**Date:** 7 October 2026  
**Claim audited:** extension of the version-1 nonlinear avoidance theorem from
integer monomial leading terms to countable families of log-bi-Lipschitz
profiles.

This is an AI-assisted mathematical audit, not human peer review or
proof-assistant verification.

## 1. Dependency boundary

Version 2 imports one substantive result from version 1:

> **Robust normalized blocker.**  
> If a null configuration \(B\) has positive logarithmic upper Banach
> density and \(\Omega\) is a prescribed null modulus, then for every small
> density budget there is an open one-periodic set meeting every normalized
> perturbed copy
> \[
> x+t b+e(b),\qquad t\in[1,2],\qquad |e(b)|\le b\Omega(b).
> \]

The finite routing argument, grid entropy estimate, exceptional-center
repair, and perturbation buffer are not reproved in v2.

The inherited exact regression was rerun under ordinary Python and optimized
Python. The reports were byte-identical. SHA-256 of the ordinary JSON
report:

efd03ab6f3d92e2f96b10f4441114dcabccde2cc314bb6f872f59a3410d67e50.

The replay is finite evidence for the inherited checker only; it is not a
formal proof of either version's infinite theorem.

## 2. New density-preservation lemma

Let
\[
 \Psi(z)=-\log_2\phi(2^{-z})
\]
and assume
\[
 c(v-u)\le\Psi(v)-\Psi(u)\le C(v-u)
\]
on a tail, with \(0<c\le C<\infty\).

The proof uses two independent consequences.

### A. Bounded multiplicity of output bins

Choose one representative \(a_j\) from every occupied input dyadic bin and
put \(z_j=-\log_2a_j\in[j,j+1)\).

If two transformed points occupy the same output bin, their logarithmic
coordinates differ by less than one. The lower Lipschitz bound gives
\[
 |z_j-z_k|<1/c.
\]
Since \(z_j\in[j,j+1)\), only a bounded number
\[
 K=\lceil1/c\rceil+2
\]
of input indices can contribute to one output bin.

**Audit check:** no separation assumption on the original representatives is
used. The estimate follows solely from the one-bin width and the lower
Lipschitz inequality.

### B. Bounded span of the transformed block

An input interval of \(L\) consecutive indices produces representative
logarithms in an interval of length less than \(L\). The upper Lipschitz
bound therefore puts all transformed logarithms in an interval of length
less than \(CL\).

An input block containing at least \(\delta L\) occupied bins consequently
produces at least \(\delta L/K\) distinct occupied output bins inside an
interval of length at most \(CL+3\).

### C. Long dense blocks imply positive upper Banach density

The proof does not silently replace upper Banach density by a limsup along
selected lengths. If a set has arbitrarily long intervals of density at
least \(\eta>0\), then for any fixed block length \(q\), partitioning those
intervals into \(q\)-blocks gives
\[
 \eta |J|
 \le
 \lfloor |J|/q\rfloor F(q)+q.
\]
Letting \(|J|\to\infty\) yields \(F(q)/q\ge\eta\). Taking the infimum in
\(q\) proves positive upper Banach density.

**Audit check:** this closes the only place where an argument based merely
on a subsequence of dense block lengths would have been insufficient.

## 3. Transfer of the perturbation modulus

For a fixed profile \(\phi\), dyadic coefficient scale \(2^k\), and error
constant bounded by an integer \(q\), v2 uses
\[
 b=2^k\phi(a)
\]
and defines
\[
 \Omega(b)
 =
 q\,2^{-k}
 \omega\!\left(\phi^{-1}(2^{-k}b)\right).
\]

Because \(\phi\) is strictly increasing on the selected tail,
\(\phi^{-1}\) is increasing. Therefore \(\Omega\) is nondecreasing whenever
\(\omega\) is. Since both \(\phi(a)\) and \(b\) tend to zero together,
\(\Omega(b)\to0\).

The original error estimate
\[
 |e(a)|\le q\,\phi(a)\omega(a)
\]
becomes exactly
\[
 |e(a)|\le b\,\Omega(b).
\]

**Audit check:** the factor \(2^{-k}\) is necessary and is present. Omitting
it would be wrong for nonzero dyadic coefficient scale.

## 4. Countable bookkeeping and infinitely many misses

The blocker family is indexed by
\[
 (\ell,r,j,k,q,h),
\]
where the first three indices select the configuration, profile, and
modulus, \(k\in\mathbb Z\) normalizes the nonzero coefficient,
\(q\in\mathbb N\) dominates the finite error constant, and \(h\) selects an
arbitrarily small tail.

This set of indices is countable, so summable density budgets are available.

For a fixed germ, blockers for arbitrarily large \(h\) produce hits at
inputs \(a_h\to0\). The relative error tends to zero, so eventually
\[
 \frac{|c|}{2}\phi(a_h)
 \le |f(a_h)-y|
 \le \frac{3|c|}{2}\phi(a_h).
\]
Thus the hit values tend to \(y\) without being equal to \(y\), which forces
infinitely many distinct image points outside the closed avoiding set.

**Audit check:** one hit for each tail cutoff is enough; the same fixed input
cannot survive all later cutoffs.

## 5. Nowhere-dense conclusion

The stated profile family need not contain the identity profile. The proof
therefore explicitly adjoins \(a\mapsto a\) with an arbitrarily small
additional budget. This does not change any requested avoidance conclusion.

The identity-profile blockers exclude nontrivial affine copies of bounded
tails of every \(A_\ell\). If the final closed set contained an interval, a
sufficiently small affine copy of such a tail would lie in that interval,
contradiction. Hence the final set has empty interior and is nowhere dense.

## 6. Corollaries checked

### Positive real powers

For \(\phi(a)=a^s\),
\[
 \Psi(z)=sz,
\]
so the profile condition holds for every fixed real \(s>0\).

### Power-log profiles

For
\[
 \phi(a)=a^s(\log(e/a))^\beta,
\]
\[
 \Psi'(z)
 =
 s-\frac{\beta}{1+z\log2}\to s>0.
\]
Thus both logarithmic Lipschitz constants are positive and finite on a
sufficiently late tail.

### Differentiable slowly varying factor

For \(\phi(a)=a^sL(a)\),
\[
 \Psi'(z)
 =
 s+\frac{aL'(a)}{L(a)}.
\]
Hence the hypothesis
\[
 aL'(a)/L(a)\to0
\]
implies the profile condition.

### Puiseux germs

For a convergent Puiseux expansion with leading exponent \(s=\nu_0/q>0\),
the next possible exponent is at least \(s+1/q\), so
\[
 f(a)=y+c a^s+O(a^{s+1/q}).
\]
The theorem with all rational powers and the moduli \(a^{1/q}\) applies.

The use of the classical Newton--Puiseux theorem to infer an algebraic
branch corollary is explicitly kept external to the v2 main proof.

## 7. Remaining nonclaims

Version 2 does not establish:

- one avoiding set for an arbitrary uncountable profile family;
- simultaneous avoidance for every real exponent \(s>0\);
- avoidance of arbitrary \(C^1\) diffeomorphisms;
- avoidance of arbitrary flat smooth germs;
- positive logarithmic density for profiles with uncontrolled logarithmic
  distortion;
- bibliographic novelty or priority;
- proof-assistant formalization.

Within the stated theorem, no heuristic numerical computation or solver
output is a proof dependency.
