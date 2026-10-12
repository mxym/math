# Log-bi-Lipschitz profile avoidance

**Entry 006, version 2 — 7 October 2026. Complete written proof draft; inherited exact routing replay passed.**

Read the [manuscript](paper.md) and [proof audit](PROOF_AUDIT.md). Version 2 is a
supplement to [version 1](../v1/), whose robust finite-cover checker remains
the computational dependency for the inherited routing engine.

## New theorem

Let \(A_\ell\) be countably many null configurations with positive
logarithmic upper Banach density. Let \(\phi_r\) be countably many positive
profiles for which
\[
 \Psi_r(z)=-\log_2\phi_r(2^{-z})
\]
is bi-Lipschitz on a tail of the logarithmic axis, and let \(\omega_j\) be
countably many vanishing remainder moduli.

For every \(\varepsilon>0\) there is one closed, nowhere-dense,
one-periodic set \(E\) of density greater than \(1-\varepsilon\) which
simultaneously excludes every tail image satisfying
\[
 f(a)=y+c\phi_r(a)+O\!\left(\phi_r(a)\omega_j(a)\right),
 \qquad c\ne0.
\]
In fact every sufficiently small tail of such an image has infinitely many
points outside \(E\).

The new structural lemma proves that positive logarithmic upper Banach
density is preserved by every log-bi-Lipschitz profile. This identifies the
coarse logarithmic-scale invariant actually needed by the version-1 routing
method.

## Consequences

The theorem applies simultaneously to any prescribed countable family of

- arbitrary positive power exponents \(a^s\), not only integer orders;
- power-log profiles \(a^s(\log(e/a))^\beta\);
- differentiable profiles \(a^sL(a)\) with
  \(aL'(a)/L(a)\to0\);
- all positive rational powers at once.

Taking all positive rational powers and the moduli \(a^{1/q}\) gives a
single near-full-measure set excluding every nonconstant germ with a
convergent Puiseux expansion and finite limit at zero.

The theorem does **not** claim simultaneous avoidance of an uncountable
family of profiles such as every real exponent at once, nor does it remove
the \(C^1\)/flat-smooth endpoint obstructions proved in version 1.

## Verification

The new profile-preservation argument is a written proof and has no
numerical proof dependency. The inherited exact robust-cover regression from
version 1 was rerun under ordinary Python and Python optimized mode; the
reports were byte-identical. The ordinary exact-rational report had SHA-256

efd03ab6f3d92e2f96b10f4441114dcabccde2cc314bb6f872f59a3410d67e50.

From ../v1/:

~~~sh
python3 verification/check_robust_cover.py --self-test --output /tmp/normal.json
python3 -O verification/check_robust_cover.py --self-test --output /tmp/optimized.json
cmp /tmp/normal.json /tmp/optimized.json
~~~

These are finite regression checks for the inherited routing engine; they
do not formalize the new infinite density lemma.

## Scope and provenance

Version 2 depends on the robust normalized blocker proved in entry 006
version 1, whose first complete source was disclosed in commit
478be8879564e99843ad0bc69ca6192379e5b59e. Historical version-1 files are
unchanged.

No first-discovery, novelty, external-referee, or proof-assistant claim is
made.
