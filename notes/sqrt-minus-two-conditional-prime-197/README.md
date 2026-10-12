# An explicit conditional solution of the actual 197-prime component problem

Research note, 8 October 2026. **Conditional theorem; not an unconditional prime-graph solution.** [Full proof](paper.md) · [197-polynomial CRT certificate](code/schinzel_affine_family.json) · [independent exact checker](code/check_polynomials.py) · [audit](AUDIT.md) · [replay log](results/replay.txt).

The [previous exact sieve-optimization theorem](../sqrt-minus-two-exact-sieve-optimum/README.md) proves **unconditionally** that in `Z[sqrt(-2)]` with actual Euclidean edge-radius `sqrt(6) <= D < sqrt(8)`, the maximum component size of the **prime-element-only graph** lies in the interval

\[
90\le B_D\le197.
\]

The same research contains a 197-vertex connected lattice pattern avoiding all **finite** congruence sieves, but this does not by itself prove that all 197 vertices can be irreducible simultaneously.

This new note makes the missing arithmetic step completely explicit. It constructs **197 concrete distinct monic irreducible quadratic polynomials**

\[
f_{a,b}(n)=(n+X+a)^2+2(Y+b)^2,
\]

one for each of the 197 coordinates in the pinned pattern, with fixed **159-digit** integers `X,Y` in the bundled certificate. It proves their product has **no fixed rational prime divisor**: 77 primes `p <= 394` are covered by complete literal CRT witnesses, while all larger primes are handled by the degree-394 finite-field root bound. An independent checker reconstructs and verifies the 197 forms.

**Conditional main result:** If classical **Schinzel's Hypothesis H** holds for this *particular* 197-polynomial family, then

\[
\boxed{B_D=197}
\]

and in fact the graph has **infinitely many** distinct components of exactly 197 prime elements. Even one integer `n` giving 197 simultaneous rational-prime polynomial values would suffice for the unconditional equality, but no such value is currently supplied.

This identifies precisely the missing prime-value existence problem. The classical Hypothesis H is **unproved**, including broad classes of quadratic-polynomial special cases. The unconditional results remain `90 <= B_D <= 197`; the conditional statement must never be cited without its hypothesis.

**Further conditional classification:** Assuming **full** classical Hypothesis H (not just this single 197-form instance), **every size from 1 through 197** occurs as an entire prime connected component **infinitely often**. A new inert-prime boundary-blocking lemma makes all exterior neighbors composite without harming local admissibility of the interior. The public exact checker verifies all 197 connected prefixes, 1,186 distinct inert-prime boundary blockers, and **15,563,538** interior–boundary modular nonvanishing predicates. This is a conditional *complete component-size spectrum*, not an unconditional existence claim.

## Independent replay

```sh
python3 code/check_polynomials.py
python3 -O code/check_polynomials.py
python3 code/check_boundary_spectrum.py
python3 -O code/check_boundary_spectrum.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

The checker validates the exact previously certified 197-point pattern hash, all 77 local primes, CRT coordinates, all 15,169 nonzero small-prime evaluations, negative quadratic discriminants and polynomial distinctness. A separate elementary written lemma handles **every** prime `p > 394`. The producer `code/build_polynomials.py` can rebuild the certificate but is not trusted by or imported into the checker. Mutation tests reject altered CRT data, missing primes or invalid polynomial counts. The additional checker independently validates all finite inert-prime exterior-boundary conditions needed for the conditional full spectrum.

## Scope and literature distinction

Unconditional constellation theorems for Gaussian and number-field prime elements (Tao, [arXiv:math/0501314](https://arxiv.org/abs/math/0501314); Kai–Mimura–Munemasa–Seki–Yoshino, [arXiv:2012.15669](https://arxiv.org/abs/2012.15669)) allow a nonzero **dilation** of a prescribed pattern. They do not guarantee unit dilation and hence do not directly provide a fixed-difference 197-prime component in this bounded-step graph. Classical Schinzel H has substantially stronger content in this specific respect.

This is a mathematically precise **conditional** research continuation, not a claimed discovery of a 197-prime component, a proof of Hypothesis H, a world-first priority determination or a Lean formalization. Existing unconditional manuscripts remain unchanged.
