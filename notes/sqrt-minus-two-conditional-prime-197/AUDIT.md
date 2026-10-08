# Correctness scope and explicit hypothesis boundary

8 October 2026. Model-assisted research audit; not external human peer review.

## Unconditional, exactly checked inputs

1. The prior [197-point pattern](../sqrt-minus-two-universal-sieve-barrier/paper.md) is connected under the fourteen specified lattice steps. Its immutable raw coordinates are SHA256-pinned by the new checker. Earlier checks established a norm-avoiding translation modulo each rational prime, with 45 concrete local shifts for primes up to 197 and a written split/inert argument for every larger prime.
2. The new deterministic producer chooses 77 explicit norm-avoiding local shifts for every rational prime `p <= 394`, then combines them by **coordinatewise CRT** into a concrete pair of 159-digit offsets `X,Y`. The independent checker verifies all 77 exact congruences and **all 197 × 77 = 15,169 norm values** are nonzero modulo the relevant small prime.
3. The 197 polynomials `f_z(n)=(n+X+a)^2+2(Y+b)^2` are monic, positive, pairwise distinct and irreducible over the rationals, with discriminant `-8(Y+b)^2 < 0`. The independent checker reconstructs and checks these finite properties.
4. For every rational prime `p > 394`, their monic product of **degree 394** is nonzero over `F_p` and has fewer roots than the field's cardinality. This elementary root-count argument proves there is **no fixed prime divisor for any p**, without enumerating infinitely many primes.
5. If an integer `n` simultaneously makes all 197 norms rational primes, their translated lattice elements are all irreducible and connected. The independently proved **unconditional** prime-only upper bound 197 then makes them a whole exact 197-prime connected component. This final implication is elementary.

## Unproved ingredient, visibly separated

Classical Schinzel–Sierpiński **Hypothesis H** asserts simultaneous prime values infinitely often for a finite family of irreducible integer polynomials of positive leading coefficient with no fixed prime divisor. The exact 197-form list satisfies its **hypotheses**. The checker does **not** test, assume or establish its **conclusion**. Consequently the assertion `B_D=197` is proved here **only conditional on H for this explicit family**. The unconditional range remains `[90,197]`.

Tao's Gaussian-prime constellation theorem and its number-field generalization permit **dilation**, so they cannot simply replace H to obtain bounded unit-scale differences. No proof of historical novelty or external human peer review is claimed.

## Reproduction

```sh
python3 code/check_polynomials.py
python3 -O code/check_polynomials.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

Standard-library Python exact integers only; no float, randomization, external solver or closed primality oracle. The checker never imports `code/build_polynomials.py`. Negative controls change prime indices, delete a prime, tamper with CRT offsets and modulus, and invalidate polynomial distinctness/count conditions, requiring explicit failure under both Python modes.

## Priority of remaining mathematical work

To remove the condition, it suffices to produce **one verifiable specialization** with all 197 norms rational prime, or to establish the required existence by a new unconditional prime-value theorem. A finite norm-congruence certificate alone cannot prove such simultaneous primality. The correct unconditional maximum therefore remains open in the interval shown above.
