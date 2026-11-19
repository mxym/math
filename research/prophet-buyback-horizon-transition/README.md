# When does the number of arrivals matter in a buyback prophet inequality?

**Yongxian Zhang.** AI-assisted research manuscript, 19 November 2026; independently reviewed internally by AI, not externally peer reviewed. No guarantee of priority.

Suppose an online buyer knows the laws and order of `N` independent nonnegative offers. It may replace an earlier choice at a fee equal to `f` times the discarded value. The benchmark is the expected maximum. As the fee goes to zero, how long must the sequence be before the worst-case loss resembles that with no horizon limit?

[The uniform estimate](PROOF.md) answers this for every horizon at once. Write `m=N−1`, `L=ln((1+f)/f)`, and let `c_N(f)` denote the best worst-case ratio of expected net reward to expected maximum. Then
```
1−c_N(f) = f m(1−exp(−L/m)) + O(f),
```
with an absolute error constant, and the ratio to the displayed leading term tends to 1 uniformly even for fixed `N≥2`. At `m/L→a∈(0,∞)`, the fraction of the unrestricted leading loss tends to `a(1−exp(−1/a))`. It tends to 1 precisely when `m/L→∞`.

[Two scales of near-attainment](HORIZON-COST.md) distinguishes this from the stronger requirement of agreeing with the unrestricted guarantee up to an additive `O(f)`: that requires and suffices that `m=Ω(L²)`. This is not an exact characterization of the smallest extremizing horizon at a fixed fee.

Ekbatani–Niazadeh–Nuti–Vondrák already gave the unrestricted all-fee characterization, the indifference instances, and the logarithmic-order loss. One of their constructions gives the hard direction at a particular crossover point. The [previous note](../prophet-buyback-three-arrivals/README.md) obtained the sharp unrestricted leading coefficient. See the [source comparison](SOURCES.md) for the precise overlap, including how ENNV's threshold analysis can be specialized to the guarantee direction.

## Reproduce the finite checks

```sh
sha256sum -c SHA256SUMS
python3 -O verify.py | diff - CHECKS.txt
```

The standard-library script uses rational backward induction and direct enumeration of threshold ties. It also verifies the tail and padding estimates at exact test inputs; the all-horizon conclusion comes from the proof.
