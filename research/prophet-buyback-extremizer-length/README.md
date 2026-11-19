# The arcsine profile and length of exact buyback extremizers

**Yongxian Zhang.** AI-assisted research manuscript, 19 November 2026. Independently checked internally by AI, not externally peer reviewed. No claim of global priority.

For a positive cancellation fee `f`, Ekbatani–Niazadeh–Nuti–Vondrák (ENNV) construct a finite, exactly worst-case instance of the prophet inequality with buyback. Its probability knots determine the independent two-point offers and enforce indifference between adjacent offers. How many distinct knots does such an extremizer have, and where do they lie when cancellation becomes cheap?

[The proof](PROOF.md) shows that **every strictly increasing ENNV-indifferent knot family that attains the unrestricted optimum exactly** has
```
N ∼ π / √(2 f ln(1/f))
```
as `f↓0`. Giving each normalized knot equal mass, the knot distribution converges to the arcsine law on `[0,1]`, with density `1/[π√(x(1−x))]`. The larger density near 0 and 1 describes a change in the spacing of the knots, not two atoms at the endpoints.

This sharpens the known coarse iteration bound for ENNV's exact construction. It does not say that all possible exactly worst-case laws must have this structure, or that no shorter unrestricted family of some other type exists. It also differs from the [number of arrivals sufficient to approximate the worst loss](../prophet-buyback-horizon-transition/README.md). See [source details](SOURCES.md).

The proof uses exact prefix variations, a uniformly controlled prefix value, a bulk difference identity, and bounds ruling out excess mass at either boundary. To replay the finite algebra checks:
```sh
sha256sum -c SHA256SUMS
python3 -O verify.py | diff - CHECKS.txt
```
The replay uses only rational arithmetic and the Python standard library. The asymptotic distribution is proved analytically, not by extrapolation from these checks.
