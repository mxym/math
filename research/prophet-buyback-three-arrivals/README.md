# Prophet inequalities with buyback: three arrivals and the small-fee limit

**Yongxian Zhang.** AI-assisted research manuscript, 19 November 2026. The proofs received independent internal AI review, not external peer review. No claim of global priority.

The buyer observes independent nonnegative values in a known order, knowing their laws. Replacing a provisional choice costs a fraction `f` of its value. Compare the best expected net reward with the expected maximum. We treat two different worst-case questions:

* **Exactly three arrivals.** [The fixed-horizon proof](PROOF.md) shows that the three-variable hard instance proposed by Ekbatani, Niazadeh, Nuti and Vondrák (ENNV) attains the worst possible ratio. For `0<f<1` it is `(1+f)(1+s)/(1+3f+(1+f)s)`, where `s=√(f(2−f))`. The new part is the lower guarantee for three arrivals at `0<f<1/3`. ENNV already established the upper example throughout, and later proved exactness even at unrestricted horizon for fees at least 1/3.
* **Any finite number of arrivals.** [The small-fee proof](SMALL-FEE.md) gives the unrestricted loss `1−α(f)=f ln(1/f)+O(f)`. ENNV already gave the exact differential-equation characterization for positive fees, the order of the loss, and the matching one-sided guarantee with unit natural-log coefficient. The other side follows from an explicit quadratic sequence of ENNV's indifference knots. This does not determine the next coefficient.

[Original papers and scope of the comparison](SOURCES.md). For the first proof the order and laws are known to the policy. Neither result claims an exact formula for every fixed horizon or an order-agnostic three-arrival guarantee.

## Reproduce the checks

From this directory, with Python 3 (standard library only):

```sh
sha256sum -c SHA256SUMS
python3 -O verify.py | diff - CHECKS.txt
python3 -O check_smallfee.py | diff - SMALL-CHECKS.txt
```

The scripts check finite exact arithmetic examples and identities. The proofs, not these examples, cover all allowed distributions or establish the small-fee limit.
