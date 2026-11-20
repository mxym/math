# Strong Goldbach: central operator and proof audit

The target is the unconditional assertion that every even integer at least four is a sum of two primes. **The conjecture is not proved or refuted here.**

- [Mean-square central kernel and exact finite-wheel variance](CentralMeanSquare.md): a density-one operator bound for the actual primes, by established linear forms asymptotics. It does not give the signed uniform estimate for every even target.
- [Two specific tests of arXiv:2611.09007v1](AntidiagonalAudit.md): the asserted transition equality fails on an infinite progression, and the universal growth assertion omits an unbounded local factor. These facts test that paper's argument, not the conjecture. Run `python3 -O check.py` for the elementary finite arithmetic.

[Li–Liu's distinct November conditional proof](https://mrc.sdu.edu.cn/english/info/1018/1514.htm) assumes Dirichlet GRH and an additional spectral hypothesis. The operator note isolates what averaging can establish without either assumption; it is not an assertion that their uniform hypotheses follow.

## Pointwise progress on the divisor-switch route

- [Sharp shifted-squarefree margin](SharpPointwiseSquarefreeMargin.md): an unconditional pointwise worst-case constant for the number of primes whose complement is non-squarefree. This does not count two primes.
- [Centered divisor switch](CenteredDivisorSwitch.md): an unconditional `O(N/B)` discarded arithmetic tail and corrected moving endpoint. The improvement of the logarithmic modulus buffer is at the same scale, not a weaker all-scales ordinary Elliott–Halberstam conjecture.
- [Annihilating moduli](AnnihilatingModuli.md): the original all-modulus Möbius-twisted hypothesis forces its own total to be small; conditional Hardy–Littlewood asymptotics follow. A smaller sufficient hypothesis tests only the squarefree twisted moduli and required endpoints, but is still unproved.

Run `python3 -O check_switch.py` for the finite exact identity checks. The checks are not evidence of the missing analytic distribution estimate.

## A signed estimate in the balanced block

- [Balanced factor-count bounds](BalancedTwistFactorCounts.md) localize the large absolute contributions for each even target.
- [Signed balanced transition](SignedBalancedTransition.md) saves a power of log on the full balanced block for actual primes, including the middle factor counts. As a scoped conditional consequence, ordinary Bombieri–Vinogradov plus a **still-unproved Möbius-twisted** distribution bound slightly below the square-root level would yield individual Goldbach asymptotics. The unconditional result does not estimate the smaller twisted moduli or prove Goldbach.
- [Smoothed signed transition](SmoothSignedTransition.md) extends that range to a fixed exponent `δ<1/9` in the scale `sqrt(N) exp(−(log N)^δ)` for the still-unproved twisted input. No smaller-modulus pointwise theorem is claimed.
- [Unweighted interior Möbius primitive](InteriorMobiusPrimitive.md) gives a pointwise-in-target `L^1` saving on a single interval throughout polynomially interior divisors. It cannot simply be integrated over a full logarithmic width to bound the weighted switch.

The [moving endpoint correction](https://doi.org/10.5281/zenodo.21939906) in the earlier Huang–Li argument was already documented by Ramón Moya in August 2026; the centered tail and signed bounds here are separate.
