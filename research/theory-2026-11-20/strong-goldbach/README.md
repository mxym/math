# Strong Goldbach: central operator and proof audit

The target is the unconditional assertion that every even integer at least four is a sum of two primes. **The conjecture is not proved or refuted here.**

- [Mean-square central kernel and exact finite-wheel variance](CentralMeanSquare.md): a density-one operator bound for the actual primes, by established linear forms asymptotics. It does not give the signed uniform estimate for every even target.
- [Two specific tests of arXiv:2611.09007v1](AntidiagonalAudit.md): the asserted transition equality fails on an infinite progression, and the universal growth assertion omits an unbounded local factor. These facts test that paper's argument, not the conjecture. Run `python3 -O check.py` for the elementary finite arithmetic.

[Li–Liu's distinct November conditional proof](https://mrc.sdu.edu.cn/english/info/1018/1514.htm) assumes Dirichlet GRH and an additional spectral hypothesis. The operator note isolates what averaging can establish without either assumption; it is not an assertion that their uniform hypotheses follow.
