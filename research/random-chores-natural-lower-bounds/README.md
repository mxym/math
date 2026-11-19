# How far below two chores per agent can exact envy-freeness be ruled out?

All chores must be allocated. Every agent draws an independent cost for every chore from the same nonatomic distribution on $[0,1]$, and adds costs within a bundle. Write $n$ for the number of agents and $m>0$ for the number of chores. With probability tending to one as $n$ grows, no exactly envy-free allocation exists in either of the following regimes:

- For **every nonatomic cost law**, $m/n$ stays a fixed positive amount below $C_A\approx1.26016893448$. The bound is distribution-independent, even if the law changes with $n$.
- For **uniform costs**, $m/n$ stays a fixed positive amount below $C_U\approx1.36145148635$. The same holds for each fixed law with positive lower-tail mass and $F(tx)/F(x)\to t$ as $x\downarrow0$ for every $t>0$, including $F(x)\sim ax$ with $0<a<\infty$.

The first proof counts candidate allocations by which agents hold single chores and the sizes of all remaining bundles. The second follows escalating conflicts over the cheapest chores; a scaled uniform order-statistic calculation determines the distribution of the number of safe ranks. Both constants are crossings of **necessary tests**. Neither is claimed to be the exact transition, and no existence conclusion follows just above either value.

[Manurangsi and Suksompong](https://doi.org/10.1137/25M180161X) proved the previous all-law lower bound near 1.1256 and existence at $m\ge2n$ for densities bounded above and away from zero. [The earlier repository note](https://github.com/mxym/math/pull/120) used specially selected laws and subsequences to rule out any uniform reduction of the sufficient factor 2; its request rule is reused here. That quantifier is different from either result above.

Read the [proof](PROOF.md), [sources and scope](SOURCES.md), and [independent internal review](REVIEW.md). Compare both scripts' [test results](CHECKS.txt) by running `python3 -B -O verify.py` and `python3 -B -O independent.py`. They use only the Python standard library. AI-assisted; not externally peer reviewed, no priority guarantee.
