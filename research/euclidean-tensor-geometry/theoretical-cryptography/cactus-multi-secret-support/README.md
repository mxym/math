# Exact randomness support on cactus graphs

In graph-based conditional multi-secret sharing, the dealer gives a share to each edge. Each vertex must recover its own secret bit from its incident edges, and their **joint** distribution can depend only on that bit. The cost here is the number of positive-probability dealer states, not their Shannon entropy.

For every finite connected cactus other than the bare triangle (the known three-secret-sharing case), we determine the minimum for every nonempty binary domain. The values are \(1,2,3,4,\infty\). Delete the edges that reveal their endpoint bits deterministically by an XOR relation. An uncovered active vertex of remaining degree below two makes the instance infeasible. After that, exact tests for uniform two and three states separately examine each remaining cycle. Two forests cover all other feasible instances with four states.

**A compatibility obstruction:** a triangle and a square, each separately shareable with at most three states, can require four when they share a cut vertex. The triangle in the example works with two states but not with uniform three, while the square has minimum three. We also show on **arbitrary graphs** that any nonuniform three-state scheme can be replaced with at most two states.

Run `sh replay.sh` for two independent finite checks. The classification is analytic and does not rely on these enumerations.
