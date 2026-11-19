# Why a fixed degree cap forces more than polynomially many cycles

For every fixed integer $D\ge 3$, a simple 3-connected graph on $n$ vertices of maximum degree at most $D$ contains at least $2^{c_D n^{\gamma_D}}$ simple cycles for sufficiently large $n$, where
\[
\gamma_D=\tfrac14\log_{2(D-1)^2+1}2,\qquad c_D>0.
\]
Cycles are distinguished by their edges. The exponent is not claimed optimal.

**Consequence.** Knor conjectured in 1994 that for fixed $2<k<\delta<D$, the minimum number of cycles among $k$-connected graphs on $n$ vertices with minimum degree at least $\delta$ and maximum degree at most $D$ is of order $n^k$. The lower bound above rules out the polynomial upper bound for **every** such triple, not just along special orders. This differs from the uncapped degree-four result in [the earlier note](../cycle-count-density-lower-bounds/KNOR.md). It does not imply an exponential-in-$n$ lower bound; known short-circumference families preclude that strengthening on subsequences.

**Idea.** Aldred and Thomassen used long cycles, disjoint chords and switchable ladders to prove superpolynomial growth for cubic 3-connected graphs. Here a bounded-degree tree argument supplies a positive proportion of disjoint ears even when vertices have different degrees. The ladder argument is performed inside the original graph, where 3-connectivity guarantees a detour even when its endpoint is inside a subdivided rung. A known circumference bound gives the displayed exponent.

[Proof](PROOF.md) · [Precursors and scope](SOURCES.md) · [Independent internal review](REVIEW.md). This is AI-assisted mathematical work with an independent AI review, not external peer review. We make no guarantee of priority.

The proof is not computer-assisted. Optional finite checks of the ladder constructions can be run with stock Python 3:

```sh
sha256sum -c SHA256SUMS
python3 check.py | diff - CHECKS.txt
```
