# Line-graph signature for all cacti and for simple suppressed kernels

For a finite connected simple graph $G$, let $c=|E(G)|-|V(G)|+1$. The signature $s(L(G))$ is the number of positive eigenvalues of its line-graph adjacency minus the number of negative ones. Paone and Paone ask whether $2s(L(G))\le c+1$.

* **Every cactus, at every cycle rank:** the inequality holds without restrictions on lengths, bridges, pendant trees, or the number of articulation vertices on a cycle. Together with the original authors' attaining examples, the maximum among cacti at rank $c$ is $\lfloor(c+1)/2\rfloor$ (at $c=0$ it is 0). [Proof by four rooted boundary states](CACTUS.md).
* **Every simple suppressed branch kernel:** for $c\ge2$, remove pendant trees down to the 2-core and suppress all degree-two vertices. If the resulting kernel has neither loops nor parallel edges, the inequality holds at all orders and ranks. [Proof using two induced matchings](SIMPLE-KERNEL.md). This is a condition on the **kernel**, not merely on the original graph.

This follows the [fixed-rank kernel note](../line-signature-cyclomatic-kernel/README.md), which covers arbitrary underlying graphs at $c\le5$. Neither result here proves the conjecture for a general nonsimple suppressed kernel outside the cactus case, nor classifies the equality graphs. The proof of sharpness for the cactus maximum uses the existing lower constructions, not a new example.

From this directory, run:
```sh
python3 -B -O verify_simple.py
python3 -B -O verify_cactus.py
sha256sum -c SHA256SUMS
```
Both scripts use the included common standard-library arithmetic module, copied from the earlier note. Only the 32 cycle states form a complete finite subcase of the proof; testing sampled graphs does not establish a theorem about arbitrary graphs. See [checks](CHECKS.txt), [primary sources and scope](SOURCES.md) and [independent internal review](REVIEW.md). AI-assisted working mathematics; the internal review is not external peer review. No priority claim. Cited works remain under their respective authors' rights.
