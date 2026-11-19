# Line-graph signature at fixed cycle rank

Let $f(c)$ be the greatest possible number of positive minus negative adjacency eigenvalues of the line graph of a **connected simple graph** with cycle rank $c=|E|-|V|+1$. The order of the root graph is unrestricted.

* **Exact for $c\le5$:** the values are $0,1,1,2,2,3$. The matching lower constructions were already known. We prove the upper bound at $c=2,3,4,5$ without relying on a finite small-order census.
* **Finite for each fixed parameter, with an explicit order cutoff:** for $c\ge2$ the exact maximum is attained on at most $19(c-1)$ vertices. Every root graph is dominated in line-graph signature by a representative in this family, not necessarily equivalent in signature or inertia. The cutoff is not asserted to be minimal.
* **What remains open:** this does not prove Paone–Paone Conjecture 5.4 for all cycle ranks. Nor does it reinstate the refuted universal bound $s(L(G))\le1$.

The proof reduces arbitrary pendant forests to at most one leaf at each support; a positive-semidefinite comparison then removes leaves from internal degree-two paths. The reduced graph has only branch marks and paths of four possible lengths. At cycle ranks 4 and 5, a violation would force an impossible positive-definite integer form on the cubic kernel.

See [proof](PROOF.md), [primary sources and scope](SOURCES.md), and [independent internal review](REVIEW.md). The supplementary exact checks use only the Python standard library:

```sh
python3 -O verify.py
sha256sum -c SHA256SUMS
```

These checks cover sample instances and local operations, not all graphs. This AI-assisted working manuscript has been internally checked, not externally peer reviewed. No historical-priority claim is made.
