# Exponentially more independent sets than the path, at every positive density

Let $i_k(T)$ count the independent vertex sets of size $k$ in a uniform labeled tree $T_n$. Wingard's sharp deterministic lower bound is the path count $i_k(P_n)=\binom{n-k+1}{k}$. A typical tree improves this by an **exponential factor**, simultaneously over the macroscopic range where the path count is nonzero. For every fixed $0<\varepsilon\le 1/2$ and all sufficiently large $n$, except on an event of probability at most $e^{-c n}$,
$$
i_k(T_n)\ge e^{b_\varepsilon n}\binom{n-k+1}{k}
\qquad\text{for every integer }\varepsilon n\le k\le\lceil n/2\rceil,
$$
where $b_\varepsilon=\min(e^{-4}/12,\varepsilon/12)\log(1+\varepsilon^3/27)>0$ is not claimed sharp. This gives the typical exponential improvement sought by [Heilman's Question 8.3](https://doi.org/10.1002/jgt.23225) in the fixed-positive-density range. For $k=o(n)$ a fixed positive exponential rate is impossible; above $\lceil n/2\rceil$ the path benchmark is zero.

The [proof](PROOF.md) uses many disjoint pendant claws. Exchanging a claw for a path leaves an extra cubic term in either state of the parent. Expanding those terms amplifies Wingard's lower bound on the remaining connected tree. The exponential concentration of the claw count itself already follows from McDiarmid's pendant-appearance theorem. The old maximum independent-set bound alone treats part of the high-density range. See [prior work](SOURCES.md) and the [internal review](REVIEW.md). This is AI-assisted research with independent AI checks, not external peer review or a guarantee of priority.

Run from this directory, using Python 3's standard library:

~~~sh
sha256sum -c SHA256SUMS
python -B -O check.py | diff - AUTHOR-CHECKS.txt
python -B -O independent.py | diff - CHECKS.txt
~~~

The first program tests 271,248 coefficient bounds on the rooted-tree enumeration through order 13; the second checks via parent maps, changes of one pointer, and direct enumeration of independent vertex sets.
