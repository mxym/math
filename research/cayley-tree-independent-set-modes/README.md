# Where does the independent-set sequence of a random labeled tree peak?

Pick a tree uniformly from the labeled trees on $n$ vertices. For each $k$, count its independent sets of size $k$. **Every maximizing size is $(\mu+o(1))n$ with high probability**, for a deterministic constant satisfying

$$
0.305300\leq \mu\leq 0.306955 .
$$

For each fixed $\varepsilon>0$, the probability that even one global maximum lies outside $((\mu-\varepsilon)n,(\mu+\varepsilon)n)$ is at most $e^{-c_\varepsilon n}$ for sufficiently large $n$. This answers the linear-scale concentration question in [Heilman, Question 8.2](https://doi.org/10.1002/jgt.23225). It does not determine a Gaussian fluctuation law or prove unimodality.

**Averaging first gives a different answer.** The size that maximizes the *expected* number of independent sets lies above $0.3074n$ asymptotically. In fact, with exponentially high probability, every such maximizer exceeds every maximizing size of the sampled tree by more than $0.0004n$ for all sufficiently large $n$. The expectation formula itself is classical.

[Proof of concentration](PROOF.md) · [Separation from the peak of the expectation](ANNEALED.md) · [Primary sources and prior results](SOURCES.md) · [Internal proof review](REVIEW.md)

The argument uses two distinct views of a Cayley tree. Looking downwards at descendant subtrees gives a formula for the limiting log partition function. Looking outwards from a typical vertex gives a finite-depth computation of the proportion $\mu$. The two root laws are not interchangeable.

**Checks.** All scripts require only Python 3's standard library. Run in this directory:

~~~sh
sha256sum -c SHA256SUMS
python -B -O interval.py
python -B -O annealed.py
python -B -O independent.py
python -B -O annealed_independent.py
~~~

The scripts certify rational enclosures and test finite identities; they do not substitute extrapolation from small trees for an asymptotic proof. This is AI-assisted research with internal AI review, not external peer review. No guarantee of historical priority is made.
