# Verification

## General argument

A separate AI-assisted internal review checked the definition against the specified paper version, the uniqueness of the limiting clique proportions, the strictly positive third part even when the internal blue density is itself reciprocal, and the mixed-copy decomposition. The strict inequality holds separately at each nonreciprocal density considered. This is not external peer review.

## Independent count for the exactly regular witness

Let $R$ and $B=J-I-R$ be the finite red and blue adjacency matrices. The labelled count is $\operatorname{tr}[(RB)^2]$ with no collision correction: adjacent labels cannot coincide (there are no loops); opposite labels cannot coincide because the same edge would have to be both colours.

In $K_{2m+1}\sqcup K_{m,m,m}$ the red degree is $2m$, so $R$ and $B$ commute. On the all-ones vector the two eigenvalues are $2m$ and $3m$. On its orthogonal complement, the red eigenvalues are $2m$ (one component contrast), $-m$ (two tripartite-class contrasts), $-1$ ($2m$ zero-sum clique vectors), and $0$ ($3m-3$ within-tripartite-class zero-sum vectors); the corresponding blue eigenvalue is $-1-\lambda$. Hence
$$
N=(6m^2)^2+[2m(2m+1)]^2+2[m(m-1)]^2
 =54m^4+12m^3+6m^2.
$$
This verifies the direct component count in [the witness](WITNESS.md).

## Reproduce

With Python 3 (standard library), run from this directory:

```sh
python3 verify.py
python3 independent.py
sha256sum -c SHA256SUMS
```

The first script exhausts injective four-tuples for $m=1,\ldots,5$, enumerates all $5^4$ ordered block patterns and checks the strict comparison in $\mathbb Q(\sqrt{10})$. It also checks the adjacent variant with a clique of size $2m$. The second computes the matrix count independently for $m=1,\ldots,12$ and encloses the comparison with rational arithmetic. The recorded output is in [CHECKS.txt](CHECKS.txt). No flag-algebra output is needed; the cited authors' numerical computations have not been rerun or diagnosed.
