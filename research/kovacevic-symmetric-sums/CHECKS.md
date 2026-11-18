# Reproduction and limits

From this directory, using standard-library Python 3.9 or later:

```sh
python3 -B -O verify.py
python3 -B -O independent.py
sha256sum -c SHA256SUMS
```

Both scripts use explicit failures; optimization does not disable checks.

1. **verify.py** enumerates 16,422 unordered symmetric input-amplitude profiles for $1\le n\le8$, $1\le r\le12$. It tests one-sided tail bounds, the actual mixed score and all 28 midpoint comparisons in that $n$ range. The score is expressed as an integer linear combination of prime logarithms; integer bit-length bounds on powers determine its sign or raise an error.
2. **independent.py** performs integer convolution on all 6,434 sorted profiles formed from the amplitude mesh $\{0,1/6,\ldots,1\}$ for $1\le n\le8$. Of these, 2,662 have both ties and off-grid outcomes, 3,748 are entirely off-grid, and 24 are entirely on-grid. For all non-full profiles it checks the middle blocks after splitting each tie equally between neighbors. For $n\le6$ it independently checks the mixed score by comparing exact *integer products*, without prime-log intervals. It also checks the binomial tie identities and increment bound through $n=14$.

These exercise boundary cases and indexing. Neither program optimizes over arbitrary independent inputs or certifies the theorem outside the stated finite tests. The analytic proof, not finite search, gives the result for arbitrary $n,r$.
