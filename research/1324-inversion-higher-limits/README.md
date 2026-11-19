# Secondary and tertiary inversion limits for subclasses avoiding 1324

For a finite forbidden set containing 1324, let a(n,k) count its permutations of length n with exactly k inversions. For every fixed integer j the first length difference

D(n,n+j−1) = a(n+1,n+j−1) − a(n,n+j−1)

is eventually an affine function of n. In particular its difference along the diagonal is eventually constant. For the pairs {1324,p} with p of length four, an exact finite computation identifies which first differences are already constant and gives the complete five tertiary generating functions. This addresses [Claesson–Linusson–Úlfarsson–Verkama, Problem 8.4](https://arxiv.org/html/2604.01143v2#S8). The reported patterns and several formulas were already predicted from data by the authors; the principal 1324 case and the 1342 case were previously proved. See [prior work](SOURCES.md).

|Representative p|Stabilization|
|---|---|
|1243, 1342, 1432, 2341, 3421, 4321|D itself is eventually constant on every diagonal.|
|2143, 2413, 2431, 3412, 4231|The diagonal difference of D stabilizes; D does not stabilize on every diagonal.|

Inverse and reverse complement yield the other patterns. The identity restriction also has zero diagonal slopes; 1324 itself recovers the known secondary case. The general theorem is not a sign inequality and does not settle inversion monotonicity for unrestricted 1324. Negative slopes are possible for a subclass.

1. [AFFINE.md](AFFINE.md): stripping singleton components and bounding the number of expandable leaf families gives the general theorem.
2. [SPLIT.md](SPLIT.md): all two-family cores, including the possible endpoint decorations; exact classification of the six and five representatives.
3. [SERIES.md](SERIES.md): the full tertiary generating functions, including why an old primary series reappears in three cases. This is not a closed form for all the secondary constants.
4. [SOURCES.md](SOURCES.md) gives historical and recent comparisons. [REVIEW.md](REVIEW.md), [SPLIT-REVIEW.md](SPLIT-REVIEW.md), and [SERIES-REVIEW.md](SERIES-REVIEW.md) record separate internal AI-assisted reviews. Neither these reviews nor the finite computation constitute external peer review; no comprehensive priority guarantee is made.

Reproduce using only Python 3 and its standard library, in this directory:

```
sha256sum -c SHA256SUMS
python3 -BO verify_profiles.py
python3 -BO verify_series.py
```

The expected results are in PROFILE-CHECKS.txt and SERIES-CHECKS.txt. The checks enumerate all formal endpoint profiles, not a sample of values of n. The structural proof explains why this finite enumeration suffices.
