# Replay evidence

The source representatives are certified by the orbit-mass equalities; the per-stage output appears in `classification.log`. There are 2,555 dimension-nine and 208 dimension-ten representatives in the input files. Output is established by mathematical coverage and exact recomputation, not a stored solver verdict.

## Positive tests

* The 48 listed points in `known48.txt` give exactly 1,128 distinct pair sums. Their binary coordinates are integers in 0–2047.
* The rank-ten, size-32 anchor `control32.txt` has exactly 992 labeled opposite 16-sets containing zero. The independent minimum-difference search returns an actual completion, tested from scratch.
* Both quarter algorithms infer full witnesses of size 48 from `control20.txt` in shape (20,12,10,6), with the first two slice Fourier cutoffs 8 and 12. Each recovered witness has 1,128 distinct pair sums.

## Enumeration totals

“Eligible” is the number of source classes after the immediate bound $\max_{u\ne0}|w_C(u)|+(b\bmod2)\le L_b$. “Pair” counts a pair of *translation classes* of compatible first and second additional layers, for a given anchor source representative. For identical layer sizes and cutoffs the pair is unordered. “Large holes” counts pairs leaving at least the required final layer size available, not successful completions. All large hole sets are searched exactly. The two algorithms agree per source for the six shapes with a 31-point hyperplane; their search orders and actual point representatives differ.

|Shape|Eligible|Pairs|Large holes|Maximum number of holes|
|---|---:|---:|---:|---:|
|(22,9,9,9)|124|1,933,634|8|11|
|(21,10,10,8)|695|336|0|6|
|(21,10,9,9)|695|901,782|8|10|
|(20,11,11,7)|7|0|0|0|
|(20,11,10,8)|7|14,884|308|11|
|(20,11,9,9)|7|1,149,200|21,530|14|

For sources removed by the immediate bound, there are zero pairs. A displayed zero maximum for an empty collection means that there were no pairs; it is not an assertion about the size of a particular hole set.

For (20,10,10,9) there are 846 eligible source classes. The first implementation applies the necessary quadratic congruences and rejects every candidate first 30-layer: zero pairs remain. The independent second implementation omits the quadratic test. It enumerates **3,210** compatible pairs; **279** have at least nine holes, the largest hole set has **12** points, and no fourth 9-set completes. Thus the final nonexistence does not depend on a correct rejection by the quadratic filter.

`checks.tsv` records all eligible anchors for all seven shapes. Each anchor is identified by its index within its cardinality in d9.txt and the SHA-256 of its decimal points separated by single ASCII spaces, without a trailing newline. The two triples are respectively (pair count, large-hole count, maximum hole count) in each independent algorithm. The first six rows of the aggregate table summarize per-anchor equalities, not merely coincidentally matching totals.

Development and replay were tested on x86-64 Linux with GCC 14.2 and Python 3.12.14. All mathematical checks use only integer operations. Runtime depends on compiler and the number of cores and can be substantial; for progress the script flushes a report after each classification size and each complete quarter shape. Run `sha256sum -c SHA256SUMS` in the extracted directory to check the archived files.
