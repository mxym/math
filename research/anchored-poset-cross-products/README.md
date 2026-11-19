# The anchored cross-product inequality for linear extensions

Given three specified elements of a finite poset, let F(i,j) count linear extensions in which their successive rank gaps are i and j. For every i,j≥1,

    F(1,1) F(i,j) ≤ F(i,1) F(1,j).

Brightwell, Felsner and Trotter proved the case i=j=2 in 1995 and explicitly suggested this all-index version at the end of §3. The [proof](PROOF.md) extends their filter inequality by coupling the first elements of two uniform extensions. It works at every width.

A [strengthening](SHIFTED.md) uses the separately smallest possible gaps a and b instead of 1 and 1: whenever i≥a and j≥b, F(a,b)F(i,j)≤F(i,b)F(a,j). This can give a nonzero comparison when F(1,1)=0. For example, take a four-element chain x<u<y<z and two additional isolated elements. For (x,y,z) the minimum gaps are (2,1), and the comparison at (3,2) is 6·4≤8·4. Neither theorem settles the classical conjecture at an arbitrary interior pair of adjacent gaps.

[Sources and scope](SOURCES.md) · Internal AI reviews of the [anchored](REVIEW.md) and [shifted](SHIFTED-REVIEW.md) proofs. No external peer review or priority claim.

Run the exact finite checks (Python standard library only):

```sh
python3 verify.py
python3 shifted_check.py
sha256sum -c SHA256SUMS
```

Outputs: [original](CHECKS.txt), [shifted](SHIFTED-CHECKS.txt). The scripts exhaust all naturally labelled posets up to order five; the results for arbitrary orders come from the proofs, not extrapolation.
