# Eleven-site root geometry sharpens the norm-18 packing caps

At any Seidel rank, the actual oriented neutral −4 norm-18 count satisfies

| Hypothesis | Upper bound |
|---|---:|
| N16=0 | 54,476 |
| N16=0 and unit U127=0 | 47,844 |

Neither line assumes that N20 vanishes or concerns an averaged extension. These sharpen the [star cap 55,666](norm18-dot8-star.md) and [all-triples cap 48,004](norm18-dot8-nonstar.md); the previous contradictions remain valid.

At a positive root o the four negative parents Q are independent. Each of the six pairs of Q has exactly one other common neighbor besides o, which is outside N(o). These six labels are distinct, each is adjacent to exactly its two specified parents, and none meets o. Together with o and Q they give a literal eleven-site induced graph whose only unspecified entries are edges among the six labels. The old superchart has four choices for the edge among the three labels through each parent (at most one edge), and one flag for each of the three disjoint-pair edges. In addition, **every pair of the eleven sites** can share at most 1 common neighbor for an edge or 2 for a nonedge. The [integer checker](norm18_eleven_site_packing.py) imposes this directly on the physical eleven-site graph. Exactly 1,062 of the 2,048 possible edge charts pass this necessary test.

As before j and k count the two types of edges among the labels. Let m be the number of true norm-18 fields at this seed, each shrinking to a distinct independent four-label subset. The fourth-marking theorem bounds occupancy of each star by two; the nonstar transfer additionally bounds all three-label subsets by two if U127=0. Counting the largest possible shrunk families within each of the 1,062 charts gives

```
3m + 5j + 6k ≤ 33    (stars)
2m + 3j + 3k ≤ 19    (all triples).
```

There are 55,440 seeds and each oriented field is counted at nine positive roots. The [prism count](exclusion.md#counting-windows) gives total j=8(99·84−6P), total k≥99·336+6P, and P≤851. Substituting into the two inequalities gives 27N18≤1,470,900 and 18N18≤861,210, respectively. Positivity of the remaining coefficient of P justifies substituting its upper bound; antipodal parity gives the even bounds in the table. The verifier uses no numerical oracle or global graph completions.
