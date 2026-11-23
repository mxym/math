# The norm-18 lower bound with unrestricted norm 24 and charge-two cost 26

In every maximal determinant-49 extension of any hypothetical Conway graph, let V denote the folded unit populations on the twelve selected types, and W the folded whole-shell populations. Use S=W123−99−7W014≥0, the excess of the charge-one cost-23 population beyond the ordinary marks and the Fano translates. Then
```
48V018 − 2V016 − 3V020 + 3V026 + 51V121 + 2V125 + 4V127
       + V228 + 2V230 + 3V337
 = 1680 + 70W014 + 12W333 + 6W335 + 8W444 + 7S .
```
This is an unconditional identity. In particular neither V024 nor V226 occurs. The [short exact checker](norm18_u226_lower.py) builds the [full native higher-degree harmonic rows](higher_moments.py) using their four raw-to-unit substitutions, appends no vanishing constraints, and reduces the displayed target by rational Gaussian elimination to zero. Normalization is W000=1. The right side consists only of nonnegative actual population quantities and the constant 1680.

If the only selected types allowed are neutral norm 18, neutral norm 24 and signed-unit charge two cost 26, then V018≥35. The same inequality holds whenever the seven positive unit terms other than V018 on the left vanish; nonzero V016,V020 cannot weaken it. In a fixed maximal H, 8V018 counts **oriented** eligible neutral norm-18 graph markings, not graphs or projective lines, so at least 280 such markings are required in every H. No equality of counts in different residue classes is assumed. The [all-rank eligibility average](norm18-population-caps.md) is E_H[V018]=N18/p, p=7^((44−r)/2)+1. Therefore the graph-wide oriented count satisfies N18≥35p in these cases.

In particular on the three-type support above, the following compare lower and upper bounds on exactly the same oriented graph fields. The upper bound at rank 38 is the [no-norm-16-or-20 graph packing](panel-heights.md); at 40 and 42 also use the [maximal-extension mass cap](norm18-population-caps.md).

| Seidel rank | lower | upper |
| ---: | ---: | ---: |
| 38 | 12,040 | 16,166 |
| 40 | 1,750 | 9,924 |
| 42 | 280 | 1,588 |

The [rank-38 active-square result](u226-rank38-forcing.md) gives a different lower bound on the **charge-two** population; that count is not added to the numbers in this table. None of these intervals is empty. There is no new rank or support exclusion here.
