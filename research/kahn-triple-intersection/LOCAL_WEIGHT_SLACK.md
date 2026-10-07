# A local counting inequality for the alternative rounding route

This lemma is a proved counting step, not a solution of Kahn 5.5.
Its historical novelty has not been assessed.

Work in auxiliary form. Let J have m>=1 points, every point degree r>=1,
block size at most a fixed D, positive codegree for every distinct
pair of points, and maximum triple codegree lambda. For each block B
use Kahn's weight t(B)=|B|/(m+r-1). This is a fractional edge cover:
at a point p, summing |B|-1 over incident blocks counts every other
point at least once, so sum_{B containing p}|B|>=m+r-1.

For a fixed subset S of h>=1 points put ell=ceil(h/2). Then

```
sum_{B meeting S} t(B)
 >= [h r + ell (m-h-D*binom(h,3)*lambda)]/(m+r-1).
```

Proof: at most binom(h,3)*lambda blocks meet S in at least three
points, since each such block contains one of its triples. Their
union contains at most D*binom(h,3)*lambda points. An outside point
p beyond that union must meet all h members of S through blocks
containing p and at most two points of S, so it belongs to at least
ell distinct blocks meeting S. Sum these outside incidences. The
inside incidences total exactly h r. Their sum proves the formula.
If the displayed outside lower bound is negative, zero outside
incidences still satisfy it. The denominator is positive.

When h,D are fixed, lambda=o(r) and m/r is bounded, this lower bound
is strictly above ell for h>=2 at all sufficiently large r. Indeed
the numerator minus ell*(m+r-1) is

```
(h-ell)r - ell*(h-1+D*binom(h,3)*lambda) >0.
```

For h=1 the lower bound is exactly one. This is evidence for a
route using Kahn's specific fractional weights and their local
surplus, rather than arbitrary optimum weights. It is not by itself
an integral-cover distribution or a global rounding theorem.

On the triangle construction, the optimal weights put total 3/2
on the blocks meeting any one local triple. Kahn's weights instead
put total

```
6s r0/(m+r-1) -> 6s/(3s-1) >2
```

there. The local triangle's integer cover requirement is two. Thus
these particular weights have enough local surplus in this example,
even though rounding the optimum with negligible loss is impossible.

Remaining gap: construct a compatible global cover/rounding theorem
from such local inequalities under small triple codegrees, accounting
for arbitrary local odd-set obstructions. No statement that these
inequalities alone suffice is made here. The current status of the
relevant Kahn/Kayll results is still being checked from primary sources.
