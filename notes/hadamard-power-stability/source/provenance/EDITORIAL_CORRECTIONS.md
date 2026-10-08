# Editorial corrections made during consolidation

These corrections were reported to the coordinating reviewer before finalization. They do not alter the frozen research revision, external source snapshots, main stability theorems, residual thresholds, or constants. The final manuscript and this new explicit rectangle label should receive the requested limited final-copy recheck by the original reviewer.

## Optional rectangle in the abstract

The first draft said that all-half-order rounding supplies a seed “and a compatible phase rectangle.” The source theorem permits no deformation, and odd half-orders admit no compatible rectangle. The abstract now says “and, when needed, a compatible phase rectangle.” The theorem body already had the correct alternative. This is a consolidation wording correction.

## Corrected label for the external order-four boundary example

The external `general-patterns.md` §6 used the displayed root

```text
G = [ 1  1  1  1
      1 -1  1 -1
      1  1 -1 -1
      1 -1 -1  1 ]
```

and described the last two rows and last two columns as compatible. All indices here are zero-based.

That particular placement is not compatible. With `R_old={2,3}` and `S_old={2,3}`, the row-ratio multiset for `a=2` and `b=0`, restricted to `S_old`, is `{-1,-1}`, rather than `{1,-1}`. If that lower-right block is multiplied by alpha, the row-0 versus row-2 inner product is exactly

```text
1 + 1 - conjugate(alpha) - conjugate(alpha)
    = 2 - 2 conjugate(alpha),
```

which is nonzero when `alpha != 1`. This is a boundary-example ordering error inherited from the external source, not a failure of the exact classification proof or the revised stability curve.

The manuscript's Appendix A uses `R={1,3}`, `S={2,3}` instead. Both sets have size two and exclude the initial index. All cross-group restricted row ratios are:

| Row in R | Row outside R | Ratios on columns (2,3) |
|---|---|---|
| 1 | 0 | (1,-1) |
| 1 | 2 | (-1,1) |
| 3 | 0 | (-1,1) |
| 3 | 2 | (1,-1) |

Each contains each element of `mu_2` exactly once. Thus this rectangle satisfies precisely the paper's compatibility definition. The corresponding exact phase family is

```text
[ 1  1      1      1
  1 -1  alpha -alpha
  1  1     -1     -1
  1 -1 -alpha  alpha ],       |alpha|=1.
```

Same-group row ratios are unchanged, while each cross-group restricted sum is zero on both column halves. This verifies the replacement labels directly. No source snapshot was edited, and no enlarged search or new parameter study was run.

## First use of notation

`V_G` is now defined as the simultaneous dephased first-order kernel before Theorem 5.2, rather than waiting until Section 8. No mathematical statement changed.
