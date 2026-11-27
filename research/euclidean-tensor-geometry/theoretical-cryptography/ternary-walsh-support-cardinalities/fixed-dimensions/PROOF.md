# Fixed-dimensional supplement

Let `omega=exp(2*pi*i/3)` and

```
W_f(u) = sum_x omega^(f(x)-u*x),   S_f={u:W_f(u) != 0}.
```

Write `C_n={|S_f|: f:F_3^n -> F_3}`.  The frozen parent theorem proves that
the only positive sizes excluded from the union of all `C_n` are

```
F={2,4,5,8,10,11},
```

and proves the exact sets for `n=1,2,3`.  No exclusion is reproved here.

## Theorem 1: dimensions 4 through 7

For `n=4,5,6,7`,

```
C_n = {1,...,3^n} minus F.
```

The upper inclusion follows from the six global exclusions.  For the reverse
inclusion, `witnesses-fixed.json.gz` gives one ternary truth table of length
`3^n` for every stated size: respectively 75, 237, 723 and 2,181 tables.

The generator begins with independently checked three-variable tables for
the 21 possible sizes through 27.  At each round it applies invertible affine
input changes, output conjugation and affine output terms, plus deterministic
local mutations, to make a fixed pool.  Three pool tables become the three
slices in one new variable.  Their spectra are joined exactly in Eisenstein
integer coordinates.  Four fixed LCG seeds locate the complete witness lists:

| output dimension | seed | pool | maximum trials | trials used |
|---:|---:|---:|---:|---:|
| 4 | 42,581,572 | 7,000 | 1,800,000 | 163,281 |
| 5 | 10,861,014 | 6,700 | 1,950,000 | 106,825 |
| 6 | 37,118,503 | 6,700 | 2,450,000 | 446,813 |
| 7 | 71,166,928 | 10,500 | 2,350,000 | 776,359 |

This search is not an exclusion argument.  Once found, every table is a
finite exact certificate.  The independent verifier evaluates its tensor
Fourier transform twice in `F_65521`, at the distinct roots 16673 and 48847
of `X^2+X+1`.  A Walsh coefficient is `a+b*omega` with
`|a|,|b| <= 3^7 < 65521`.  Both projections vanish exactly when `a=b=0`;
there is no numerical tolerance or modular false zero.  The verifier checks
the support count of all 3,216 new tables.

## Corollary 2: minimum dimension through 2187

For every attainable `1 <= s <= 2187`, the minimum positive dimension is

```
max(1, ceil(log_3(s))).
```

The lower bound is `|S_f| <= 3^n`.  Equality with this lower bound follows
from the exact parent classifications for dimensions 1--3 and Theorem 1 for
dimensions 4--7.  The six members of `F` remain impossible in every
dimension and are not assigned a minimum.

## Proposition 3: a certified interval in all larger dimensions

Define `L_6=729`, `L_7=2187`, and

```
L_(n+2)=3 L_n + 11.
```

For every `n>=6`, dimension `n` realizes every size in `[12,L_n]`, as well as
the padded small sizes `1,3,6,7,9`.  For `n=6,7` this is Theorem 1.  For the
induction step use the parent result's two-new-variable join.  If `f` has
support size `s`, and `g,h` are fixed two-variable tables, the joined function
has dimension `n+2` and support size

```
3s + q(g,h).
```

The exact pair counter in `verify_fixed.py` checks

| q | g | h |
|---:|:---|:---|
| 9  | `000111000` | `000000000` |
| 22 | `020100000` | `021000000` |
| 26 | `020211000` | `001200000` |

Use `q=9,22,26` for target residues `0,1,2` modulo 3.  Padding already covers
all targets through `L_n`.  For `L_n < r <= 3L_n+11`, the integer
`s=(r-q)/3` lies in `[12,L_n]`; hence the join covers the remaining targets.
This proves the recurrence.  No claim is made that `[12,L_n]` is maximal, or
that dimensions `n>=8` are fully classified.
