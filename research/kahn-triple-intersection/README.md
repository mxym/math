# Kahn's triple-intersection cover question: active research

This direction starts from Kahn 1994, Section 5, Conjecture 5.5:
for fixed c and intersecting r-uniform families with m<=cr and
maximum common intersection of three distinct edges o(r), must
tau<=(c/(c+1)+o(1))r hold? The primary statement is in auxiliary
dual form, with r denoting its regular degree. The available limited
screen has not verified the conjecture's present resolution status;
we do not assert that it remains open in all subsequent literature.

The [route obstruction](TRIANGLE_ROUTE_OBSTRUCTION.md) gives an
explicit affine-design realization of the local triangle issue
already described by Kahn in Section 5. It has triple intersections
at most two but integrality gap exactly 4/3. Therefore the new
unconditional fractional-cover envelope cannot simply be rounded
to the same value under the triple-intersection hypothesis.

This is a research obstacle record, **not a new breakthrough or a
counterexample to Conjecture 5.5**. The construction satisfies the
conjectured harmonic bound. The next missing mathematical step is
to control integer cover cost while accounting for local odd-set
obstructions, rather than assuming they disappear with small
triple intersections.

The [local-weight count](LOCAL_WEIGHT_SLACK.md) gives a precise
surplus inequality for Kahn's particular fractional weights. It
explains why those weights can behave differently from an optimum
on the triangle example, and records the unproved global rounding
step rather than assuming it.

```sh
python3 check_triangle.py
python3 -O check_triangle.py
```

The checker uses exact incidence, explicit covers, primal/dual
fractional certificates and counting lower bounds. The written
argument applies to every prime power and every affine dimension
at least two; the finite checker supplies diagnostics only.

Source: J. Kahn, *On a Problem of Erdős and Lovász. II: n(r)=O(r)*,
JAMS 7 (1994), 125–143, Section 5, printed pp.140–141;
DOI https://doi.org/10.1090/S0894-0347-1994-1224593-5.
Conjecture 5.5 and the original local triangle mechanism are prior
work. The repository's fractional envelope remains a separate
fractional theorem.
