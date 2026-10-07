# Additive continuation: diffuse optima and partial integer recovery

The separate [diffuse-cover note](../diffuse-fractional-cover-rounding/README.md)
uses this package's finite bound and strict-ramp degree-core extraction.
It does not modify any frozen predecessor payload.

For maximum vertex degree D>=3 and
Delta=(D-1)m-D(D-2)r-D>0, it proves the existence of an optimal cover of
value m/D with coordinates at most 1/ceil(Delta/[D(D-2)]). The new
three-complement repair increases rank by one per removed incidence;
an optimum avoids the replacement vertices because their degrees are
strictly below D. Minimizing the maximum coordinate gives the bound.

With maximum triple intersection o(r), it derives integer recovery on
the explicit interval

`m/r -> c in (D-1-2/[3D(D-2)+2(D-1)],D-1]`.

The new note checks Kayll's local matching-polytope hypothesis, rather
than replacing it by a cover-cost inequality. Edmonds and Kayll are
attributed imported inputs. The finite coordinate and repair results
are independent of those inputs. This does not settle the whole ramp
or the general Kahn 5.5 question. Six selected finite Lean checks do
not constitute a formalization of the full new paper.
