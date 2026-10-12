# Diffuse optimal fractional covers and integer recovery

[Complete written proof](paper.md) · [Six-page PDF](paper.pdf) ·
[Self-review](AUDIT.md) · [Exact checker](check_exact.py) ·
[Partial Lean scope](formal/README.md).

Let H be simple and intersecting, with m nonempty edges of rank at most
r>=2 and maximum vertex degree at most D>=3. Put

\[
 \Delta=(D-1)m-D(D-2)r-D>0,\qquad K_D=D(D-2).
\]

We prove that an optimal fractional vertex cover of value m/D exists with
every coordinate at most

\[
                 1/\lceil\Delta/K_D\rceil\le K_D/\Delta.
\]

The proof deletes all maximum-weight vertices of a minimax optimum,
repairs intersections using three complementary groups, and applies the
previous finite fractional bound. The repair raises rank by only one per
removed incidence and introduces vertices of degree below D, which an
optimum of value m/D must avoid. The claim concerns the existence of a
diffuse optimum, not every optimum.

For fixed D, r->infinity, m/r->c, and maximum triple intersection o(r),
we establish

\[
 \tau(H)=m/D+o(r),\quad \tau^*(H)=m/D\text{ eventually},\qquad
 c\in\left(D-1-\frac{2}{3D(D-2)+2(D-1)},D-1\right].
\]

Thus D=3 gives c in (24/13,2], and D=4 gives c in (44/15,3]. Pair
intersections may be of order r. The conclusion also applies to
fractional extremizing sequences after the previously proved o(r)-edge
degree-core extraction, on these same noninteger intervals.

The integer result imports Kayll's bounded-size rounding theorem and
Edmonds's graph matching polytope characterization. The paper explicitly
proves the diffuse certificate, local pair budget, higher-coordinate
mixture and all remaining implications. It does not resolve the entire
Kahn 5.5 question, the rest of the strict ramp, or Ryser's conjecture.
No priority or external human-review claim is made.

## Reproduction

```sh
python3 notes/diffuse-fractional-cover-rounding/verify.py
bash notes/diffuse-fractional-cover-rounding/build.sh
cd notes/diffuse-fractional-cover-rounding/formal
bash bootstrap.sh
cd ..
python3 verify.py --lean
```

Python uses only the standard library. The PDF build uses Pandoc and
pdfLaTeX and defaults to `/tmp/diffuse-fractional-cover-paper`; it does
not overwrite the frozen PDF. Lean uses pinned Lean 4.34.1 and Mathlib
commit d13f23b723b8a846827a245b89c10fc7d3f11612. The bootstrap was
actually replayed with available dependency caches. Six finite exports
pass with standard Lean axioms and no `sorryAx` or `native_decide`.
The full minimax and asymptotic theorem are not Lean formalizations.

The checker uses exact rational arithmetic, actual edge/block incidence,
36 explicit repairs including 30 across degrees 3--12, primal/dual
certificates, 592 local incidence diagnostics, a full matching
distribution with a higher subset, and negative controls for the
triangle obstruction and invalid extension to D=2. Both ordinary and
optimized Python must reproduce the frozen output. These diagnostics
do not replace the infinite proof or imported theorems.

The source/dependency map is [source-lineage.json](source-lineage.json).
The finite fractional theorem and edge-core extraction are earlier
repository results at commit c5255a. Sources and their exact roles are
in [results/source.txt](results/source.txt). A separate
[limited literature comparison](../../research/novelty-assessment/2026-10-07-bounded-degree-fractional-cover-repair-screen.md)
was prepared with the user-requested GPT-6 Luna High agent, which did
not review this proof. Frozen payload hashes are recorded in
[MANIFEST.json](MANIFEST.json) and [SHA256SUMS](SHA256SUMS).
