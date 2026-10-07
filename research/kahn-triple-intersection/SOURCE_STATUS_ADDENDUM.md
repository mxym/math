# Later same-day source-status addendum

The frozen research record at commit fe32e5f is preserved. A subsequent
primary-source check found P. Mark Kayll's DIMACS Technical Report 95-55
(December 1995), *Asymptotically Good Covers in Hypergraphs: Extended
Abstract of the Dissertation*, Theorem 2.1, printed p.5:
https://archive.dimacs.rutgers.edu/archive/TechnicalReports/TechReports/1995/95-55.ps.gz

This theorem resolves Kahn's 1994 Conjecture 5.6 and allows a fractional
cover instead of only a fractional tiling, with fixed rank, alpha3(t)->0
and b(t)->infinity. The report names the later Kahn–Kayll 1997 manuscript
as the full proof venue. The complete journal paper has not been accessed
in this environment; its theorem statement is independently visible in
the primary dissertation report. See the [full limited source comparison](../novelty-assessment/2026-10-07-kahn-followup-edge-count-screen.md).

This does not establish Conjecture 5.5, whose current status remains
unverified by this finite screen. In particular, b(t) is a *matching*
polytope condition on all local coordinates of size at least two, not
simply an integer-cover lower-bound constraint. When triple coordinates
vanish, projected pair weights must obey graph matching odd-set upper
bounds. The positive local cover-cost surplus in LOCAL_WEIGHT_SLACK.md
does not prove those upper bounds and cannot be substituted for b(t).
The triangle example itself does not satisfy the needed matching condition.

Thus the local surplus is a correct counting lemma, but the proposed
general integer rounding remains unproved. Neither the existing Kayll
result nor the surplus lemma is advertised as a new resolution here.
