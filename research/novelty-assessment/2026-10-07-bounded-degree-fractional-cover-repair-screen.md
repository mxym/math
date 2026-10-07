# Bounded-degree fractional-cover repair: limited prior-work screen

Screen date: 2026-10-07. This is a bounded source comparison, not a proof review or a priority claim. The candidate theorem and its proposed consequence are taken as supplied by the authors.

## Candidate compared

For a finite simple intersecting hypergraph of rank at most `r`, maximum vertex degree `D≥3`, and `m` edges, set

`Δ=(D−1)m−D(D−2)r−D`.

In the strict region `Δ>0`, the candidate uses the fractional-cover frontier `τ*=m/D`. Every optimal fractional vertex cover is claimed to be supported only on degree-`D` vertices and to have load exactly one on every edge. The stronger coordinate statement is existential: the candidate claims there is an optimal cover whose every coordinate is at most `1/ceil(Δ/[D(D−2)])≤D(D−2)/Δ`. This distinction matters; the supplied exact parallel-class example has an optimal cover with maximum coordinate 1, above the diffuse-optimum cap. The revised repair replaces a removed degree-`D` vertex by three new vertices: partition its `D` incident edge labels into three nonempty groups and put each new vertex on the complementary groups. Each incident edge receives two replacement vertices in place of the removed one, each new vertex has degree at most `D−1`, and the candidate states that the symmetric-difference distinguishing vertex and its replacement preserve simplicity. The revised minimax/deletion bookkeeping yields the diffuse optimum; this screen does not check that argument.

The proposed asymptotic implication fixes `D` and sets

`χ_D=D−1−2/[3D(D−2)+2(D−1)]`.

For sequences with `r→∞`, `m/r→c∈(χ_D,D−1]`, and maximum triple intersection `o(r)`, it claims fractional-cover equality at scale `m/D` forces `τ=τ*+o(r)` by passing to the dual bounded-rank hypergraph and using a Kayll rounding theorem. This screen does not assess either argument.

## Closest sources read

1. **Zoltán Füredi, “Maximum Degree and Fractional Matchings in Uniform Hypergraphs,” *Combinatorica* 1(2) (1981), 155–162, DOI [10.1007/BF02579271](https://doi.org/10.1007/BF02579271).** Full text read; local copy `/tmp/furedi_007_cca1981_fractional_matchings.txt`. Its main theorem is for rank-`r` hypergraphs with matching number `v`: absent `p+1` pairwise-disjoint projective-plane subhypergraphs, `τ*(H)≤(r−1)v+p/r`. Corollary 3 says that an intersecting **r-uniform** hypergraph is either a projective plane of order `r−1`, with maximum degree `m/(r−1+1/r)`, or has maximum degree at least `m/(r−1)`. This is a close rank/degree/fractional-matching precedent, but it gives neither the candidate’s `Δ`-dependent bound on individual optimal-cover weights nor a deletion stability statement. Its exceptional projective-plane scale has `m=Θ(r²)`, unlike the candidate’s fixed-`D`, linear-`m` regime.

2. **Zoltán Füredi, Jeff Kahn and Paul D. Seymour, “On the Fractional Matching Polytope of a Hypergraph,” *Combinatorica* 13(2) (1993), 167–180, DOI [10.1007/BF01303202](https://doi.org/10.1007/BF01303202).** Full text read; local copy `/tmp/furedi_121_kahn_seymour_fractional_matching_polytope.txt`. Theorem 1.4 is a weighted fractional-matching inequality for an intersecting hypergraph; Theorem 1.5 gives an intersection-sum extremal bound for uniform intersecting hypergraphs, with projective-plane equality. Neither theorem is parameterized by a maximum vertex degree and rank margin of the form `Δ`, and neither gives support-weight concentration or repair-by-deletion.

3. **P. Mark Kayll, *Asymptotically Good Covers in Hypergraphs: Extended Abstract of the Dissertation*, DIMACS Technical Report 95-55 (1995), Theorem 2.1, [report record and PDF](https://archive.dimacs.rutgers.edu/TechnicalReports/abstracts/1995/95-55.html).** The 11-page report was read in full (`/tmp/kayll95-55.txt`; PDF `/tmp/kayll95-55.pdf`). For fixed `k`-bounded hypergraphs and fractional covers `t`, Theorem 2.1 gives asymptotic integral edge-cover rounding under `α₃(t)→0` and `b(t)→∞`. This is the relevant known rounding input after dualizing the candidate family: maximum degree `D` becomes dual edge size at most `D`. It supplies the rounding tool, not the candidate’s strict threshold `χ_D` or a theorem deriving its hypotheses from the proposed optimizer repair.

   The corresponding journal paper is Jeff Kahn and P. Mark Kayll, “Fractional v. Integral Covers in Hypergraphs of Bounded Edge Size,” *Journal of Combinatorial Theory, Series A* 78(2) (1997), 199–235, DOI [10.1006/jcta.1997.2761](https://doi.org/10.1006/jcta.1997.2761). The journal citation is metadata-verified; the accessible full primary text in this screen is the DIMACS dissertation extended abstract, not the journal version.

4. **Georg Gottlob, Matthias Lanzinger, Reinhard Pichler and Igor Razgon, “Fractional Covers of Hypergraphs with Bounded Multi-Intersection,” arXiv:2007.01830v4 (2023), [arXiv](https://arxiv.org/abs/2007.01830).** Full text read (`/tmp/2007.01830.txt`). Theorem 34 gives bounded-support replacement for fractional vertex covers under a bounded multi-intersection condition, preserving specified covered-neighborhood data. It is structurally adjacent to support control, but its purpose and hypotheses differ: it does not give the candidate’s existential diffuse-optimum coordinate cap, restrict optimal-cover support to maximum-degree vertices in this intersecting-family setting, or bound deletion cost by the candidate’s fractional margin.

## What appears to be standard versus not directly matched

Once `τ*=m/D` is known, the two properties asserted for every optimizer—“support lies on degree-`D` vertices” and “each edge constraint is tight”—are standard complementary-slackness consequences of the feasible fractional matching assigning weight `1/D` to every edge. They should not be presented as independent prior-work breakthroughs. The candidate’s existential diffuse-optimum coordinate cap and the minimax repair/deletion mechanism are the substantive additional claims under comparison here.

The sources above contain (i) rank-versus-maximum-degree and fractional matching bounds (Füredi), (ii) general intersecting fractional-matching polytope inequalities (Füredi–Kahn–Seymour), (iii) fractional-to-integral rounding under bounded-rank local conditions (Kayll / Kahn–Kayll), and (iv) a different bounded-multi-intersection support-compression theorem (Gottlob et al.). None of the read theorem statements directly gives the candidate’s explicit diffuse-optimum cap `1/ceil(Δ/[D(D−2)])`, its revised three-group deletion/replacement inequality, or the value `χ_D` and resulting near-equality criterion. The revised formula gives `χ_3=24/13` and `χ_4=44/15`.

The Kayll theorem should be attributed as an existing rounding input, not as a new method. Conversely, a limited non-hit for the proposed repair/stability statement is not evidence that it is new or that related results do not exist.

## Search boundary

This pass read the four primary texts listed above (with the qualification that the 1997 Kahn–Kayll journal article itself was not accessible; its dissertation extended abstract was read). A finite arXiv search for fractional vertex covers, intersecting hypergraphs, degree, and stability returned the Gottlob–Lanzinger–Pichler–Razgon paper as the closest direct support-control match; targeted searches did not surface a theorem with the candidate’s rank/degree margin or delete-and-repair conclusion. This is a limited screen only; no exhaustive citation-chain review was attempted.
