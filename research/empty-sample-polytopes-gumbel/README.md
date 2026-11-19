# Gumbel limits for the largest empty polytopes with a fixed number of sample vertices

**Yongxian Zhang · 19 November 2026**

Draw $n$ independent uniform points in a fixed $d$-dimensional convex body $K$, $d\ge2$. Fix $k\ge d+1$. Among convex polytopes whose **exactly $k$ vertices** are sample points and whose interiors contain no other sample point, let $M_{n,k}$ be the largest volume, **divided by $|K|$**. Write $m=k-d$ and $A=c_{d,k,K}d^{m-1}/\Gamma(m)$, where $c_{d,k,K}>0$ is the [known leading constant](../empty-k-holes-leading-limit/PROOF.md) for the mean total number of empty $k$-vertex polytopes divided by $n^d$. Then
$$
 \Pr\!\left(nM_{n,k}-d\log n-(m-1)\log\log n\le x\right)
 \longrightarrow \exp(-A e^{-x})
$$
for every real $x$. The number of polytopes above that threshold converges to a Poisson variable of mean $Ae^{-x}$. For planar triangles $A=2$ and there is no log-log centering term.

- [Poisson and Gumbel proof](GENERAL.md). Planting a typical large empty polytope can create or destroy others. Transverse thin hulls scarcely overlap; nearly parallel pairs either pay a large emptiness cost or have almost identical vertices in normalized coordinates. Those dependency estimates are what turn the mean into a law.
- [Volume density and mean exceedance profile](EXTREME-COUNTS.md). The projected-anchor chart identifies the constant at the extreme threshold.
- [Almost-sure bounds for simplices](ALMOST-SURE.md). When $k=d+1$, the difference $nM_{n,k}-d\log n$ is eventually $O_d(\log\log n)$ almost surely, with the nonsharp one-sided constants in the proof. The positive tail is at most $C_d e^{-x}$ at fixed $n$. The first-order sample-simplex growth was already proved in [#231](https://github.com/mxym/math/pull/231).

One lower consequence for the maximum $V_n$ **without** a vertex-count limit (and also for the largest empty convex body) is $(nV_n-d\log n)/\log\log n\to+\infty$ in probability: for any fixed target, choose a fixed $k$ with $k-d-1$ larger, and use $V_n\ge M_{n,k}$ and the tight centered fixed-$k$ law. This supplies neither a sharp unrestricted rate nor an unrestricted Gumbel law; no priority is claimed for this implication. The theorem itself does not allow $k=k(n)$ or establish a joint point-process limit.

[Primary sources and scope](SOURCES.md) · [independent internal review of the distributional proof](GENERAL-REVIEW.md) · [review of the first moment and pathwise simplex bounds](REVIEW.md). The work and separate internal reviews were AI-assisted; the initial second-order and marked-mean derivations arose in background AI research. Not externally peer-reviewed or formally verified; no priority guarantee. The standard-library command `python3 -B -O check.py` checks finite occupancy and algebraic identities ([output](CHECKS.txt), [hashes](SHA256SUMS)); it does not simulate or prove a limiting law.
