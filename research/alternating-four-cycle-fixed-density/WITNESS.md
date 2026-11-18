# An exactly regular witness at β=2/5

In the notation of Definitions 1–2 of [Balogh et al.](https://arxiv.org/abs/2601.03433v1), count injections from the ordered four vertices (u,v,w,x) into a complete two-coloured host, requiring uv,wx red and vw,xu blue; uw and vx are unrestricted. Write N for this labelled count. For a sequence indexed by every vertex number n one takes the limit N/n⁴ and requires the fraction of red unordered pairs to tend to β. A cyclic shift by one bijects the count with the other choice of alternating colouring; we use only the single prescribed orientation, not its sum with the other.

**Construction.** For m≥1 take the red graph to be the disjoint union of a clique on 2m+1 vertices and a complete tripartite graph with three parts of m vertices each, and all remaining pairs blue. Its order is n=5m+1, every vertex has red degree 2m, and the red density is exactly 2m/(n−1)=2/5.

If the ordered red edges uv and wx are in different components, the two blue conditions hold automatically. This contributes 2(2m+1)(2m)·6m². They cannot both be in the clique. If both are in the tripartite graph, v,w must lie in one part, and x,u in a different part. Thus there are exactly 6[m(m−1)]² further injections. This covers all possibilities, without identifying dihedral or colour symmetries. Consequently
```
N = 54m⁴ + 12m³ + 6m²,
lim N/(5m+1)⁴ = 54/625 = 0.0864.
```
For all sufficiently large orders n take m=floor((n−1)/5) and adjoin at most four vertices with all incident pairs blue to the indicated graph. The red density changes by O(1/n); changing the number of vertices by at most four changes the count by O(n³), since each new copy must meet the added vertices. Hence the sequence satisfies Definition 2. The limiting graphon is exactly 2/5-regular, and the subsequence n=5m+1 even has exact finite regularity and exact finite edge density.

**Comparison.** At β=2/5, Question 1 prescribes k=ceil(5/2)=3 disjoint red cliques, with limiting proportions a,a,b and b≤1/3. Any limit point obeys 2a+b=1 and 2a²+b²=2/5. Substitution gives 30a²−20a+3=0 and b≤1/3 forces a≥1/3, so the only possible proportions are a=(10+√10)/30 and b=(5−√10)/15. In particular possible rounding or oscillation of part sizes cannot change the limit. In a clique union, the two ordered red edges must occupy different cliques, and then both required blue edges occur. Its limiting density equals
```
  (2a²+b²)²−(2a⁴+b⁴)
= 103/1350 + 2√10/675.
```
The difference from our lower bound is (341−100√10)/33750>0, because 341²=116281>100000. Thus the proposed construction does not achieve the supremum.

**Numerical comparisons.** In §4 the cited v1 prints 0.0859499752 as a numerical upper bound at 2/5, and 0.08409772 under regularity. They are smaller than the explicit lower bound. These are reported numerical outputs, not the proved general inequality of Theorem 1.3; we make no claim about the reason for the discrepancy. Indeed 54/625 < (2/5)²(1−2/5)=12/125. We do not claim that the witness is extremal or unique.

*Optional detail on regularity indexed by all orders.* If desired, for all sufficiently large n choose the largest m≤(n−1)/5 satisfying 2m≡n−1 mod 3. Let l=(n−1−2m)/3≥m; l−m is bounded. Use a clique of order 2m+1 and a disjoint graph on three classes of size l, placing an m-regular bipartite graph between each pair of distinct classes (e.g. the union of m cyclic shift matchings). Every vertex has degree 2m. The latter component omits only O(n) pairs relative to the full tripartite graph, and each edit affects O(n²) ordered copies. The class proportions approach 2/5,1/5,1/5,1/5, so this all-n regular sequence has the same limit. Exact edge density at each n is not a hypothesis of the cited question, nor is regularity.
