# Exact graph-tensor exponent of a triangle with a pendant star

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Let H be a logarithmically weighted triangle ABC with weights AB=x≥AC=y≥0 and BC=z≥0. Attach leaves D_i only to A, with weights t_i≥0, and put t=Σ_i t_i. Then the asymptotic rank exponent over any field, with the pinned OpenAI rectangular-exponent theorem, is exactly R(x+t,y,z), i.e. grouping all leaves with B loses no exponent. This uses [Zhou, Theorem 5.6 and Lemmas 5.1, 5.4](https://arxiv.org/html/2610.34273v3#S5.SS3) and [OpenAI rectangular exponent, pinned Lean theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean#L45). These tools, not a new unqualified claim about C5, are essential; no priority assessment.

**Lower.** Regard B and every D_i as a single party. Every term in any rank decomposition remains a simple tensor on grouping, and tensor powers commute with grouping. The grouped graph has triangle weights (x+t,y,z), so its exponent is a lower bound for H.

**Upper.** Write a=x+t. For y,z>0, test the copositive quadratic constraint with coordinates a y/z, x, y, t_1,…,t_k on A,B,C,D_1,…,D_k. If L=ay/z, the left side divided by 4 is at least
L(xp_AB+yp_AC+Σ_i t_i p_ADi)+xy p_BC+Σ_i (x t_i p_BDi+y t_i p_CDi).
As x≥y and p≥0, the last sum dominates yΣ_i t_i (p_BDi+p_CDi)≥yt p_BC by the triangle inequalities. Since xy+yt=Lz, we have bounded L times the desired objective by (L+x+y+t)^2/4. Hence the upper bound is
 ((a+y)z+ay)^2/(4ayz).
By symmetry of the expression, this gives the exact rectangular exponent as long as the positive-part correction in R is active or at its zero boundary. Write X≥Y≥Z for the decreasing arrangement of a,y,z; the condition is (X+Y)Z≥XY. The estimate is directly on Zhou's path-strengthened CP program, so also proves that program exact in this class when combined with the grouping lower bound.

**Inactive regions.** Since a≥y, the small coordinate is z or y.
- If z≤ay/(a+y), increase z to that threshold. The resulting active-boundary graph has exponent a+y by the above; the original graph attains at least a+y via the cut of A versus all other parties. Monotonicity gives equality.
- If y≤az/(a+z), with y>0, this requires a>y. Put z0=ay/(a−y)≤z and use the active-boundary graph with BC weight z0 (where its exponent is a+z0). Add a separate BC edge of weight z−z0; tensor products at the same parties add an upper bound on log-asymptotic rank. A cut containing A and C versus the remaining vertices attains a+z, so equality holds.
- If y=0 or z=0 (including a=0), all positive edges are bipartite and the total edge weight is the answer. Edges of arbitrary rational weights can be realized by common scaling, and continuity gives the corresponding real-weight formula in Zhou's weighted notation. On the upper program itself the same inactive steps work by monotonicity and subadditivity of the support function U_CP^Δ; an individual edge has value its own weight because p≤1.

**Application to C5.** Each four-part nontrivial coarsening identifies exactly two vertices. Adjacent vertices give an unweighted square after dropping the internal edge, exponent 4. Nonadjacent vertices give an unweighted triangle with weight 2 on a pendant edge, exponent 49/12. Thus all direct four-part coarsenings, even if solved exactly, cannot improve the existing 49/12 lower bound for C5. This does not assert a bound for four-party targets obtained after preliminary splicing, arbitrary local linear projections, or non-graph intermediates.


## Stronger coarsening barrier

If L_1⊗...⊗L_5 is any local restriction of the original five-party tensor (or of k copies aggregated at each original party), grouping according to a fixed partition π commutes with these maps: apply ⊗_{i∈P}L_i in each final group P∈π. The same observation holds for local degenerations by applying the grouping isomorphisms coefficientwise. Thus the final grouped target, even if non-graph, has asymptotic rank no greater than that of the original tensor grouped by π (multiplied by k in the exponent for k copies). The exact ranks of the two four-part coarsenings bound all coarser partitions, since every partition with ≤4 blocks is coarser than some four-block partition. Therefore *any* fixed final coarsening to at most four groups, after arbitrary preliminary local restrictions or degenerations that preserve the original party labels, cannot beat 49/12. This is not an assertion about operations that first split a party into separate parties, nor about inequalities combining several ranks in a more elaborate way.

## CP/SDP equality without the OpenAI exact lower theorem

Zhou's Proposition 6.2 identifies all path-strengthened triangle CP and SDP values with the displayed R formula independently of whether the tensor lower bound is tight. For the star graph, start with an optimal triangle strengthened SDP feasible P and give every D_i the same Gram vector as B. Then p_DiB=0 and p_DiDj=0; other entries copy the B distances, so the triangle inequalities and positive semidefiniteness both stay valid. The objective on the pendant star is the triangle objective with AB increased by t. This proves U_SDP^Δ(H)≥R, and the rational CP upper certificate above gives U_CP^Δ(H)≤R. Thus both conic values are exactly R independently of the exact rectangular lower; only the active-case tensor equality depends on the pinned OpenAI theorem. The inactive graph tensor equality follows already from Zhou and max cut.
