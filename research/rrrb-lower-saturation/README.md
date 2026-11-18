# How far does the two-class RRRB formula remain sharp?

Let $M(p)$ be the largest asymptotic density of a four-cycle with three consecutive red edges and one blue, at red-edge density $p$. The [preceding note](../rrrb-quasirandom-threshold/README.md) computed $M$ on $[1/2,1]$ using an operator upper bound $U(p)$. This continuation extends the exact profile down to
$$
p_0=0.3205350674\ldots,
$$
the unique root in $(1/4,1/3)$ of $65536p^4-86528p^3+39133p^2-5378p-139$.

| Red density | What is determined |
|---|---|
| $p_0\le p<1/2$ | $M(p)=U(p)$; the [formula](PROOF.md) and an unequal two-class attaining graphon are explicit. Together with the preceding note this determines $M$ on $[p_0,1]$. |
| $p=p_0$ | The maximizing graphon is unique up to graphon equivalence: one block is a clique, one is independent, and the cross-edge probability is fixed. |
| $0<p<p_0$ | $M(p)<U(p)$. Neither the true value nor the shape of its maximizers is determined here. |

The lower point $p_0$ concerns **attainment of one scalar upper bound**, not quasirandom optimality. The latter has the different threshold $p_*\approx0.52059805$ in the preceding note. Failure of the bound to be sharp below $p_0$ does not prove a singularity of $M$, or exclude other two-class optimizers.

[Proof](PROOF.md) · [Feasibility on the remaining interval](FEASIBILITY.md) · [Two checks of the critical root](ALGEBRA.md) · [Sources and review](REVIEW.md). The normalization is labelled injections divided by $n^4$, so divide the profile here by two for the undirected count of Basit et al. AI-assisted research and independent internal AI review; not externally peer reviewed. No priority claim.
