# When is random colouring optimal for a three-red, one-blue four-cycle?

Fix the red-edge density $p$ in a red/blue complete graph. Count four-cycles with three red edges and one blue edge (RRRB); their two diagonals are unrestricted. The question is whether a quasirandom colouring maximizes this count. It is **not** the alternating RBRB question.

Write $p_*=(1+\sqrt{4-2\sqrt2})/4\approx0.52059805$. The [threshold proof](THRESHOLD.md) gives the following asymptotic answer:

| Red density | Is quasirandom optimal? |
|---|---|
| $p_*<p\le1$ | Yes. Every asymptotically maximizing sequence is quasirandom. |
| $p=p_*$ | Yes, but a nonconstant two-class construction also attains the maximum. |
| $0<p<p_*$ | No. A two-class construction strictly exceeds the quasirandom value. |
| $p=0$ | The empty graphon is the trivial extremizer. |

The [profile calculation](PROFILE.md) determines the maximum for every $p\in[1/2,1]$. At $p=1/2$ its value is $(21+5\sqrt5)/512$ for labelled copies per $n^4$, or $(21+5\sqrt5)/1024$ for the undirected cycles counted by Basit et al. **No exact maximum below $1/2$ is claimed here.**

Basit, Granet, Horsley, Kündgen and Staden proved quasirandom optimality for $p\ge(1+\sqrt2)/4$; their question about extending that range is immediately *before* Problem 9.3 in [§9.1 of their paper](https://arxiv.org/abs/2501.09842v2). Problem 9.3 itself concerns alternating four-cycles.

**Verification:** [operator and counting checks](REVIEW.md) and [references and scope](SOURCES.md). AI-assisted research and internal AI review; not externally peer reviewed. No priority claim.
