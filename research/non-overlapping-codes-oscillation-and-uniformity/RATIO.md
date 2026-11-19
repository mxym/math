# A separate implication for the one-run to unrestricted size ratio

Use S (one-run maximum), C (unrestricted maximum), a=1−1/q, h(x)=x exp(−x), ξ=q log(q)/(q−1), as in the main proof. [Chee–Kiah–Purkayastha–Wang, IEEE TIT 2013, Theorem 4.1, Eq. (6), p.4671](https://personal.ntu.edu.sg/hmkiah/docs/papers/cbfcode.pdf) asserts liminf S(n,q)/C(n,q)≥2a/e. For each fixed q≥8 this inequality fails. No upper bound on C or result on the optimal binary constant is needed for this conclusion.

Indeed, along the minimizing sequence in A the normalized S tends to a h(ξ), whereas B gives liminf nC/q^n≥a/e. Thus liminf S/C≤e h(ξ). For real q>1, ξ>1 and ξ'=(q−1−log q)/(q−1)²>0, so this upper bound strictly decreases with q and the asserted lower bound increases. At q=8, log 2>2/3 by strict Jensen on x↦1/x on [1,2]. Hence ξ>16/7. Now e h(16/7)<7/(4e), since the equivalent inequality exp(2/7)>64/49 follows from 1+2/7+(2/7)²/2=65/49. This proves the strict contradiction for q≥8.

If in addition one invokes the fixed-q limit nC/q^n→a/e of the earlier repository manuscript, the exact ratio limits are liminf S/C=e h(ξ) and limsup S/C=1. The contradiction above is independent of that extra result. The unrestricted-optimum lower bound (Theorem 1.1, Eq. (1)) is preserved, not contradicted.
