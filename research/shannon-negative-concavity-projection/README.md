# The Shannon projection norm fails for some non-log-concave convex measures

For a symmetric planar random vector $Z=(X,Y)$, consider the candidate norm
$$
u\longmapsto \exp h(\langle u,Z\rangle),\qquad u\ne0,
$$
with value zero at the origin. Here $h$ denotes Shannon differential entropy (order $p=1$). Its triangle inequality applied to the coordinate vectors would read $e^{h(X+Y)}\le e^{h(X)}+e^{h(Y)}$.

**Result.** For every $H>0$, there is a full-dimensional, coordinatewise symmetric planar probability law, jointly $\kappa$-concave for some finite $\kappa<0$, such that
$$
e^{h(X+Y)}>H\big(e^{h(X)}+e^{h(Y)}\big).
$$
The witness can have compact support, and every nonzero one-dimensional projection has finite entropy. The parameter $\kappa$ is allowed to depend on $H$. This disproves the extension to all convex measures in [Madiman–Melbourne–Xu, Conjecture 3.22, arXiv v2](https://arxiv.org/pdf/1604.04225v2#page=29), and [Li, Conjecture 3.1, arXiv v2](https://arxiv.org/pdf/1704.02634v2#page=7). **The Ball–Nayar–Tkocz conjecture for symmetric log-concave measures remains open; this construction is not log-concave.**

The construction mixes uniform laws on nested rectangles. Most of the first range of logarithmic scales has wide horizontal cross-sections; most of the second has narrow ones. The two ranges have equal limiting probability. The diagonal projection picks up the wider coordinate in both ranges, whereas the opposite changes in horizontal width cancel on averaging their logarithms. A single convex potential produces this change of aspect ratio without losing joint $\kappa$-concavity. Strict violation persists when one conditions on a sufficiently large rectangle.

[Proof](PROOF.md) · [Independent check of the entropy limit](REVIEW.md) · [Earlier results and scope](SOURCES.md). AI-assisted research with independent internal AI review, not external peer review or a formal proof-assistant check. No priority claim.
