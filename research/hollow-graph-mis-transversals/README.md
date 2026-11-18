# Hitting all maximal independent sets in a graph with no small maximal independent set

Fix a constant $0<c<1$. For **every sufficiently large** $n$, there is an $n$-vertex graph in which every inclusion-maximal independent set has at least $cn$ vertices, but any vertex set intersecting all of them has size at least

$$
b_c\sqrt{n\log n},\qquad b_c>0.
$$

For this family the minimum hitting-set size is $\Theta_c(\sqrt{n\log n})$. The upper bound applies **only** to the constructed family. The conjecture of Bollobás, Erdős and Tuza that a sublinear hitting set always suffices under the hypothesis remains open. “Maximal” means that no vertex can be added, not that the independent set has the largest possible size.

The starting point is [Cooper and Hollars, Theorem 1.7 and Lemma 3.1](https://arxiv.org/abs/2607.15486v1), who attach an independent reservoir to a graph by random edges and obtain a hitting-set lower bound of order $n^{1/3}/\log n$. Here the other vertices form disjoint cliques. If a proposed hitting set is small, one can choose a representative outside it in each clique so that the representatives collectively have neighbors at every forbidden reservoir vertex. Adding all the remaining reservoir vertices that see no representative produces a maximal independent set avoiding the proposed hitting set. Two simultaneous estimates ensure this works even when the proposed set meets **both** parts.

[Proof](PROOF.md) · [Independent mathematical review](REVIEW.md) · [Sources and scope](SOURCES.md) · [Finite checks](CHECKS.txt).

AI-assisted research, with independent internal AI review. Neither external peer review nor proof-assistant verification has been performed. No priority claim.
