# Finite joint-measurability structures on a real qubit

This gives an affirmative answer to [Andrejic and Kunjwal, Conjecture 4](https://arxiv.org/pdf/2003.00785), as stated for finite sets of qubit measurements without a fixed outcome bound. The outcome count in this construction depends on the structure. It does not assert a binary realization.

**Theorem.** Suppose that K is a downward-closed family of subsets of a finite set V, and contains every singleton and the empty face. There exist distinct finite-outcome POVMs on the two-dimensional complex Hilbert space, with real rational effects, such that a subfamily has a common joint POVM exactly when its vertex set is a face of K. If K has M facets, each setting has at most 2M+1 outcomes. The parents need not be projective.

**Conventions.** A POVM is a finite family of positive semidefinite operators summing to I. A joint POVM for a family is a POVM on its Cartesian product of outcome sets, with the prescribed operator marginals. A finite experiment followed by a separate deterministic response function for each measurement gives such a joint POVM: sum its operators according to the resulting outcome tuple. Conversely a positive Cartesian parent effect is at most each of its corresponding marginal effects in the Loewner order.

**Construction.** If V is empty there is nothing to prove. Otherwise put N=|V|, index the facets by F_1,...,F_M (M≥1), and write A_i={j≤M : i∉F_j}. Each i belongs to at least one facet, so |A_i|≤M−1. On C² choose M+N real projective bases indexed by j=1,...,M+N, with all 2(M+N) one-dimensional ranges different. For example take t_j=j/(M+N+1), and use the + direction (1,t_j) and − direction (−t_j,1); write P_{j,σ} for the corresponding normalized rank-one projectors. The positive directions have distinct positive slopes and the negative directions distinct negative slopes. Rationality follows from the denominator 1+t_j².

Take w=2/(2M−1) and ε=1/[2N(2M−1)]. Measurement i has:
* outcomes (j,σ) of effect wP_{j,σ}, for every j∈A_i and σ∈{+,−};
* two private outcomes (M+i,σ) of effect εP_{M+i,σ};
* one null outcome ⊥ of effect (1−w|A_i|−ε)I.

All effects are positive and normalized, as each basis sums to I and 1−(M−1)w=1/(2M−1). There are at most 2M+1 outcomes. Private rays distinguish measurements up to any relabeling, even when two vertices have the same facet incidences. Distinctness is not otherwise needed.

**Faces.** For S⊆V put J(S)=∪_{i∈S} A_i. The condition S⊆F_j is equivalent to j∉J(S). Thus S∈K iff J(S) misses at least one label. For a face take as parent effects the pairs wP_{j,σ} for j∈J(S), the pairs εP_{M+i,σ} for i∈S, and the residual [1−w|J(S)|−ε|S|]I. The residual scalar is at least 1/[2(2M−1)]>0. If a shared label (j,σ) is drawn, i∈S reports it when j∈A_i and otherwise reports ⊥. A private draw is reported by its owner alone, all other settings reporting ⊥; the residual always reports all-null. This realizes exactly the prescribed marginals (non-null outcomes occur with their required effects, and the null marginal is their normalized complement).

**Nonfaces.** For S∉K we have J(S)={1,...,M}. For each j fix a single representative i_j∈S with j∈A_{i_j}; representatives may coincide. In a putative Cartesian parent (G_x), consider the 2M marginal events E_{j,σ}={x:x_{i_j}=(j,σ)}. For each j the two signs are disjoint. For j≠k and any signs, any x in both events satisfies 0≤G_x≤wP_{j,σ} and G_x≤wP_{k,τ}. Generally, for 0≤G≤cP with P a rank-one projection, ker(P)⊆ker(G) (use the nonnegative square root of G), hence ran(G)⊆ran(P). Two distinct rank-one ranges intersect in zero, so G_x=0. Consequently any nonzero G_x is counted by at most one of the 2M events. Summing and using the observed marginals yields
MwI = Σ_{j,σ}wP_{j,σ} = Σ_{j,σ}Σ_{x∈E_{j,σ}}G_x ≤ Σ_x G_x = I.
But Mw=2M/(2M−1)>1. Contradiction. When M=1, all vertices lie in the sole facet and no nonface occurs; the same formula constructs a jointly measurable tuple. ∎

The outcome bound grows with the number of facets. Neither all-binary qubit realizability nor arbitrary infinite complexes follows from this proof. The construction concerns compatibility (existence of one joint POVM), not commutation or nondisturbance; every parent constructed for a face is an ordinary unconditioned quantum measurement.
