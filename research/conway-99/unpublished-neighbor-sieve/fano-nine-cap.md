# A cap and a duplicate exclude the nine-edge original Fano mask

Assume Seidel rank 36 and an original Fano root r with P,N its two signed seven-site shores and Z the 15 sites missing both. Choose p∈P. Let Yp be its ten external contact neighbors, whose four *caps* have distinct negative labels adjacent to p, and whose six other sites occur in three duplicate pairs, with labels in N₀={n∈N:n≁p}. Use the simple cubic graph Q on Yp whose 15 edges are the 15 sites z (each touching two members of Yp). The [32-mask theorem](fano-six-contact-determinant.md) leaves exactly one mask with nine Q-edges among the six doubles. It already proves that in every surviving original case, the 29+10 site marks together with r span the entire nondegenerate 36-dimensional mod-seven ambient space. No assumption is made about graph automorphisms.

**Theorem.** The nine-edge mask is impossible at every signed vertex. Only 4,5,6 edges remain, with at most 12,18,1 labeled masks respectively before any additional constraints.

**Proof.** Under the nine-edge alternative the six doubles are a cubic Q-component, since their graph is the full prism. The four caps are another cubic component, necessarily K₄. Let Zc be the six edges of this K₄, and C the set of four caps. In the ordinary mark space consider

    η = −2u_p + 2 Σ_{q∈P\{p}}u_q + 2 Σ_{n∈N₀}u_n + Σ_{z∈Zc}u_z − 2 Σ_{v∈C}u_v − 2r.

The site coefficients a_i in this expression sum to 14. Hence η·u_i = 3a_i−Σ_{j∼i}a_j−2f_i mod 7. For the successive classes p, P\{p}, N\N₀, N₀, Zc, Z\Zc, C, and the six doubles, the integer neighborhood sums are respectively −8,4,2,8,−4,0,1,0. Here any q≠p on the positive shore shares exactly two negative neighbors with p, and the external cap sites each see three K₄-edge points of Z. The eight evaluations therefore vanish modulo seven. Further η·r=10−6−4=0 using the two sign shores and r²=2. The 40 vectors just checked span the ambient space, so η=0 there.

Take one cap and one double. They are nonadjacent in the actual graph: in N(p) the cap is paired to its negative label, not to a double. Inside the 39-site core they have exactly one common neighbor, p: their negative labels differ, their Z-triples lie in opposite Q-components, and the cap has no neighbor in Yp. Their other common neighbor x must be an exterior contact site outside Yp. Its positive label q is different from p; write I=1 if its negative label belongs to N₀, and zero otherwise, j=|N(x)∩Zc|, and t=|N(x)∩C|. Pairing η with u_x gives

    2 + 2I + j − 2t = 0 (mod 7).

As x is nonadjacent to p, their two common neighbors are already the chosen cap and double. Thus x meets precisely these two sites of Yp (so t=1), and does not meet any of the four negative neighbors of p (so I=1). The congruence says j≡5 mod7, whereas 0≤j≤3 since each contact site sees exactly three Z. Contradiction.
