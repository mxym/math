# Smith comparison across the sixty-site triangle boundary

Fix **any** triangle in a hypothetical Conway graph, without a saturation, symmetry, or Seidel-rank assumption. Write D for its 36-site cubic wing adjacency, H for its exterior 60-site 8-regular adjacency, B for the exterior-by-wing incidence, and L for the three-by-36 physical-wing incidence. The latter records one root per wing site. The following restrictions on the *actual graph H* use only the small wing for their right-hand sides.

For every prime p other than 2,5,7, the p-primary invariant factors (including the equal free nullity) of H−I and D+2I coincide after ignoring unit diagonal entries. At p=7, H−I has precisely one additional torsion factor Z/7, and all other p-primary factors match. Thus in particular
    rank_F7(H−I) = 23 + rank_F7(D+2I),
    rank_Fp(H−I) = 24 + rank_Fp(D+2I)   for p∉{2,5,7}.
Here the shift 23 rather than 24 records precisely one constant direction. These identities do not assert existence of exterior completions.

**Proof.** The SRG block equations are
    HB=2J−B(I+D),    BᵗB=12I−D−D²+2J−LᵗL,    BBᵗ=12I−H−H²+2J.
Work over the p-adic integers for p≠2,5. By the primary summand for a residue a of an integral symmetric operator we mean the invariant direct summand whose characteristic polynomial reduces to a power of (x−a); complementary factors with distinct reductions split by Bézout/Hensel. The complementary summand of an operator shifted by −a is locally invertible, so contributes no nonunit Smith factors.

On the (−2)-primary wing summand LD=J₃L because every wing dart has exactly one wing-neighbor in each physical wing. The operator J₃ has only eigenvalues 0 and 3, neither −2 mod p for p≠2,5, even if these two are congruent at p=3. Thus this entire summand is killed by L and also by the coordinate sum. On it BᵗB equals 12I−D−D², invertible because its value at −2 is 10. Meanwhile H1=8·1. On the 1-primary far summand the coordinate sum vanishes if p≠7; if p=7, split the constant vector off first in the integral far lattice (its norm 60 is a unit), and take the 1-primary summand inside its orthogonal complement. On that summand BBᵗ is invertible by the same polynomial's value 10 at 1.

The first equation and its transpose now intertwine H−I with −(D+2I) via B and Bᵗ. The images lie in the indicated primary summands by the intertwining; at p=7 the image of B is centered there since every wing column has ten contacts. Each of BᵗB and BBᵗ is a unit on its own summand, so B and Bᵗ are isomorphisms between these integral primary lattices. In detail the inverse of B is (BᵗB)⁻¹ Bᵗ there. The removed constant line at seven contributes H−I=7. This proves all Smith and rank statements, with no assumption of diagonalizability after reduction.