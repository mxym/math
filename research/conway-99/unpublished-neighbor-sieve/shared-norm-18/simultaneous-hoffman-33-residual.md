# The simultaneous Hoffman / 33-set rank-42 residual

Scope: the rank-42 two-type {N18,N24} face. Fix its actual unique Hoffman coclique C of size 22 and an actual G(3,33) field w=-1_T. The four surviving tuples have n=50,51,52,53 oriented N18 fields per signed seven-residue. Existence of a T in every tuple follows from the separate [G333 lower bounds](norm22-johnson-positive-mass.md), not from this lemma. Its overlap with C is Δ=5 or 12. The 33-set has two neighbors per inside vertex and six per outside vertex. This note is a conditional necessary graph structure, not a rank exclusion.

Let U be the even rank-44 graph lattice of determinant 49 on the terminal face, and u_i the graph site marks (u_i-u_j in U). Write d_i=3 e_i-Ae_i and u_i=(d_i+1/9)/√7. Here C and T without subscripts in an indicator denote actual literal vertex sets. Since A1_C=4−4 1_C and A1_T=6−4 1_T, put

    m_T=Σ_{i∈T}u_i=√7(1_T−1/3),
    m_C=(3/7)Σ_{i∈C}u_i=(3/√7)(1_C−2/9).

The first is in U (it has charge zero modulo 3 and trivial seven class). The second is in U: away from 7 use 3Σ_C u_i∈U; at 7 m_C belongs to U* by the true zero-seven-class coclique, and its integral norm 22 forces membership in U by the anisotropic discriminant plane. Also m_T/7=−w°/√7 ∈ U*: its actual charge is 3, permitted in U* at 3. The discriminant vector [m_T/7] is nonzero at seven by its norm 22/7. These memberships use the graph lattice dictionary, not an arbitrary free-variable theta control.

Set ℓ=3Δ−22 and P=Z m_T+Z m_C. Its Gram in this order is [[154,ℓ],[ℓ,22]], with determinant D=3339=3²·7·53 at Δ=5, or 3192=2³·3·7·19 at Δ=12. This P is primitive in U. Indeed, a p-divisible primitive combination a m_T+b m_C would require p²|D. For any site difference u_i−u_j the pairing with this combination is 7a(1_T(i)−1_T(j))+3b(1_C(i)−1_C(j)); every one of the four C/T cells is populated. At Δ=12, p=2 then forces a and b even. At Δ=5, p=3 forces 3|a, and b m_C/3 cannot have integral norm unless 3|b. This exhausts possible primes.

Let W=P^⊥∩U. The image of U under evaluating (m_T,m_C) lies in 7Z×Z; the site differences give (7,0),(0,3), while evaluating m_C gives (ℓ,22). Hence the image equals 7Z×Z. Evaluation on P has determinant D, so [U:P⊕W]=D/7, and det W=49(D/7)²/D=D. Thus W has rank 42, determinant 3339 or 3192. There is NO gluing index at seven; the two discriminant lines at seven have the same square class since U's anisotropic binary discriminant form has square determinant. At every other prime the discriminants of W and P are anti-isometric by primitivity and unimodularity of U there. In particular W* generally has extra non-seven-primary classes. More precisely U*∩W_R consists exactly of vectors of W* with trivial prime-to-seven discriminant component. Indeed away from seven orthogonality forces the P component zero and the maximal-graph gluing requires the W component trivial; at seven U=P⊕W locally. Consequently (U*∩W_R)/W is cyclic of order seven. An actual vector of U or U* lying in W_R itself must have folded charge zero: orthogonality to m_C requires integral δ=22a/9 and |a|≤4. It also has both literal totals on C,T equal to zero. No such charge restriction applies to arbitrary projected vectors of W*.

For every true oriented N18 signed-unit field t, write x=t/√7∈U* and η=t·w. Then (x,m_C)=0 by the Hoffman orthogonality, (x,m_T)=−η. Its orthogonal projection x' onto W_R actually belongs to W*, with squared norm

    ||x'||² = 18/7 − 22η²/D.

All 8n oriented fields give different x', including signs. If two project together, write the raw difference t−v = k(1_T−1/3)+j(1_C−2/9). The four nonempty C/T cells imply k,j integers, and |k|≤4 since both fields are signed units. Testing on C gives 3ℓk+154j=0. Hence 22|k at Δ5 and 11|k at Δ12. Both force k=j=0. In particular no projection vanishes.

Precisely 2n of these projected fields are unshifted vectors x=x', with norm 18/7. Indeed η≡0 (mod7) iff [t] lies on the perpendicular of [w] in the anisotropic binary plane. This line contains precisely two of the eight signed classes of norm 18 mod7 (since [w] has squared norm 33−11≡1, the other diagonal is a square as well). Every such class has mass n by the exact [unaveraged residue-balance theorem](two-type-residue-balance.md). For an N18, 0≤ numbers of positive/negative sites in T ≤9, so |η|≤9. The only other multiples ±7 would give an impossible charge ±3 field of raw norm 18+33−14=37. Therefore η=0 exactly on these two classes. Conversely all vectors of U*∩W_R of norm18/7 have folded charge zero as noted and are these true fields. The assertion is ONLY for this seven-primary part of W*; the rest of W* is not asserted to have that mass or minimum.

The determinant, saturation, image and projection-injectivity calculations are independent of modular-form coefficient searching.

[The full dual gap](two-mark-dual-gap.md) characterizes every short vector through squared norm 23/10 by an actual 33-set switch, and gives two exact root counts for rank-six mirror gluings.
