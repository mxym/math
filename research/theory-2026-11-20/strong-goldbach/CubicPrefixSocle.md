# A missed large multiple of six forces a cubic in the full socle of an actual prime prefix

Fix a field k. For each integer s let A_s be the **complete** set of odd primes ≤s, R_s the polynomial ring on x_p, p∈A_s, and G_s=R_s/I_s where I_s includes **every** equal-pair binomial on A_s, even at pair weights exceeding s. Put m_s=(x_p:p∈A_s). For all sufficiently large odd s divisible by three, let M_1,M_2 be cubic monomials from the two central components of the ternary prime hypergraph of total s, one in each nonzero residue sign modulo three. These components are guaranteed by [CubicGiant.md](CubicGiant.md); all but O_D(s/log^D s) prime labels in [s/8,5s/8] lie in them, for every fixed D. Their monomial classes need not be distinct in G_s. Unconditionally, already in this finite prefix,

    m_s (M_1−M_2) = 0.

In particular if s−3 is not a sum of two odd primes then f=M_1−M_2 is a **nonzero** homogeneous cubic in the socle. Its annihilator is exactly the homogeneous maximal ideal, depth at that ideal is zero, and in particular G_s is nonreduced since f²=0. This is necessary, not a proof of positive depth, or Goldbach; we do not claim the converse. Positive depth for all sufficiently large complete prefixes with these cutoffs would suffice for the sufficiently large multiples of six. Nelson's [Corollary 6.8](https://arxiv.org/html/2611.14580v2) gives an **upper**, not lower, depth bound. The cutoff here is on individual prime labels, not on the relation weights.

## Explicit paths for every variable, uniformly
For t=3 use [the three-move quartic chart](SquareZeroBridge.md). For precision, take all free coordinates in intervals of radius .001s about (a,b,p,b')=(.450,.275,.225,.275)s; the moving labels c=s−a−b, q=3+a−p, u=b+p−b', d=b'+c−3 are within .005s of (.275,.225,.225,.550)s for large s. Every moving label is therefore positive and ≤s, endpoint labels lie centrally. The fixed 3 also belongs to the prefix.

Now let t be any odd prime 3<t≤s. Use four equal-pair moves

    (t,a,b,c) → (u,v,b,c) → (3,h,v,c) → (w,z,h,v) → (t,r,h,z),
    c=s−a−b,   v=t+a−u,   h=u+b−3,   z=3+c−w,   r=a−u+w.

Coincident entries cause no difficulty: an equal-pair identity is still valid (a trivial move may be skipped). There are nine moving forms in the four coordinates (a,b,u,w). Impose a,b,u≡1 and w≡2 modulo three, so a,b,c are sign 1, r,h,z sign 2, and v≡t is nonzero. At 2 take all four odd. At any prime ℓ≥5 choose a≠0, then b outside {0,s−a}, u outside {0,t+a,3−b}, and w outside {0,3+c,u−a}. All nine labels are nonzero; this includes the prime divisors of t and every special residue of s.

Independently restrict the four input coordinates to radius .001s about the indicated centers. The following table gives centers in units s, except that the exact moving v center retains t/s and the exact centers for h,z include shifts −3,+3 respectively.

    t/s      a     b     u     w     c    v           h     z     r
    ≤.75    .40   .28   .20   .16   .32  t/s+.20    .48   .16   .36
    >.75    .32   .16   .42   .26   .52  t/s−.10    .58   .26   .16

Input errors are ≤.001, and output errors about these *displayed* centers are respectively .002,.002,.002+3/s,.003+3/s,.003. Thus for s≥3000 all moving labels are in [.15s,.96s]; for example v∈[.198s,.952s] in the first band, v∈[.648s,.902s] in the second. The six endpoint labels a,b,c and r,h,z all lie in [s/8,5s/8]. Together with 3 and t this accounts for every variable in all five states.

Apply [Tao–Teräväinen, Theorem 1.6](https://doi.org/10.4171/JEMS/1404) to the nine affine forms on this positive-volume box after fixed substitutions imposing the mod-3 residues. Their linear parts, listed by free coordinate unit vectors A,B,U,W, are

    A, B, U, W, −A−B, A−U, U+B, −A−B−W, A−U+W.

They are pairwise nonproportional and fixed; the intercepts are O(s), uniformly in t. The box and these bounds give a uniform o(s⁴) error. At large ℓ pairwise linear independence mod ℓ gives a uniform normalized local factor 1+O(1/ℓ²); the finite remaining primes have a uniformly positive product by the explicit choices above (at 3 the prescribed residue class makes every output a unit). Hence the weighted count is ≫s⁴ uniformly for every t in EITHER band. Removing proper prime powers costs O(s^(7/2)log^9 s) by fixing one label. Prescribing any endpoint a,b,c,r,h,z to lie in the central bad-label set costs O_D(s⁴log^(9−D) s), since fixing one affine form leaves O(s³) tuples. Take D>10. For all sufficiently large s, for EACH t a chart remains whose endpoint triples are in the respective central giants. This uses one common threshold independent of t, not a union bound or an exchange of density and universal quantifiers. A path within either central component uses only prime labels ≤s; chaining with this chart identifies x_tM_1 and x_tM_2 inside G_s.

If s−3 has no binary representation, no prime triple of s contains 3. Each has three equal nonzero signs modulo 3; a shared-label move cannot change the sign. Thus the two endpoint classes are distinct even in the complete degree-three fiber. The quotient by pair differences has the connected components as a k-basis, so f is nonzero in all characteristics, including two. Since m_s kills it, its annihilator is proper and contains a maximal ideal, proving the depth and socle assertions. This proves the theorem without estimating the depth of any other actual prefix.

[Exact local checks and sample prime paths](check_prefix_socle.py) run under `python3 -O check_prefix_socle.py`. They exercise the two cutoff regimes and the move identities; they do not establish a positive depth bound.
