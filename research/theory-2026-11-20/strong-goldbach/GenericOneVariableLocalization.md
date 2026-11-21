# A generic single prime variable localizes the full binary Goldbach ring to its torus

In the full ring G=R/I and with the toric ideal J as in the one-prime catalyst theorem, there is a set T of odd primes of relative density one with the following **simultaneous** property. For EACH FIXED t∈T, inverting x_t alone makes ALL x_p units (for every odd prime p). Hence G[x_t⁻¹] is the full Laurent group algebra of the degree/weight group, and

    I:x_t^∞=J. 

The statement is about the full ring, not about paths staying under any prescribed finite cutoff. A single t may be chosen once and for all, independently of f∈J, but the exponent needed is allowed to depend on f. Distinguish the separate one-prime catalyst theorem: for each fixed f∈J, a density-one set of t kills f with exponent one. The order of quantifiers and the assertion that every variable is a UNIT are new here. In particular a fixed t with the present property is a non-zero-divisor in G if and only if I=J, the genuine full-fiber connectivity/domain question posed in [Nelson, Question 8.1](https://arxiv.org/html/2611.14580v2#S8). Neither injectivity of localization nor I=J is assumed or proved.

## 1. Forcing the finitely many starting primes to be units

Over any commutative ring, if a product is a unit so is each factor. In particular pair replacements starting on the unit side in G[x_t⁻¹] can generate further unit variables. For an arbitrarily specified fixed odd prime r and a moving odd prime t construct the following entirely genuine prime labels.

* If r is 0 or t modulo 3, find prime a,b,2t−a,2t−b and c=a+b−r. The relations with x_t² make x_a,x_b units. Their product equals x_r x_c, so x_r is a unit. In fact x_r divides x_t⁴ by explicit monomial pair moves.
* If r≡−t≠0 modulo 3, find primes a₁,…,a₄, all 2t−a_i, and c=a₁+a₂−3, d=a₃+a₄−3, e=c+d−r. Four pairs summing to 2t make all a_i variables units; the two sum identities introduce x₃,x_c,x_d as units, and the final identity gives x_r as a unit. This displays x_r as a monomial factor of x_t⁸ by actual moves.

Here t is the one common PRIME anchor in both or all four sum pairs; the averages are not over four independently changing targets. All needed variable labels form a fixed system of pairwise nonproportional affine linear parts: t; the a's and 2t−a's; the corresponding disjoint pair-sums; and in the second case their combined four-sum. Each nonshared form depends on some a_i. Take t∈[X,2X], a_i∈[X/4,X/3] so all varying labels are positive and comparable to X when r is fixed. At 2 choose all a_i odd. At 3 choose a_i=t: in the first case 2t−r≠0, and in the other c=d=2t≠0, e=4t−r≠0. At ℓ≥5, fixing ANY nonzero class t, the next a_i must avoid 0,2t. On completing the (a,b) pair avoid one value that kills c. In the four-anchor construction, on completing the first pair avoid 3−a₁; on completing the second pair avoid 3−a₃ and the one further value which kills e. At most four residues are forbidden. These conditions apply unchanged when ℓ divides r or any of the fixed constants.

Thus the normalized one-/two-copy W-class second-moment lemma in [§4 of the one-prime catalyst note](OnePrimeCatalyst.md#4-relative-density-one-not-just-positive-density) applies. For a relative-density-one set T_r of moving primes t, a successful tuple exists. If both residues require different schedules, apply the lemma separately in the two nonzero classes modulo 3. Given any finite set of r's we can intersect all T_r. This argument does not use any unproved assertion about a single fixed binary Goldbach target.

## 2. Finite seed and induction; sharp order of the number of copies

There is a finite P₀ such that for every odd prime p>P₀ there are odd primes a,b,c with
    p+a=b+c,     a≤2p/log²p,      p/3−2 ≤ b,c ≤2p/3+2.          (1)
In fact choose the primes a∈[p/log²p,2p/log²p]. There are ≫p/log³p by PNT. The corresponding distinct even m=p+a lie in the interior (5M/2,7M/2) for M=⌊p/3⌋, once p is sufficiently large. The classical balanced almost-all Goldbach asymptotic, [Bazzanella–Languasco eq. (2) with H=1](https://www.research.unipd.it/bitstream/11577/122136/4/B-L.pdf), leaves O(p/log⁵p) exceptional m, and each other m has genuine prime b,c∈(M,2M] after removing the O(√p log³p) proper-power weighted contribution. Choose one nonexceptional a. The simpler statement with b,c<p is already Nelson Lemma 6.4 (Kátai–Phong). No numerical onset P₀ is needed.

Take T as the finite intersection of T_r for odd r≤P₀ (discard t=3). For fixed t∈T, induct on p. All initial x_r are units. Relation x_p x_a=x_b x_c and b,c<p makes x_p a unit. This is a legitimate induction across the whole infinite prime list, not the intersection of infinitely many density-one statements. Localizing at x_t is therefore equivalent to inverting every variable. Nelson's integral group-completion theorem (Theorem 6.2, v1 and [v2](https://arxiv.org/html/2611.14580v2#S6.Thm2)) identifies the unit localization with the group algebra of rank-two degree and weight; equivalently, its kernel from R is J. The contraction from G[x_t⁻¹] is I:x_t^∞, giving the desired equality. If x_t is a non-zero-divisor, the localization is injective, hence I=J; conversely R/J is a domain. Over a field a Laurent polynomial ring over the degree-weight lattice is a domain, independent of the characteristic.

There is also an order-sharp actual-move bound for generating units. Let k_t(p) be the least positive k such that k copies of t can be carried by homogeneous binary moves to a k-list containing p. Section 1 gives k_t(r)≤8 for all seed r. Relation (1) implies k_t(p)≤k_t(b)+k_t(c) by performing the two paths independently and replacing b,c by p,a. The following bound is linear, not merely p^{1+o(1)}:
    (p−3)/(t−3) ≤ k_t(p) ≤ C_t p.
The lower bound is the minimal weight 3 for the remaining k−1 slots. For the upper, increase the finite seed threshold in advance if necessary (keeping its finite-intersection construction) to ensure b,c≤0.7p, and choose a constant D with D log(1/0.7)>2. Induct on k_t(p)≤C_t p exp(−D/log p), absorbing all fixed seed cases in C_t. Using 1/log b,1/log c ≥ 1/log p + log(1/0.7)/log²p and (1), the sum of the two inductive bounds is at most
    C_t p exp(−D/log p) (1+2/log²p) exp(−D log(1/0.7)/log²p)
    ≤ C_t p exp(−D/log p).
The move count itself is not what k_t counts: it is the number of initial identical prime labels.

## 3. Genuine remaining issue

The generic localization criterion can test a proposed non-zero-divisor argument: regularity of even one of these fixed variables would force complete fiber connectivity. In particular at an unrepresented large N≡0 mod6, the actual ternary fiber s=N+3 has both pure residue-sign sectors of triples and no label 3 to link them (as proved in the [giant-fiber note](CubicGiant.md)). This gives I≠J and therefore makes EVERY t∈T a zero divisor, even though the same single-variable localization remains the full torus. The theorem identifies that implication but does not rule it out. Nor does group completion, catalysis after multiplication, or existence of these units in the localization prove regularity back in G. No claim that regularity automatically handles the other residue classes of binary Goldbach is made.

[Exact local controls and literal short move paths](check_generic_one_variable.py) run with `python3 -O check_generic_one_variable.py`. This concerns localization of the relation ring, not saturation of the set of attainable binary weights.
