# A near-smooth six-label fixed-seed orbit must contain a subpower nonseed

Fix an odd prime p and a finite set F of primes. Let N tend to infinity through even integers prime to p, with log(N/N_F)=o(log N), where N_F is the full F-part. Suppose six distinct odd prime units modulo N, written x_0=p,x_1,…,x_5, constitute a strongly connected factor-closed all-composite component: the whole prime factorization of each N−x_i uses these labels, and i→j means x_j divides N−x_i. Then

    min_{1≤j≤5} log(x_j)/log N → 0.

In particular the five moving labels cannot all be ≥N^δ infinitely often for any fixed δ>0. There is **no** bound on the powers of p in the complements and no fixed-power-class condition on N/N_F. The same conclusion holds for a forward orbit from p of exactly six labels with all complements composite, by the nonterminal alternative of [the six-label fork](PrimeOrbitSixLabelFork.md), which already gives subpower nonseeds. We do not exclude six-label components with fewer polynomial-size nonseeds, bound the size of the forward orbit in general, prove a representation of N, or establish binary Goldbach. The threshold is not made effective.

## 1. Two independent scales force a vertical component

Suppose to the contrary that all five labels exceed or equal N^δ along a countersequence. Use [the coefficient pencil theorem](PrimeOrbitCoefficientPencils.md) and its prerequisites. After fixing the five bounded nonseed columns A′ and passing to a subsequence, write B′=E−A′ for E the last five columns of I_6. The actual seed-exponent column a and the signed zero-fiber translates λ are on one of the pencils:

    t=p^m,   m→+∞,   a_i=a_i⁰+s_i m,   λ_i=λ_i⁰ t^(n_i),   s=B′n,

where n has five nonseed coordinates, a_0=s_0=0, λ_0=λ_0⁰=p, and n_0=0 by convention when attached to an input. The λ_i⁰ are nonzero signed rational p-powers. The integers s_i are nonnegative and at least two are positive; call the latter inputs hot, the remaining nonseed inputs cold. The weaker [seed-mass theorem](PrimeOrbitSixSubpowerSeedMass.md) proved max a_i=o(log N); hence log t=o(log N). Every cold a_i⁰ is a nonnegative integer, but a hot intercept need not be nonnegative. Also A′w=1 with every 0<w_j<1, so each projected row contains at least two nonseed factors, counted with multiplicity. All rows are loopless.

Take the Zariski closure of the actual sequence
     
    (t,T,X_1,…,X_5)=(p^m,N,x_1,…,x_5)
     
in A¹_t × (G_m)^6 over Qbar, retaining the units T,X_j but **not inverting t**. Choose an irreducible component and a dense infinite subsequence therein. Its projection to (t,T) is dominant: for any nonzero polynomial in T with polynomial coefficients in t, its highest nonzero T coefficient grows as a nonzero constant times its leading t-power as t→+∞. All coefficient magnitudes are exp(o(log N)), and that highest coefficient is bounded below by a positive constant for large t. Thus the polynomial cannot vanish at these physical points. The selected irreducible closure Y has dimension at least two. The exact physical equations extend as regular identities on Y:
     
    T−X_i=p^(a_i⁰) t^(s_i) ∏_{j>0} X_j^(A′_ij),    X_0=p.

Choose one embedding Qbar→C_p. The points (N,x_1,…,x_5) are p-adic units eventually: N is prime to p and the moving primes are distinct from p. By compactness a subsequence converges in (Z_p^×)^6 while t tends to zero p-adically. Its limit y is in Y(C_p) at t=0 with all six coordinates units, because all defining Laurent-polynomial identities pass to the limit. This is a point on the closure of the actual sequence: no extrapolation of extraneous torus solutions at t=0 is involved. Y remains irreducible after the algebraically closed base extension; t is neither identically zero nor a unit in its affine coordinate ring. Every irreducible component of its nonempty fiber at zero has dimension dim Y−1≥1 (principal ideal theorem and dimension formula for affine varieties). Choose a component D of that fiber containing y after base extension; the geometric components are defined over Qbar since the fiber was and Qbar is algebraically closed.

On D, hot labels equal T. The remaining equations are precisely the cold system
     
    T−p=T^(u_0) ∏ X_j^(b_0j),       T−X_i=p^(a_i⁰) T^(u_i) ∏ X_j^(b_ij),
     
with j ranging over at most three cold labels and u_i the total multiplicity of hot factors. The algebraic impossibility lemma in [the seed-mass proof](PrimeOrbitSixSubpowerSeedMass.md), section “Eliminate two or more rows of positive seed mass”, excludes any torus solution of this **specific** system over Q(T)^alg if T is transcendental: it uses only the cold coefficients, full row arities and actual strong connectivity. A dominant T on D would give a nonempty torus variety over Q(T)^alg by taking the generic fiber and an algebraic closed-field point, so T=τ is constant. It is a nonzero algebraic number, a p-adic unit in the chosen embedding from y, and τ≠p by the nonzero seed-row product. Any other coordinate constant along D is likewise a p-adic unit. Some cold coordinate varies, since T, t and the hot coordinates are constant and D has positive dimension.

All subsequent function-field arguments can be made on an algebraic curve on which these same cold coordinates vary: choose a smooth algebraic point of D where each of its finitely many nonconstant coordinate differentials is nonzero (characteristic zero), a tangent direction in none of their kernels, and generic linear sections through the point transverse to D with that tangent line. The resulting local curve is smooth there and each chosen coordinate remains nonconstant; use the normalization of the projective closure of that curve component. For dim D=1 just use D. The curve need not pass through the p-adic limit: all coordinates already constant on D retain the established values and p-adic unit property.

## 2. Classify the varying cold coordinates on the vertical curve

Let U be the set of varying cold coordinates. There are at most three. Every other coordinate, including the hot labels τ, takes a nonzero constant value. The loopless row of a varying coordinate must use another varying coordinate, or it would itself be constant. Thus |U|=1 is impossible.

At any pole of a varying input X on the normalized projective curve, τ−X has a pole, so its product row must use another pole input; there are no self-loops. At least two coordinates have poles there. No zero of a varying coordinate can coexist with a pole: otherwise there are exactly two poles and one zero, as at most three coordinates vary. The zero input cannot use itself and cannot use either pole, since its complement has order zero there, no other zero is available for compensation, and every constant is nonzero. Its row would contain only constants, contrary to variation. It follows, by taking a zero of each nonconstant coordinate in turn (which exists on a complete curve), that **no constant input row with nonzero complement product can use any varying coordinate**: all inputs are regular at that zero, while the product would vanish. This applies to the seed and any constant cold row, whose complements are the displayed nonzero products; it need not apply to any hot row whose specialized complement is zero.

Suppose first all cold labels vary, necessarily two or three. Then the seed row uses only hot labels, so τ−p=τ^u with u≥2. At every complex embedding |τ|>1: |τ|≤1 would give p=|τ−τ^u|≤2. At any pole all the varying labels are poles. For two labels this follows above. For three, if only two were poles, the remaining coordinate would have a finite nonzero value (no coexisting zero); its row could use neither pole, since its complement is regular and has no vanishing factor to offset a pole, nor itself. This would make it constant. At a common pole select the labels of least positive pole order. The row of each has precisely **one** variable factor, of multiplicity one and of the same least pole order: add the positive orders on the right and use the equality of pole orders on the two sides. These unique successors form a directed cycle among least-order labels. Each such row is τ−X_i=C_i X_j with C_i=p^(a_i⁰) τ^(u_i); its true arity at least two gives a_i⁰+u_i≥1. Thus |C_i|>1 in any complex embedding. But multiplying the leading-coefficient equalities at the pole around the cycle gives ∏(−C_i)=1, a contradiction.

The **only remaining case** has two varying cold labels X,Y, one constant cold label Z (value z_0≠0), and precisely two hot indices H_1,H_2. The seed and Z rows use neither X nor Y, by their nonzero constant products above; the Z row cannot use itself. The two moving rows specialize to
     
    τ−X=C_X Y^a,       τ−Y=C_Y X^b,
     
with fixed nonzero C_X,C_Y and a,b≥1. Substitution gives a polynomial in the nonconstant function X of degree ab when ab>1, impossible. Thus a=b=1. The resulting affine linear identities force C_X C_Y=1 and τ(1−C_X)=0, hence C_X=C_Y=1. Each C is a product of a nonnegative power of p and powers of the p-adic units τ,z_0. Consequently the actual X and Y rows have **no seed factor**; their only variable-pair factors are one copy of each other. There is no need to eliminate the constants τ,z_0 separately by a scalar absolute-value argument.

## 3. The residue equations rule out this last class

Let v be the distinct nonzero primitive null indices of B′, with v_0=0, and let C be a two-by-six rational matrix whose row space is the full left eigenspace of the actual A at 1 (equivalently the left kernel of B′). Denote its six two-dimensional column vectors by g_i, including g_0. All are nonzero and no three are proportional. Indeed the index j of the largest prime has a unique parent i, so g_j=A_ij g_i with A_ij>0. The [ramified seed theorem](PrimeOrbitRamifiedSeedList.md), section “The projective line and its nonconstant product”, proves this pair is nonzero (the four-by-four trace/Perron argument). Every nonzero left eigenspace row has at least four supported coordinates: its positive and negative supports each contain a directed cycle of length at least two. A further zero column would give a vector killing the known pair and that third index. Likewise three proportional columns would leave just three possible nonzero coordinates in a nonzero left row annihilating them. In particular the six columns must include at least one **positively proportional pair**.

The two directions n and v obey the seed and Z-row homogeneous constraints, since s_seed=s_Z=0. For either d=n or v one has
     
    d_Z=A′_ZH · d_H,      (A′_0H + A′_0Z A′_ZH) · d_H=0,
     
where H denotes the ordered two hot columns and d_0=0. The displayed nonnegative two-vector is not zero: the seed has a nonseed factor, and the Z row if needed has at least one nonseed factor, necessarily hot as it uses neither X,Y nor itself. The vector v_H is nonzero, so n_H is a rational multiple of v_H. Subtracting this multiple of v from n gives n′ with n′_H=n′_Z=0 and the same s=B′n′. The X,Y cold row identities now give n′_X=n′_Y=h; here h≠0 because s≠0. Hence
     
    s_i=−h(A′_iX+A′_iY)>0              (i=H_1,H_2).
     
In particular each hot row uses at least one of X,Y.

The X,Y column equations of C A=C, added together, give
     
    (A′_H1,X+A′_H1,Y) g_H1 + (A′_H2,X+A′_H2,Y) g_H2=0.
     
The seed and Z rows use neither, and the one-copy mutual terms g_X,g_Y cancel. Both displayed coefficients are strictly positive, so the two hot columns are oppositely proportional. Choose a nonzero left row c that kills this class. It is supported on all four remaining coordinates. The same individual column equations give c_X=c_Y. As each sign occurs at least twice, c_0,c_Z both have the opposite sign to c_X,c_Y.

Finally use the exact characteristic-zero residue divisibilities from [the étale fiber](PrimeOrbitSlowCurveEtaleFiber.md). For every root z of the physical irreducible residue polynomial and for the two rows of C,
     
    Σ_i g_i (λ_i⁰)^−1 t^(−n_i) z^(−v_i)=0                  (vector equality).
     
Write n′=n−αv as above and z′=t^α z. Choose the positive root t^α at each physical positive t=p^m. All t^α lie in one fixed number field (take a fixed denominator-th root of p); this gauge change neither changes the six distinct index exponents nor bounds the a priori moving fields by decree. It rewrites the equality as
     
    F(z′)+t^(−h) G(z′)=0,
    F(U)=Σ_{i∈{0,Z,H_1,H_2}} g_i (λ_i⁰)^−1 U^(−v_i),
    G(U)=Σ_{i∈{X,Y}} g_i (λ_i⁰)^−1 U^(−v_i).
     
These two-vector Laurent polynomials have fixed rational coefficients. Thus det(F,G) must be the **zero Laurent polynomial**: otherwise each z′ lies among a fixed finite set of its nonzero algebraic roots, and consequently the splitting fields of all the physical polynomials are contained in one fixed number field after also adjoining the fixed root of p. This contradicts the degree-at-least-two, escaping-residue-fields conclusion of the étale-fiber theorem.

Expand the determinant into eight terms, indexed by one outside and one inside index. The smallest sum v_i+v_j occurs uniquely at the respective minima in the two sets; similarly the largest at the two maxima. Distinctness of all six indices is essential. The nonzero fixed factors (λ_i⁰ λ_j⁰)^−1 cannot cancel these unique extreme coefficients; their vanishing implies the outside-minimum column is proportional to the inside-minimum column, and likewise for the maxima. Neither outside extreme can be hot since the two hot columns already form a whole size-two proportionality class, and the inside labels are distinct from them. Thus 0 and Z pair, in some order, with X and Y in two further proportionality classes. Applying c above shows each of these pairs is **oppositely**, not positively, proportional. All six Gale columns are now exhausted by three opposite pairs. This contradicts the positively proportional largest-prime/parent pair and finishes the proof.

This is a structural argument about actual prime-factor orbits; no finite chart census or arity bound is used. For the underlying exponent-digraph framework see [Bożek](https://arxiv.org/abs/1909.09900).

[Kelanemer’s 2026 preprint](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) uses a related irreducible exponent-matrix framework. Its public abstract advertises broader conclusions, but the full argument was not available for this comparison; no priority or comprehensive nonoverlap claim is made here.
