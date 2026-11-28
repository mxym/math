# Octary scalar representations for binary three-fold matroids with a long line

## 1. Statement and port interpretation

Let M be a matroid of rank at most three. A **binary three-fold representation** is a family of binary subspaces V_e such that the dimension of the sum of V_e for e in any set S is 3 r_M(S). We prove that M is representable over F₈ if it has rank at most two, or if its rank is three and some rank-two flat in its simplification contains at least five points. Equivalently, the rank-three hypothesis is that M has a restriction isomorphic to U_(2,5), not just five parallel copies. We obtain a scalar representation of the **same labelled matroid**, meaning every subset rank is preserved. We do not claim that one can turn every original three-fold representation into that scalar representation by a joint binary change of basis.

Loops have zero subspace and parallel nonloops have identical subspaces, so we may simplify and reinsert zero columns and duplicate representatives at the end. For rank one the assertion is immediate; at rank two there are at most (2⁶−1)/(2³−1)=9 distinct nonzero, pairwise disjoint three-dimensional subspaces in the full six-dimensional span. The simple rank-two matroid is uniform on at most nine points and is represented on the projective line over F₈. The empty matroid is included.

For a nonloop dealer element d, its port qualifies a coalition S not containing d exactly when r_M(S∪{d})=r_M(S). A scalar representation preserves this equality and its failure at every S. Choose a uniform linear functional on the F₈ ambient space and evaluate it at the dealer column and at all share columns. The dealer evaluation is uniform because its column is nonzero. A qualified S linearly determines it. An unqualified S is independent of it because appending the dealer column strictly increases rank by one, so its value remains uniform conditioned on all those evaluations. Thus every nonempty dealer port of M has a scalar F₈-linear ideal scheme (dummy parties may be omitted or assigned independent field noise, without changing the port). This applies to the 8-ideal subclass with such a binary three-fold matroid representation. It does not presume that general 8-ideal schemes have binary-linear representations.

## 2. The known partial-spread dichotomy in matrix coordinates

Let U be the six-dimensional span of the chosen long line L. Identify U=W⊕W, W=F₂³. Write [d] for the graph subspace (x,d x) with d a binary endomorphism of W, and [∞] for (0,y). Any three members of L can be ordered and normalized to [∞],[0],[I]: split using the first two disjoint members as axes; the third projects isomorphically onto both, and one basis change puts its graph at I. Every further member is [X] with X and X+I invertible. Two graph subspaces of distinct slopes are disjoint precisely when the difference of their slopes is invertible. All sums and differences below are in characteristic two, and matrix products act on columns rightmost first.

Choose five members with slopes ∞,0,I,X,Y. An invertible binary 3×3 matrix X with X+I invertible has irreducible characteristic polynomial of degree three (otherwise it has eigenvalue 0 or 1). Its centralizer in the binary matrix algebra is F₂[X]≅F₈, by cyclicity; identify W with the field and X with scalar multiplication by x. We use this elementary compatibility fact:

> If an invertible binary map T is not scalar in this field structure, at most two nonzero field scalars a have T+aI invertible. In this fact aI means multiplication by a on F₈, not a binary matrix entry.

In fact each map can be written uniquely as T(z)=A z+B z²+C z⁴. Uniqueness follows from the root bound for a nonzero polynomial of degree at most four; both spaces have binary dimension nine. A two-term map is singular because the nonzero multiplicative group has prime order seven, and a power with exponent difference 1, 2 or 3 permutes it. A single non-scalar term B z² or C z⁴ has ratios T(z)/z exhausting the seven nonzero scalars. For an invertible three-term map, the ratio equality at distinct nonzero z,w reduces to

    z²+z w+w² = B/C .

Choose w=vz with v≠0,1; the coefficient 1+v+v² is nonzero because the multiplicative group has no element of order three. Unique squaring roots give a solution with z≠0. This ratio class is the set of nonzero elements of an F₂-kernel of dimension two. There cannot be another two-dimensional ratio class, since distinct two-dimensional subspaces in dimension three intersect. The five different nonzero ratios consist of a class of three and four singletons. Exactly two nonzero a are therefore compatible in this case.

If X and Y commute, all five belong to the field spread (the nine one-dimensional F₈-subspaces of F₈²). Since there are already three distinct nonzero scalar slopes I,X,Y, the compatibility fact forces **every** binary three-space disjoint from those five, as well as all further L elements, to belong to that same field spread. The compatibility statement here and below allows coinciding with a member of L, as long as it is disjoint from all the other members.

If X and Y do not commute, the five are maximal as a partial spread. For a short self-contained proof, fix the field of X. There are exactly 48 invertible T with T+I invertible: the two irreducible binary cubics give two conjugacy classes of size (168/7)=24. Six of these T are nonidentity scalar multiplications. Each of the other 42 has exactly two nonzero compatible scalars, one of which is 1. For a prescribed second scalar x≠0,1 there are exactly seven such T. Indeed simultaneous Frobenius conjugation sends x to x², and T↦T+I sends the second scalar to x+1. These permutations are transitive on the six possibilities (Frobenius has the two trace classes of size three; adding 1 interchanges the classes). Thus the 42 divide evenly. Conjugation by the seven nonzero scalar multiplications acts freely on the seven T for fixed x. If a nonidentity scalar commuted with an off-field T, its centralizer would force T to be scalar. Hence these seven T form one orbit.

A new finite slope Z compatible with ∞,0,I,X,Y would be invertible. If Z were in the field, compatibility with Y would force Z=I or X by the two-compatible-scalars fact. Otherwise it is one of the seven conjugates of Y by multiplication by t. The case t=1 gives the old slope Y. For t≠1, write Y(z)=A z+B z²+C z⁴ with B,C≠0. Then Z(z)=A z+B t⁻¹ z²+C t⁻³ z⁴, and Y+Z is a two-term map with both coefficients nonzero, hence singular. This rules out every new slope. In particular any direction compatible with a noncommuting five-set is already one of its members. The same count shows two simultaneous similarity classes of the **ordered normalized pairs** (X,Y), one for each irreducible polynomial of X, although we do not need that count for the rank-three argument.

This spread dichotomy and the seven-way orbit are already in Shaw's 1997 treatment of five-plane partial spreads and double-fives in PG(5,2), §4.1. The proof above is supplied so that the rank-three extension argument needs no classification table. The new conclusion concerns arbitrary points outside the spread's line, not uniqueness or classification of full spreads.

## 3. Directions of points off the line

The full binary span has dimension nine. For any point P outside L, U+V_P has dimension nine and V_P meets U trivially. Choose a complementary three-space and write P as the graph subspace with block column (a,b,I), i.e. (a z,b z,z) for z in W after identifying the complement with W. Call (a,b) its affine coordinates.

For distinct off-line P,Q the six-space V_P+V_Q meets U in the three-space

    D(P,Q) = {((a_P+a_Q)z,(b_P+b_Q)z,0): z∈W}.

The dimension follows from projection onto the third coordinate, which is surjective, and pair rank two. For each point X₀ of L, the triple P,Q,X₀ has binary dimension six or nine. Hence D(P,Q) either equals V_(X₀) or meets it trivially: if the sum has dimension six then V_(X₀) is contained in it, and if the sum has dimension nine the intersection is zero. Thus D(P,Q) is a direction compatible with L in the sense above. The triple with X₀ is collinear exactly when the direction equals V_(X₀). For three distinct affine points P,Q,R, collinearity is equivalent to D(P,Q)=D(P,R), since V_P+V_Q is the direct sum of V_P and D(P,Q). Triples with two on L and one outside are independent. These tests, together with simplicity, determine all subset ranks in rank three.

If the off-line points lie on one matroid line (possibly only two points), the common direction is D(P,Q) for every outside pair. There are at most eight outside points on that line: their three-spaces and the common direction are nine or fewer disjoint three-spaces in a six-space. In the commuting case the direction is scalar, possibly unlabelled in L; in the noncommuting case it is an actual L element. Realize L by distinct labelled points of the scalar projective line (respecting the direction), and realize the outside points by distinct affine positions on one scalar line in that direction. This preserves all the tests. With just one outside point there is nothing to constrain in its choice.

Otherwise choose a noncollinear outside triple. Its three pair directions are distinct. By using one of its points as the complement, the first becomes the affine origin O. We can normalize the three directions for O,U₀,V₀ to 0,∞,I in the order OU₀,OV₀,U₀V₀. In the commuting case the three directions are in the scalar line, and we use a change in GL₂(F₈); in the noncommuting case they are all in the chosen five-set, and we use the binary two-axis normalization in §2. The latter five-set remains maximal, so the other two slopes in the new coordinates cannot commute. In either case an invertible change on the third coordinate sets U₀=(I,0). Then OV₀ has slope ∞ and U₀V₀ slope I, forcing V₀=(0,I). The three normalized points are

    O=(0,0), U₀=(I,0), V₀=(0,I).                                   (1)

## 4. Commuting case: scalar coordinates of every affine point

Every pair direction is a scalar one. A finite scalar direction d of (a,b) from the origin means b=d a and a invertible; the vertical direction has a=0 and b invertible. Given (1), if a=0, the direction to U₀ implies b is scalar. If b=0 and a≠0, the direction to V₀ implies a⁻¹ is scalar. If a=I there is nothing more to show since b=d a is then scalar. In all remaining cases both a and b are invertible. The direction to U₀ cannot be vertical unless a=I, so a+I is invertible and b=d'(a+I) for a scalar d'≠0. With b=d a this implies (d+d')a=d'; the scalars are distinct (otherwise d'=0). Thus a and b are both scalar. These arguments use only the direction equations for the three anchor points. Every affine point is represented by the same coordinate pair over F₈, and directions, lines and hence all ranks coincide.

## 5. Noncommuting case: the seven-point extension

The line now has exactly five members with slopes ∞,0,I,X,Y. Every direction of an affine pair must be one of these, by maximality. For a point (a,b) distinct from (1), a proposed finite direction d from an anchor (c,e) means b+e=d(a+c) with a+c invertible. A proposed vertical direction means a=c and b+e invertible. We show that, relative to (1), the only possible affine points and their triples of directions to O,U₀,V₀ are

    point                         (a,b)              directions
    U_s, s∈{X,Y}                  (0,s)              (∞,s,∞)
    V_s, s∈{X,Y}                  (s⁻¹,0)            (0,0,s)
    W_s, s∈{X,Y}                  (u_s,u_s+I)        (s,I,I), u_s=(s+I)⁻¹
    T                             (I,I)              (I,∞,0).

To verify exhaustiveness, first let the directions to O,U₀ be d,e. If d=∞, then a=0, so b∈{0,I,X,Y} from the direction to U₀. The old points exclude 0 and I, leaving U_s. If e=∞, then a=I and b,b+I must both be among {0,I,X,Y}. Here s+I is neither 0,I,s nor the other noncommuting slope, so only b=I gives a new point, T. If d=e is finite, then d a=d(a+I) forces d=e=0. The direction to V₀ is a⁻¹, which yields V_s. When the finite directions are different, neither can be zero except at an old point. Thus d,e are distinct members of {I,X,Y}; solve

    a=(d+e)⁻¹e,     b=d a,     (b+I)a⁻¹=I+d+e⁻¹d.                  (2)

Here a and a+I are invertible. For e=I the last direction is I, giving W_d. For d=I it is e⁻¹, not an allowed slope. For d,e noncommuting, the last expression cannot be 0,I,d,e: equality to 0 implies e⁻¹=I+d⁻¹ (commutation); equality to I implies e=I; equality to d implies e=d; and equality to e gives (e+I)d=(e+I)e, again e=d. It is never ∞ as a is invertible. This proves the table without search.

The only compatible pairs of extra affine points are the two points of the same letter U, V or W. They have directions ∞,0,I, respectively; the needed differences are invertible by X+Y invertible (and, for differences of inverses, by conjugate multiplication of that difference by invertible maps). For completeness the exclusions of all cross pairs follow as follows.

- From T to U_s, V_s, W_s, the slopes are s+I, s(s+I)⁻¹, and s⁻¹, respectively. Each is a field element of F₂[s] different from 0,I,s, and so cannot equal the other noncommuting slope.
- Between U_s and V_t the slope is s t. If s=t, its square value is not allowed; if distinct, equality to 0,I,s,t is impossible by invertibility, distinctness and noncommutation.
- Between U_s and W_t the slope is s t+s+t. For s=t this is s². For distinct s,t, equality to 0 would give s=t(t+I)⁻¹; equality to I would give (s+I)(t+I)=0; equality to s would give (s+I)t=0; equality to t would give s(t+I)=0. All are impossible. These pairs have invertible first difference, so are not vertical.
- Between V_s and W_t the first difference s⁻¹+u_t is nonzero (zero would imply s=t+I), while the second difference u_t+I is invertible. Thus slope ∞ or 0 is impossible. When s=t the slope is s². For distinct s,t a slope I, s or t would require u_t+I equal to that slope times s⁻¹+u_t. These equalities give, respectively, I=s⁻¹, (s+I)u_t=0, or t s⁻¹=0. All are impossible. If the first difference is singular but nonzero, no slope from L is possible either.

The compatibility graph is therefore three disjoint edges and one isolated vertex. An extension selects zero extra points, one extra point, or both ends of one edge; there are at most five affine points in this noncollinear case.

Now choose any two distinct field values x,y∈F₈∖{0,1} for the labels X,Y on the scalar line at infinity. Reuse (1) and the formulas in the seven-point table with scalar x,y in place of X,Y. The chosen extra points are distinct from the anchors (and from each other if two are present), their three anchor directions are exactly the stated ones, and whenever a pair is present its mutual direction is the required ∞,0, or I. All pair directions in the entire realization match the labelled five-set. This implies by the tests of §3 that every triple rank agrees with M. Since the matroid is simple and rank three, these triple ranks determine every subset rank. Reinserting loops and parallel elements completes the proof.

## 6. Scope

The long-line theorem is about rank three (or lower) and binary three-fold subspace representations. The delicate five-point case gives scalar representability of the matroid, **not** conjugacy of a nonextendible five-spread to a contained part of the scalar field spread. There is a finite size cutoff on what remains in rank three. Fix a point of a simple rank-three matroid in this class and quotient the 9-dimensional ambient span by its 3-space. Each rank-two flat through that point gives a 3-space in the 6-dimensional quotient, and any two such spaces are disjoint away from zero because the two distinct flats together have matroid rank three. By counting the 63 nonzero quotient vectors, there are at most nine such flats. If every flat has at most four points, the matroid has at most 1+9·3=28 points. Thus any remaining simple rank-three counterexample within the binary three-fold class is on at most 28 points.

The general existence question for non-F₈-linear 8-ideal access structures, including general nonlinear representations, is not decided.
