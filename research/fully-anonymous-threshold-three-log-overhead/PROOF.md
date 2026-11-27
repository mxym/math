# Perfect fully anonymous 3-threshold sharing with logarithmic overhead

All logarithms are base two. The model is a single honest dealer and n participants. Conditioned on a fixed secret, every ordered pair of shares of distinct participants is independent uniform on the square of one common finite alphabet. This implies the same statement for singletons, perfect privacy, and the source's exact U-anonymity. Authorized participants have distinct identities but their share values may coincide. The decoder sees only the multiset of their shares, not identities. It recovers the secret from any three honest shares of one dealer, with no correctness error. Larger honest multisets can be decoded by selecting the first three occurrences under a public value ordering, keeping duplicates. No robustness to mixing dealers or faulty shares is claimed.

**Theorem.** For every n ≥ 4 and integer L ≥ 1, there is such a scheme with m = ceil(log n) and share length M = m ceil(L/m) + 10m ≤ L + 11m − 1, using deterministic polynomial public preprocessing, expected polynomial-time sharing from fair bits, and deterministic polynomial-time decoding. For n = 3, M = L suffices. If L = 0, the unique empty secret is shared with zero-bit shares.

## 1. Auxiliary construction for a pair of field elements

Fix q = 2^m ≥ 4. Start with q participants indexed by the elements of F = F_q. Let E = F_(q^5), let H = |E| = q^5, and let V = E^2 with |V| = Q = H^2 = q^10. The auxiliary secret set is F^2, of size q^2, and one auxiliary share is a point of V.

### 1.1 Exact tags

The group PGL(2,F) acts on E minus F by fractional linear transformations. For z in E minus F and an invertible F-matrix [[a,b],[c,d]], cz+d does not vanish, and the image is outside F (apply the inverse if necessary). Every z in E minus F has degree 5 over F. A purported stabilizer satisfies c z^2 + (d-a) z - b = 0, forcing c=b=0 and d=a, the identity in PGL. The action is free. Counting two independent columns and dividing by the q−1 possible common nonzero scales gives

    |PGL(2,F)| = (q^2−1)(q^2−q)/(q−1) = q(q^2−1).

There are exactly (q^5−q)/(q(q^2−1)) = q^2+1 disjoint orbits in E minus F. Assign a different orbit and representative z_s to each auxiliary secret s.

Also assign a different one-dimensional E-linear subspace D_s of V to each secret. For example, choose e in E minus F and, for s=(s_1,s_2), take the line spanned by (1,s_1+e s_2); the slopes are distinct. The full set of lines consists of the H spans of (1,u), u in E, plus the span of (0,1). Their nonzero parts partition V minus zero. Each line has H−1 nonzero points.

For t in F, set x_s(t)=t+z_s t^2. These are distinct: for a≠b the difference is

    x_s(a)−x_s(b) = (a−b)(1+z_s(a+b)) ≠ 0.

Indeed 1+z_s(a+b) could vanish only if z_s were in F, with a+b=0 making that factor instead equal to one.

### 1.2 Dealer

The dealer independently samples a uniform translation B in V. The following mixture determines a nonzero direction vector A in V and a parameter t_i in F for each participant i in F. Its share is

    Z_i = B + x_s(t_i) A.                                      (1)

- Matching branch, probability (q−1)/Q: choose a uniform nonzero h in F. The pairs {i,i+h} form a perfect matching in characteristic two, and t_i is the canonical smaller of i and i+h under any fixed ordering of F. Both ends of each edge use the same parameter and distinct edges use distinct parameters. Choose A uniformly nonzero on D_s.
- Nonmatching branch, probability (Q−q+1)/Q: set t_i=i for every participant. For each E-line D define the conditional selection weight

    w_D = H−1 − (q−2) 1_(D=D_s).                              (2)

  Choose line D proportionally to w_D, then choose A uniformly nonzero on D.

All w_D are positive: even the diminished weight is H−q+1>0. The weights sum to

    (H+1)(H−1)−(q−2) = Q−q+1,

so the unconditional probability of a given line being used in the nonmatching branch is w_D/Q. The branch with each particular matching shift h has probability exactly 1/Q. For any distinct indices i,j, the unique shift which pairs them is h=i+j, so conditional on matching the chance they are paired is 1/(q−1). (Using a uniform perfect matching would also give this probability; a single shift is sufficient.)

### 1.3 Exact pair law

Fix s and any i≠j. Write W=Z_j−Z_i. The matching shift h=i+j gives W=0, with unconditional probability 1/Q, and no other case gives zero because x_s is injective and A is nonzero. If they are in different matching edges, the difference x_s(t_j)−x_s(t_i) is nonzero in E; multiplying the uniformly random nonzero A on D_s by this difference leaves it uniform on the nonzero part of D_s. The total unconditional mass of this portion of matching is (q−2)/Q. In a nonmatching line D the same reasoning makes W uniform over D minus zero, with total unconditional mass w_D/Q. For any nonzero w in V on its unique E-line D we obtain the exact atom

    Pr[W=w] = ((q−2) 1_(D=D_s) + w_D)/(Q(H−1)) = 1/Q.        (3)

Conditional on the branch, shift, and A, the quantity W is fixed, and Z_i=B+x_s(t_i)A is uniform on V because B is independent uniform. Thus Z_i is uniform independent of W, not only marginally uniform. Equations (1)–(3) give, for every u,v in V (including u=v),

    Pr[(Z_i,Z_j)=(u,v)] = Pr[Z_i=u,W=v−u] = Q^(-2).           (4)

This argument is pointwise for every secret and every ordered pair.

### 1.4 Anonymous decoding

An honest triple with all three shares equal is impossible: x_s is injective and A nonzero, and no parameter is used more than twice. If exactly two values occur, this must be the matching branch. The nonzero difference lies on D_s and therefore determines the secret via the public line labels.

If the three values are distinct, their corresponding t_1,t_2,t_3 in F are distinct. The two differences Z_3−Z_1 and Z_2−Z_1 lie on the same E-line. A total decoder first checks E-collinearity (the 2-by-2 determinant of the two differences must vanish). For distinct shares passing this check, there is a unique ratio R in E with Z_3−Z_1=R(Z_2−Z_1); divide in either nonzero denominator coordinate. Formula (1) gives

    R = [(t_3−t_1)/(t_2−t_1)] *
        [1+z_s(t_3+t_1)]/[1+z_s(t_2+t_1)].                  (5)

This is an invertible F-Möbius transform of z_s. In fact, writing c_0=(t_3−t_1)/(t_2−t_1), a matrix in the format of 1.1 is [[c_0(t_3+t_1),c_0],[t_2+t_1,1]], of determinant c_0(t_3−t_2)≠0. Consequently R belongs to the tagged orbit of z_s. The argument applies to every ordering of the three input values. Explicitly, exchanges of entries act on R by R -> 1/R or R -> 1−R, which generate the six order changes and belong to PGL(2,F). One may sort first to define a deterministic multiset function even on invalid input. Unassigned or invalid tags can return a fixed default, which never happens on an honest triple.

We may run the scheme on all q participants and retain any n≤q of them. Every pair and triple of retained participants was already among those verified; a discarded participant may be a matching partner, with no change in the argument. This is an exact U-FASS for q^2 secrets on any n between 3 and q, with auxiliary share length log Q = 10m.

### 1.5 Explicit preprocessing and sampling

Fix public binary bases of F and E and the ordering on F. Deterministic finite-field construction is polynomial in q: for F, exhaustive monic degree-m polynomial search costs at most q candidates with polynomial-in-m irreducibility tests. For E, enumerate monic degree-five polynomials over F and check irreducibility by the Frobenius identity and excluding degree-one and degree-two factors. There are at most q^5 candidates and each test uses polynomially many bit operations in m. Enumerate PGL matrices by normalizing the first nonzero entry to one. Iterate over E minus F; whenever an element is not marked, choose it as an orbit representative and mark its orbit. Freeness ensures that the total number of mark operations is q^5−q. The lookup table and the subsequent line tags are deterministic and public, with size polynomial in q. No secret preprocessing or nonuniform table search over sharings is needed.

Sample B by 10m fair bits. The branch and h can be sampled jointly by a uniform 10m-bit integer, reserving q−1 outcomes for the q−1 nonzero shifts. To sample a nonmatching line exactly, draw a uniform integer in [0,Q−q] by fair-bit rejection and use the integral cumulative weights (2); the sum stated there gives the correct denominator. A scalar in E minus zero is sampled exactly by rejecting zero. Rejection samplers take bounded expected numbers of trials. The dealer's work to form all q shares and the decoder's field arithmetic and public lookups are polynomial in q. When q is the least power of two at least n, q<2n, so all costs are polynomial in n (and in L for the compiler below).

## 2. Direction-space compiler for an arbitrary L-bit secret

This is the threshold-three form of the common direction space of Ren–Yu (Theorem 1 and Algorithm 1), but uses one genuinely multi-symbol auxiliary invocation instead of encoding its message bit by bit.

For n≥4 let q be the least power of two at least n. Fix distinct public alpha_i in F. Put d=ceil(L/m) and encode the L-bit secret as S in F^d using fixed trailing zero padding. Draw independently A_0,A_1 uniform on F^d and define payloads

    Y_i = A_0 + alpha_i A_1 + alpha_i^2 S.

The dealer computes the canonical row-reduced nonzero basis b_1,...,b_r of U=span_F(A_1,S), with r≤min(2,d), and writes S=theta_1 b_1 + ... + theta_r b_r; the coefficients are the pivot coordinates of S. Pad the list of coefficients with field zeros to a fixed pair theta=(theta_1,theta_2) in F^2. This includes r=0, where theta=(0,0). Share theta once by §1, independently using fresh coins conditional on the payload masks and secret. Participant i receives (Y_i,Z_i).

For every fixed S and i≠j the linear map (A_0,A_1) -> (Y_i,Y_j), apart from a fixed translation, has invertible coefficient matrix [[1,alpha_i],[1,alpha_j]]. Thus the payload pair is uniform on (F^d)^2. Given S,A_0,A_1, both the payload and theta are fixed and the auxiliary pair is uniform on V^2, by (4) for every possible theta. Averaging over the masks proves the joint exact pointwise law of the complete shares, uniform on (F^d × V)^2. The auxiliary pair cannot leak theta's dependence on the masks.

Given the values for any three distinct participants i,j,k, the two payload differences from i span U. Their two-by-two coefficient matrix relative to the ordered generators A_1,S has rows (alpha_j−alpha_i,alpha_j^2−alpha_i^2) and (alpha_k−alpha_i,alpha_k^2−alpha_i^2), with determinant (alpha_j−alpha_i)(alpha_k−alpha_i)(alpha_k−alpha_j)≠0. This proves equality of spans even if the generators are dependent or zero. Consequently the decoder computes the same canonical basis without knowing i,j,k or their evaluation points. It recovers theta from the auxiliary triple, then forms S from this basis (ignores the padded zeros) and unpads. This gives perfect reconstruction regardless of the order of the three complete shares. Rank zero, rank one and rank two, as applicable for a given d, are all handled by the same decoder.

Length is M=md+10m. For all integer L≥1, md−L is between zero and m−1, so M≤L+11m−1, also for short L<m where d=1. For n=3 use the standard XOR sharing of the L-bit secret: draw two independent uniform L-bit strings and use their XOR with the secret as the third, recovering by XOR of all three. For L=0 all parties may hold the empty string; uniformity is on a singleton and the decoder returns the unique secret. This proves the theorem including the endpoints.

## 3. Comparison to the published alphabet lower bound

For 1<t<n, the Kishimoto–Okada–Kurosawa–Ogata bound for finite anonymous perfect threshold schemes implies |Omega| ≥ (|Sigma|−1)(n−t+1)+1. It applies already with ordinary perfect secrecy, which follows here from product uniformity. Ren–Yu §5.4 discusses applying it to the exact product-uniform model and to arbitrary finite laws. At t=3 and n≥4, fixed-width M-bit shares for L≥1 therefore satisfy

    M − L ≥ log((2^L−1)(n−2)+1) − L ≥ log(n−2) − 1.

This is an order comparison as n grows, uniform in L≥1. We do not assert a sharp leading factor or any bound at larger thresholds. The construction works at a single t and does not assert active security, robustness to mixed dealers or computational anonymity of an implementation.
