# Proof

## 1. Model and statement

For public n ≥ 1 and q ≥ 2, sender i has a bit x_i. All senders share a sample R uniform on a finite set, independent of x; an external referee does not know R. Each sends one deterministic message of (x_i,R), and the referee sees the ordered tuple. Perfect correctness means each input and seed decodes to the function value. Perfect privacy means equality of the entire ordered transcript laws for any inputs of the same function value. Support privacy weakens equality of laws to equality of supports. Communication is the maximum over x,R of total bit length. Public parameter descriptions and the pre-shared seed are not sent in the transcript.

**Theorem 1.** Put m=min(q,n+1). For all integers n ≥ 2 and q ≥ 2, the minimum worst-case total communication for MOD(q,n)(x) = 1[q divides Σ_i x_i] is Θ(n log₂ min(q,n+1)), with absolute constants, for perfect privacy and for support privacy. At n=1 the exact optimum is one bit. In particular, a perfectly private protocol costs (4n−4)⌈log₂ P⌉ bits for any prime P ≡ 1 (mod m). Its projective version costs at most (n−2)⌈log₂(P(P²−1))⌉ + 2⌈log₂(P+1)⌉ bits.

In the notation MOD(q,n), q is the tested integer modulus, not the field characteristic. The communication order is established by an upper bound plus an external lower bound; no exact optimum is claimed for general n≥2.

## 2. A private contraction lemma

Let F be a finite field of cardinality P, d≥2, G=GL_d(F), n≥2. Fix a nonzero row u, nonzero column v, and for each sender i a public map T_i from its input alphabet into G. Write T_i=T_i(x_i) and h(x)=u T_1 ··· T_n v. The Boolean function 1[h(x)=0] admits a perfect PSM with (2d+(n−2)d²)⌈log₂ P⌉ bits.

The shared seed consists of independent uniform G_1,...,G_{n−1} in G and s in F*. The ordered messages are

- m_1 = u T_1 G_1 (one row);
- m_i = G_{i−1}^{−1} T_i G_i for 2≤i≤n−1 (one matrix each);
- m_n = G_{n−1}^{−1} T_n v s (one column).

Each message is computed before seeing any other. The referee multiplies in order, obtaining h(x)s by cancellation, and outputs 1 exactly if the scalar is zero. Each endpoint uses d fixed-length field symbols and each middle message uses d². At n=2 there are no middle matrices, and all empty matrix products below are identity.

**Distribution of the middle and change of coordinates.** For fixed x, the map (G_1,...,G_{n−1}) ↦ (G_1,m_2,...,m_{n−1}) is a bijection of G^{n−1}: for each 2≤i≤n−1 recover G_i=T_i^{−1}G_{i−1}m_i. Thus the middle messages are independent uniform matrices, independent of G_1 and s. Let B=m_2···m_{n−1}. Conditional on those messages, the invertible, public transcript transform (m_1,m_n) ↦ (m_1,Bm_n) gives the pair

    (a G_1, G_1^{−1} b),  a=u T_1,  b=T_2···T_n v s.              (1)

Both vectors are nonzero; their contraction is hs.

**Orbits and exact fibres.** For every t∈F, let O_t be the set of pairs (r,c) with r a nonzero row, c a nonzero column, and rc=t. The action (r,c) ↦ (rA,A^{−1}c) of A∈G is transitive on O_t. If t≠0, choose basis first column c and d−1 basis vectors of ker r as the other columns. In that basis the pair is ((t,0,...,0),e_1). If t=0, choose first column c, second column w with rw=1, and fill the remaining columns so that c together with the remaining columns forms a basis of ker r. The pair is then ((0,1,0,...,0),e_1). This also proves nonemptiness at d=2. For either case, the preimages of a pair are all a stabilizer coset of equal size under the map from uniform G_1, so (1) is uniform on O_{hs} for fixed s and middle messages. Counting the nonzero row and then the affine solutions for the column gives

    |O_0| = (P^d−1)(P^{d−1}−1);
    |O_t| = (P^d−1) P^{d−1} for each t≠0.                          (2)

If h=0 (output 1), (1) is uniformly distributed on O_0. If h≠0 (output 0), hs is uniformly distributed on F*, and (1) is a uniform mixture of the equally sized nonzero-contraction orbits, equivalently uniform on their union. In both cases the pair law is independent of the middle messages and depends on x only through the output. More explicitly, for a fixed x and a target transcript in the appropriate support, after fixing the middle matrices, the number of seed preimages is (P−1)|G|/|O_0| for output 1, and |G|/|O_t| for output 0 with t any nonzero contraction. The recursion fixes all other G_i once G_1 is chosen. At d=2 those counts simplify to P(P−1) and P−1, respectively. This counts the entire transcript, not only the scalar.

An explicit simulator samples all middle matrices independently uniformly. It sets t=0 if the output is 1 or samples uniform t from F* otherwise. It samples r uniformly nonzero, then c uniformly subject to rc=t and c≠0 (the latter automatic if t≠0). It returns r, the middle matrices, and B^{−1}c. For example, one may choose a nonzero coordinate of r and solve that coordinate of c after picking the other coordinates uniformly, rejecting c=0 if necessary. This is exactly the proved law.

## 3. Specialize to integer modulus

The equivalence q|w iff m|w holds for every w∈{0,...,n}, with m=min(q,n+1): if q>n both tests accept only zero. By Linnik's theorem the least prime P≡1 (mod m) is at most C m^L for absolute C,L, and the cyclic group F_P* contains an element g of exact order m. Make P,g public. Take d=2, u=(1,−1), v=(1,1)^T, and T_i=diag(g^{x_i},1). Then

    h(x) = g^{Σ_i x_i} − 1,

which is zero exactly when q divides the ordinary integer weight. The contraction lemma in §2 gives the claimed (4n−4)⌈log₂ P⌉ bits and perfect privacy. If n=1, sending the local answer 1−x_1 suffices; zero bits cannot compute this nonconstant function. At n=2 the displayed direct formula applies with just the row and column; no special convention for q=2 is required.

**Shorter projective alphabet.** Replace the row and column by their one-dimensional subspaces, and replace each matrix by its class modulo nonzero scalar multiples. These are separate deterministic postprocessings of the original messages. Products of any representatives give the same zero test. Hence correctness and full-tuple privacy carry over, and the scalar s can be omitted because it has no effect on the projected message. The image of a uniform GL_2 element is uniform on PGL_2, because the quotient fibres all have size P−1. The number of row lines and column lines is P+1 each, and the number of projective matrix classes is (P²−1)(P²−P)/(P−1)=P(P²−1), giving the stated bit bound by public fixed-length codes. Geometrically, in dimension two the row line specifies its kernel point on the projective line. The test is equality of that point and the transported column point. PGL_2 is transitive on pairs of distinct points (choose column representatives as a basis), and on equal pairs. This is the small-group specialization of permutation branching-program garbling underlying the compression.

**Parameter generation and randomness.** Linnik supplies size, not a poly(log m) time algorithm for finding P. These values can be fixed as public parameters. If uniform compilation as a function of the n-bit input length is desired, after taking m≤n+1, scan primes in the progression using even trial division until P is found, and scan units and powers up to m to find g. The numeric search bound is polynomial in m, hence in n (plus reading the binary q, if q is supplied). It need not be polynomial in log m alone. Dense projective alphabet codes can be built by enumerating and ordering their representatives in polynomial time in P. Uncompressed width-two online encoders and decoding use only elementary field arithmetic once parameters and seed are given. The finite uniform shared seed is part of the PSM model. Exact generation from fair coins by rejection is possible in expected finite time; no fixed number of fair bits for an exactly uniform sample is asserted.

**Lower bound and parameter edges.** For 2≤q≤n, Ball et al. Theorem 2 / Corollary 16 gives Ω(n log q) for support privacy, hence also perfect privacy. The constants in the lower bound can be taken independent of q,n; the reduction uses NOR on fewer than q live bits (formal citation in SOURCES.md). For q>n the function is NOR_n, the complement of OR_n, so their Theorem 1 / Corollary 15 gives Ω(n log n). Complementing the decoder does not change correctness or privacy classes, and log(n+1)=Θ(log n) for n≥2. Finite small cases can be absorbed uniformly into the constants; in particular each party must send distinct messages on its two local bits for every seed, since with all other bits zero the output changes. At a fixed seed we may simultaneously choose the longer of each party's two messages and hence obtain at least n bits even under variable-length coding. All displayed upper bounds are perfect-private, so they also upper-bound support-private cost. The prime-modulus additive construction and the OR/NOR upper bound of the original sources often have better constants; the new comparison is for composite 2≤q≤n.

## 4. Weighted and sparse residue corollaries

For public integer weights a_i and public residue r modulo q, choose P≡1 (mod q), g of exact order q, T_i=diag(g^{a_i x_i},1), u=(1,−g^r), v=(1,1)^T. The same theorem checks Σ_i a_i x_i≡r (mod q), with O(n log q) bits (the unweighted q>n truncation is not needed or claimed here). The lemma also applies if each sender directly holds a residue and defines its local exponent from it.

More generally, let S be a public nonempty proper subset of Z/qZ, and let k=min(|S|,q−|S|). Let A denote S or its complement, whichever has k elements. With g,P as above, define H(z)=∏_{r∈A}(z−g^r). Write H(z)=Σ_{j=1}^d h_j z^{e_j} with distinct exponents and nonzero h_j. Since H is monic with nonzero constant and k≥1, 2≤d≤k+1. Use u=(h_j)_j, v=(1)_j, and T_i=diag(g^{e_j a_i x_i})_j, which are invertible regardless of the bits. The contraction is H(g^{Σ_i a_i x_i}), zero exactly on A. If A is the complement of S, flip the certified output. This is a perfectly private O(n(k+1)^2 log q) bound; more generally the number of nonzero monomials of a chosen polynomial zero test sets the width. Constant S=∅ or all residues costs no bits. At n=1 every such predicate is computed by its sender. No matching lower bound for these extra predicates is asserted.
