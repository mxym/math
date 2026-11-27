# Equality CDS: exact and small-error shared randomness

## 1. Model

Let X=Y be a fixed finite label set of size N≥2, and let the secret alphabet have size M≥2. Alice knows x and s; Bob knows y and does not know s. They share a finite random variable R independent of x,y,s, hidden from the referee. Its positive probabilities are π_r, r∈[q]. Alice and Bob may use arbitrary private randomness, independent of one another and of R. There is no extra free, common random resource. They send one message each, in finite alphabets; the referee knows (x,y). Write their conditional channels as P^x_{s,r}(a) and Q^y_r(b). The entire transcript at fixed inputs and secret has law

    T_s^{x,y}(a,b) = ∑_r π_r P^x_{s,r}(a)Q^y_r(b).                   (1)

Correctness means a decoder Rec_{x,x} recovers s with probability at least 1−ε for every x,s. For every x≠y, privacy means a distribution Sim_{x,y}, not depending on s, such that ‖T_s^{x,y}−Sim_{x,y}‖_1≤δ for all s. The norm here is ℓ1, not TV; TV is half ℓ1. Both requirements match Hasegawa–Mataraarachchi Definition 2.4 when M=2. For M>2 we use the same conditions for each symbol. We count log₂ q (the log-support cost) or fixed fair shared bits. With k fixed fair bits, q≤2^k for any deterministic conversion to R; private coins cannot increase the common support. Shannon entropy H(R) is a separate quantity, not identified with log₂ q unless R is uniform. Perfect means ε=δ=0.

## 2. Exact converse, all labels and secret alphabets

**Theorem 1.** For any perfectly private, perfectly correct equality CDS in this model,

    q ≥ 1+N(M−1)                       and                       H(R) ≥ 2 log₂ M.    (2)

The support bound also holds with perfect privacy and ε<1/M. In particular for a bit secret it holds for every ε<1/2. Both bounds allow arbitrary nonuniform R and private channels. They do not require linear encoders.

### 2.1 Support by a direct sum of secret-difference spaces

For any x, choose y≠x. Perfect privacy at (x,y) implies equality of Alice's marginal message laws for every secret, by summing (1) over b. The marginal depends only on x and s, not y. Fix a message a_x with positive mass p_x in this common marginal. The choice does not depend on the secret: the *same* a_x has mass p_x>0 for all of them. Number the secrets 0,...,M−1 and put

    w_{x,s}(r) = π_r P^x_{s,r}(a_x),
    L_x = span{w_{x,s}−w_{x,0}: 1≤s≤M−1} ⊆ R^q.

Let Q_y map a vector w∈R^q to the vector over Bob's message alphabet with entries ∑_r Q^y_r(b)w(r). Since all w_{x,s} have mass p_x, L_x lies in the coordinate-sum-zero hyperplane. Perfect privacy and (1) imply Q_y L_x=0 whenever y≠x. For y=x, the nonnegative vectors Q_x w_{x,s} have the same positive mass p_x and disjoint supports: a common positive b would give the same authorized transcript (a_x,b) for different secrets, which perfect correctness forbids. They are therefore linearly independent. Accordingly dim L_x=M−1 and Q_x is injective on L_x.

If vectors v_x∈L_x satisfy ∑_x v_x=0, applying Q_y leaves Q_y v_y=0 and hence v_y=0 for each y. Thus the sum is direct and lies in a space of dimension q−1. This proves the first inequality in (2).

For the stated extension, allow ε<1/M. For each x separately, condition the authorized decoding error on A=a; the law of A is still independent of s. Summing the conditional errors over s and averaging over this common law gives a value at most Mε<1. Choose an a_x of positive mass with its sum of errors less than 1. From each normalized vector Q_x w_{x,s}/p_x apply the authorized decoder for this a_x. The resulting M×M row-stochastic matrix of output laws, one row per s, has trace exceeding M−1. It is nonsingular: eigenvalues of a row-stochastic matrix have modulus at most 1 (its operator infinity norm is 1), so a zero eigenvalue would force real trace at most M−1. Linear independence before applying the decoder follows. The same direct sum proof is valid. If a decoder has an erasure output, it may be deterministically mapped to a secret value first, which cannot increase error.

### 2.2 A distinct Shannon constraint

Take a uniform secret S and two distinct labels x,y. On a common probability space draw R and S independently, and conditionally use independent private coins to sample A_x,A_y,B_x,B_y with their prescribed local channels (only the A variables use S). This is a proof coupling, not a second use of the protocol. Its (A_u,B_v) marginal for fixed S is exactly (1) for every u,v used below.

Perfect privacy gives S independent of (A_x,B_y). Perfect decoding from (A_x,B_x) also gives zero conditional entropy after adjoining B_y. Consequently

    log₂ M = I(S;B_x | A_x,B_y)
           ≤ I(S;R | A_x,B_y)
           ≤ H(R|B_y).

The first inequality is conditional data processing because B_x is independent of (S,A_x,B_y) given R. The second uses nonnegativity of conditional entropy and conditioning reduces entropy. Independently, A_y alone hides S by off-diagonal privacy, while (A_y,B_y) decodes it. Thus

    log₂ M = I(S;B_y | A_y)
           ≤ I(S,R;B_y | A_y)
           = I(R;B_y | A_y)
           ≤ I(R;B_y).

The equality uses B_y independent of (S,A_y) given R. The final inequality follows from I(A_y;B_y|R)=0 and the mutual information chain rule. Adding H(R|B_y) and I(R;B_y) gives the second inequality in (2). This is a Shannon-entropy lower bound independent of the support argument. With perfect privacy but error ε≤1−1/M, the same inequalities with log₂ M replaced by log₂ M−h₂(ε)−εlog₂(M−1) follow by Fano's inequality on the two authorized pairs; we use only the perfect case below.

## 3. Exact fixed fair bits on binary domains

**Theorem 2.** For X=Y={0,1}^n with n≥1 and S={0,1}^ℓ with ℓ≥1, the minimum number of fixed fair shared bits for perfect correctness and privacy is ℓ+max(n,ℓ). The upper sends ℓ bits from each party, and each alphabet of any perfectly correct and private protocol needs at least 2^ℓ symbols.

If k fixed fair bits suffice, then by (2),

    2^k ≥ 1+2^n(2^ℓ−1) > 2^{n+ℓ−1},    and    k ≥ H(R) ≥ 2ℓ.

Since k is integral, k≥max(n+ℓ,2ℓ). For the alphabet statement, on a diagonal pair the secret is independent of either message alone, by off-diagonal privacy for Alice and because Bob has no secret. Hence log₂ M≤H(A_x|B_x) and log₂ M≤H(B_x|A_x) by perfect decoding. Each message alphabet must have at least M symbols. This is a cardinality statement, not a converse for variable-length coding.

For achievability put d=max(n,ℓ). Fix a binary basis of the field F of cardinality 2^d, a public injection x↦ξ_x into F, and a surjective binary-linear map Π:F→{0,1}^ℓ. Share independent uniform U∈F and V∈{0,1}^ℓ (d+ℓ fair bits). Define a label mask C_x=V⊕Π(Uξ_x). Send A=s⊕C_x and B=C_y. If x=y, A⊕B=s for every seed. If x≠y, Π(U(ξ_x−ξ_y)) is uniform because multiplication by the nonzero field element ξ_x−ξ_y is bijective and Π is surjective. Moreover C_y is uniform and independent of U because of V, thus independent of C_x⊕C_y. So (C_x,C_y) is uniform on the product of the two mask alphabets; the unauthorized full transcript is uniform independently of s. This is the classical pairwise-independent field mask with an ℓ-bit projection, as in Gertner–Ishai–Kushilevitz–Malkin §3.2, except that only the used ℓ bits of the offset are sampled. See SOURCES.md for the prior communication optimum. Fields and label embeddings may be public parameters; the finite protocol itself uses only the stated fair bits, and no communication of the seed.

For `ℓ≥n`, (2) also gives the exact minimum shared Shannon entropy and log-support cost, both 2ℓ, and the construction attains them. In general when ℓ<n this note gives the lower bound (2) on support/entropy and the exact optimum for fixed fair bits; it does not identify the optimum nonuniform Shannon entropy or the optimum non-power-of-two support. If N=1, there are no off-diagonal privacy constraints and sending S directly requires no shared seed; this edge is outside (2). A one-symbol secret is vacuous.

## 4. A robust support bound for a one-bit secret

**Theorem 3.** For all N≥2, 0≤ε≤1/2 and 0≤δ≤1 in this one-bit equality-CDS model,

    q ≥ (1−2ε)^2 N / (1+(N−1)δ).                                  (3)

No bound on private randomness or message length is imposed. This theorem gives a quantitative lower bound when δ becomes small. It does not replace Hasegawa–Mataraarachchi's deterministic-SMP-based lower bound for constant error.

For fixed x,y let D(x,y)=TV(T_0^{x,y},T_1^{x,y}). By the decoder event and the triangle inequality, D(x,x)≥1−2ε and D(x,y)≤δ when x≠y. For a binary secret, the last inequality is also sufficient for δ-privacy in the ℓ1 convention by using the midpoint of the two laws as simulator.

Define z_a^x(r)=P^x_{0,r}(a)−P^x_{1,r}(a). For every r, ∑_a |z_a^x(r)|≤2. Let

    φ_x(p) = (1/2)∑_a |⟨p,z_a^x⟩|,    p a probability vector on [q].

Then 0≤φ_x≤1. If b is distributed according to Bob's message under y, the posterior p_y(r)=Pr[R=r|B=b,y] has law μ_y. For b of zero marginal probability take any posterior, which never enters the expectation. Factoring each term in (1) by the marginal probability of b shows exactly

    D(x,y) = E_{p∼μ_y} φ_x(p).                                      (4)

In particular (4) is a statement about the full transcript, not just Bob's marginal. It uses that Bob's encoder does not know the secret.

In the proof only, draw p_x∼μ_x independently for every label. For each x choose a bounded supporting vector

    v_x = (1/2)∑_a sign(⟨p_x,z_a^x⟩) z_a^x,

taking sign(0)=0. Each coordinate of v_x has absolute value ≤1. We have ⟨v_x,p_x⟩=φ_x(p_x); for any p independently of how v_x was chosen, |⟨v_x,p⟩|≤φ_x(p) by the triangle inequality. Form the real N×N matrix W with W_{xy}=⟨v_x,p_y⟩. For every outcome, rank(W)≤q by this factorization. Its expected trace is at least N(1−2ε) by (4). Moreover W_{xx}²≤1, and when x≠y,

    E W_{xy}² ≤ E φ_x(p_y)² ≤ E φ_x(p_y)=D(x,y)≤δ.

For any real square matrix, |Tr W|≤‖W‖_*≤√rank(W) ‖W‖_F; the first inequality follows immediately by singular-value decomposition. Thus Cauchy–Schwarz on the random choice and summing the entries of the Frobenius norm yield

    N²(1−2ε)² ≤ (E Tr W)² ≤ q E ‖W‖_F²
                               ≤ q (N+N(N−1)δ).

Dividing gives (3). The proof never conditions on a referee decoding action, requires no joint actual runs across labels, and does not count the proof sampling as a protocol resource.

## 5. Matching order across privacy errors

**Corollary.** Fix any γ₀∈(0,1]. For n≥1, ℓ=1 and errors ε,δ≥0 satisfying 1−2ε−δ≥γ₀, the optimal log-support cost, and separately the optimal number of fixed fair shared bits, have order

    Θ_{γ₀}( min{ n, log₂(n+1)+log₂(1/δ) } ),                        (5)

with the convention log₂(1/0)=+∞. The exact fair-coin result at ε=δ=0 is Theorem 2, not the order statement alone.

For the lower bound let N=2^n. For δ>0, (3) and 1+(N−1)δ≤2max{1,Nδ} imply

    log₂ q ≥ min{n,log₂(1/δ)}−1+2log₂ γ₀.

At δ=0 this holds by the evident limit. Theorem 3.6 of Hasegawa–Mataraarachchi gives log₂ q=Ω_{γ₀}(log₂(n+1)) because equality on n-bit inputs has deterministic SMP complexity Θ(n), from its distinct rows and columns. That theorem allows arbitrary ε,δ with the indicated uniform gap, as its quantitative bound shows. For small parameters q≥2: if q=1, Bob is independent of Alice's message at each fixed (x,y,s), and D(x,y) cannot vary with y for fixed x, contradicting the gap. This absorbs additive constants. The maximum of log₂(n+1) and min{n,log₂(1/δ)} is at least half of min{n,log₂(n+1)+log₂(1/δ)}. A finite fair shared tape costs at least log₂ q.

For the upper bound at δ=0 take the exact construction of §3. For δ>0, independently sample K uniform n-bit row vectors in a public list, where K is the least power of two at least 2(n+2)ln(2)/δ². For each fixed nonzero w, the signs (−1)^{⟨g_i,w⟩} are unbiased independent signs under the list selection; Hoeffding and a union bound over 2^n−1 choices show that with positive probability their empirical mean has absolute value at most δ for every w. Fix such a list as a public parameter, not as protocol randomness. One use of the protocol shares a uniform list index J and a fair bit U. Let C_x=U⊕⟨g_J,x⟩, and send A=s⊕C_x, B=C_y. On equal labels the referee always reconstructs s. For unequal labels, the two individual bits are uniform because of U and their parity has absolute bias ≤δ. An elementary two-bit calculation gives ℓ1 distance exactly the absolute parity bias to the uniform two-bit law, supplying the required simulator. This is at most 1+ceil(log₂(2(n+2)ln(2)/δ²)) fair shared bits. Take the cheaper of this and n+1 bits from the exact protocol. This proves (5) and is a nonuniform public-list existence argument; it does not claim a new explicit small-bias construction. The same upper bound also follows up to constants from standard CDS randomness sparsification of the classical two-message scheme.

This order characterization concerns the specified equality model at positive gap, with no assertion for selection functions other than equality, the robust-inner-product question, two-sided secret holders, or quantum communication.
