# Perfect XOR: shorter distributed preprocessing and an entropy converse

All logarithms are to base 2 unless explicitly written ln. For a distribution on at most countably many points, entropy means discrete Shannon entropy, with the usual extended nonnegative convention. All vector spaces in the protocol sections are over F₂ unless otherwise specified.

## 1. Model and statements

There are n≥2 input parties P₁,…,Pₙ with authenticated private point-to-point channels, each holding one input bit. They all receive the correct XOR. There is no extra participant, dealer trusted by assumption, pre-shared secret, or public random string. A coalition is fixed before execution and follows the protocol. Perfect t-privacy means that for every C with |C|≤t, two inputs agreeing on C and on XOR give identical probability distributions of the entire joint view of C. A view contains input, private randomness known to that party, all sent and received messages with their endpoints and timing, and output. Synchronous rounds can carry a distinguished empty symbol and padding after local termination. Random tapes in the Shannon part are mutually independent and independent of the input. The splicing proof below may be read with finite tapes and finitely many rounds; it also applies to countably supported tapes and finite execution on every positive-probability tuple. If tapes have infinite Shannon entropy its bound is immediate.

**Theorem A (fair-coin upper bounds).** For 1≤t<n, there is a perfectly private protocol with at most

    t(5t+⌈log n⌉+3)

fair private bits in every execution. Its public description has polynomial length, and parties run in polynomial time given that description; the description is obtained by existence, not a deterministic polynomial-time algorithm. There is also a deterministic polynomial-time constructible protocol using at most

    t min(n−1, t⌈log n⌉)

fair private bits. With zero privacy requirement there is a deterministic protocol. For n=2 and t=1 the upper bound is not an optimum claim: XOR and own input determine the other input, so zero randomness is enough. The older 1-private one-bit protocol for n≥3 is not a new consequence here.

**Theorem B (private-tape entropy).** For n≥3, 1≤t<n and s=min(t,n−2), any perfectly private XOR protocol in the above model satisfies

    H(R₁,…,Rₙ) ≥ L_s := Σ_{k=1}^s max{1, (log(k+1)−1)/2}
                        ≥ (1/3) log((s+1)!).

It is also true that some input has expected total fair tosses at least L_s in the model of adaptively reading fair independent bits and terminating almost surely. This does not assert an Ω(t²) Shannon converse.

**Theorem C (one-bit encoding).** A one-bit encoding is a pair of distributions P,Q on words, with disjoint supports (zero-error deterministic decoding), identical marginals on every set of at most k coordinates, and a single arbitrary-distribution tape R independent of the encoded bit, from which the encoder selects one of those distributions by a deterministic map. Let message length m be unrestricted. For k≥1 the infimal entropy H(R) has order Θ(log(k+1)). It is already attained to this order over binary words with m=2k⁴ and finite rational distributions. The encoder is a stand-alone object, not a protocol implementing XOR.

## 2. The common sequential protocol and its exact privacy criterion

Use D=t and call P₁,…,P_D the dealers (we also consider the D=t+1 variant). These are ordinary input parties subject to corruption. Dealer d uses independent uniform seed bits to produce a vector a^(d) of n−1 cut masks by a fixed public linear map A_d. Set a₀^(d)=aₙ^(d)=0. In a preprocessing communication round dealer d privately sends a_(i−1)^(d)+a_i^(d) to each P_i other than itself and retains its self-value when i=d. P_i adds those contributions into r_i. Then, in index order, P_i receives Y_(i−1) (Y₀=0), computes and sends Y_i=Y_(i−1)+x_i+r_i to the next player if i<n. Finally Pₙ sends Yₙ to all others. For every seed and input,

    Y_j = Σ_{i≤j} x_i + Σ_{d=1}^D a_j^(d).

The mask at the final cut n is zero, proving correctness. The public output can be implemented by n−1 identical private sends; there is no trusted public channel with hidden extra information.

Fix C, |C|≤t. Write H={1,…,D} minus C, k=|C minus {1,…,D}|, h=|H|≥k (h≥k+1 in the variant). The interior cut coordinates seen by C are

    J = {i−1,i : i∈C} ∩ {1,…,n−1}.

Let V=F₂^J. Write B:V→F₂^C for the adjacent-difference map, extending cut vectors at 0 and n by zero. Rows only use coordinates of J. Let M_d be the restriction of A_d to J. When we condition on the corrupt dealer seeds and on **all separate setup contributions B M_d u_d for each honest dealer d**, the remaining honest seeds are uniform independently on the product of their nonempty linear fibers. (The setup does not depend on x.) The aggregate honest mask is consequently uniform on a translate of

    W := Σ_{d∈H} M_d ker(B M_d)  ≤  ker B.

This follows because the linear map from the product of the kernels to its image W has equally sized fibers (each is a translate of its own kernel). All conditioning values with positive probability are covered; zero-probability values do not appear in either view.

The orthogonal complement of W is the intersection over d∈H of the sets

    { w∈V : M_dᵀw ∈ im((B M_d)ᵀ) }
      = { w∈V : M_dᵀ(w+Bᵀλ_d)=0 for some λ_d∈F₂^C }.

This follows from (ker T)^⊥=im Tᵀ and orthogonality to a sum. That intersection contains row(B)=im Bᵀ. Thus W=ker B if it contains no w outside row(B). For privacy this equality is sufficient, since under inputs x,x' agreeing on C and with the same XOR, the difference of plain prefix parities has value zero at 0 and n and gives a vector v∈ker B on J (adjacent difference at i is x_i+x'_i=0 for i∈C). Adding v leaves each conditional uniform coset law unchanged. Given fixed corrupt seeds and separate setup contributions, the joint view is obtained from the observed chain cut values, corrupt inputs and final XOR, with the setup sends by corrupt dealers deterministic from their seeds; the remaining local computations are deterministic functions of these data. Hence exact equality of the conditional laws proves exact equality of the entire views. A perfect polynomial-time simulator can fill the honest inputs with any fixed tuple consistent with the specified XOR and the corrupt inputs, run this very protocol locally with fresh private seeds, and output the full view of C. Such a tuple exists since |C|<n. In particular the simulation includes each corrupt dealer's full seed and all its outgoing messages, not merely its contribution to the aggregate mask. In the all-dealers-corrupt case for D=t, C is exactly the first t parties. Their entire preprocessing is deterministic from their known tapes; their chain messages Y₁,…,Y_t are functions of their inputs and these tapes, and any received final broadcast is the specified XOR. Equivalently B is invertible on J={1,…,t} by anchoring a₀=0, and W=ker B=0 even though H is empty.

## 3. Nonexplicit short matrices

For the main construction take D=t, p=t, and r=4t+⌈log n⌉+3. Each dealer map A_d consists of p identity rows supported on the first p private seed bits, and n−1−p suffix rows on an independent r-bit seed block. In choosing a protocol description, choose the suffix matrices of different dealers independently, every entry a fair bit. These bits are used for a mathematical existence proof; after choosing good matrices, they are public deterministic constants. No execution samples the matrices. In every execution each dealer uses p+r fresh fair private bits only; all subsequent operations are deterministic.

For fixed C and w∈V outside row(B), consider whether criterion (Section 2) can fail at a single honest d. Any witness w+Bᵀλ_d annihilated by M_dᵀ must have **all prefix coordinates zero**, because the prefix identity rows occupy independent seed slots, disjoint from the suffix slots. This condition is exact and independent of all chosen suffix rows. Every row of B indexed by a corrupt dealer lies fully in the prefix (its cut ends are i−1,i with i≤D, and endpoint n is excluded). It follows that, even though λ_d can vary arbitrarily by d, the family of suffix residual vectors from candidates w+Bᵀλ_d with prefix zero has cardinality at most 2^k: its suffix projection depends only on the k coefficients for corrupt outsiders. Every admissible residual is nonzero, since w∉row(B). For each fixed nonzero suffix residual the probability of annihilation in r independent columns of that dealer is 2^(−r). The resulting per-dealer bad-event probability is at most 2^(k−r). If k=0, J has no suffix cuts. When h>0, any honest dealer gives the full desired variation; when h=0, the all-dealers-corrupt case of Section 2 gives it. Thus k=0 has no bad event.

Different dealers in H have independent public matrix choices in the probabilistic method. The probability of a bad intersection for fixed C,w is at most 2^(−h(r−k)) even if the λ_d differ. For each k from 1 through t there are at most 2^D n^k coalitions: at most 2^D choices of corrupt dealers, and at most n^k outside choices. Each has its J deterministically, with |J|≤2t, and at most 2^(2t) choices of w. With L=⌈log n⌉ and h≥k, r−k≥3t+L+3. Hence the union bound is at most

    Σ_{k=1}^t 2^(3t) n^k 2^{−k(3t+L+3)}
      ≤ 2^(3t) Σ_{k=1}^t 2^{−k(3t+3)} < 1.

The first term of the latter geometric series is 1/8 and its ratio is at most 1/64 because t≥1. This includes coalitions of sizes below t, all feasible dealer splits, and k=t (then h=D=t). The k=0 and empty suffix cases were accounted for without any failure event. Hence a single fixed family meets the exact criterion for all coalitions. By Section 2 it works for all inputs and feasible setup values simultaneously. The matrix description is public of polynomial size in n and cannot leak input or tape bits; its existential construction is not counted in runtime fair coins. No communication step after sampling p+r bits per dealer flips another coin. If t grows at least as fast as a positive constant times log n, O(t²+t log n)=O(t²). Goyal–Ishai–Song's existing fair-coin Ω(t²) bound applies for n≥3 and t≤n−2; for t=n−1 apply it at t−1. Thus this gives unrestricted Θ(t²) on that parameter regime, including sublinear t. It does not give a matching unrestricted bound for growing t=o(log n).

**Optional t+1-source variant.** Take D=t+1 and p=min(t+1,n−1), with the same r. Now h≥k+1 for all coalitions; the previous per-dealer argument and the count 2^(3t+1) n^k give a failure bound at most 2^(−L−2) Σ_{k=0}^t 2^{−k(3t+3)}<1. This version never has zero honest dealers but uses a slightly larger coin budget. The t-source placement of the main construction already occurs in Kushilevitz–Mansour; the novelty is the total fair-coin bound, not a source-count lower bound.

### Restricted sequential-template converse

Keep the same setup and chain, with D=t prefix dealers, but now permit arbitrary independent finite or countable tapes and arbitrary deterministically generated cut masks for each dealer. Let t≥2, N=n−D, and M=⌊N/2⌋. For M≥2 the total private seed entropy required in this template is at least

    (D/2) log M.

Fix any two dealers H, and fix a positive-probability joint tape value of all other dealers. For two cuts i<j from the list D+1,D+3,…,n−1, take C to contain the D−2 other dealers and P_i,P_j. (The list contains exactly M cuts.) There is an honest player at an index strictly between i and j and another Pₙ strictly after j, outside C. Flip both those inputs. All coalition inputs and final XOR stay fixed; the plain-prefix parity of the two selected cut values changes by 1. The corrupt dealers' tapes are in the view, so conditional privacy still holds at their fixed value. In this conditional distribution the parity of the two aggregate masks must be uniform. Contributions of fixed dealers are constants, so this is the same as uniformity of the parity of the two H-generated masks. The distribution of the tapes of H is unchanged by conditioning on other dealers' independent tapes.

Let f_i be (−1) raised to the H-generated aggregate mask at cut i. These M functions have norm one and are pairwise orthogonal in L² of the two private tapes. For any positive-probability atom u with probability p_u, its normalized indicator has squared norm one; Bessel gives M p_u=Σ_i |⟨f_i,1_u/√p_u⟩|²≤1. Hence even the min-entropy of the pair is at least log M. Shannon entropy of the pair is the sum of the two individual tape entropies. A uniform average over pairs includes each dealer with probability 2/D, proving the bound. Combining this bound for fixed-length fair tapes with the known general fair-coin Ω(t²) bound shows Θ(t²+t log n) within this fixed prefix-dealer chain template for t≥2: when n≥2t and n grows, log M is of order log n; otherwise t is of order n and the quadratic term suffices. Bounded edge cases do not affect the asymptotic order. This particular bound only concerns the stated template and is not an unrestricted entropy lower bound. In the broader Gál–Rosén restricted (additively masked-message) class, the fair-coin order also follows by combining their existing Ω(t log(n/t)) with the general Ω(t²) lower bound and this new upper construction, because t log t≤t² and every one of our protocol messages splits additively into an input-only and a tape-only term.

## 4. Deterministic explicit short generator

It is enough to make every dealer's cut vector on every J of size at most 2t exactly uniform: then for any honest dealer its local variation space in Section 2 is already all ker B. For D=t the no-honest-dealer case is handled as in Section 2. We can always use n−1 independent bits. Alternatively construct an extension field K=F_(2^L), L=⌈log n⌉, and choose distinct nonzero α_j for the interior cuts j=1,…,n−1, for example the nonzero binary coefficient vectors in order in a fixed polynomial basis. Form binary columns of size tL by expanding the entries of

    v_j=(α_j, α_j³, …, α_j^(2t−1))  ∈ K^t.

Any at most 2t columns are F₂-independent. Otherwise a nonempty set S of s≤2t columns has sum zero, giving zero sums of odd powers ≤2t−1. Squaring repeatedly gives the same for every power 1,…,2t in characteristic two. The s by s matrix with entries α_j^i for i=1,…,s and j∈S is a Vandermonde matrix times an invertible diagonal with entries α_j, so these equalities cannot hold for the all-one coefficient vector. A uniform tL-bit seed paired with the columns yields exactly uniform projections onto every J of size ≤2t, as required. This is the classical binary BCH-column construction, not a new coding result. With D=t, at most tL or n−1 bits per dealer are used. The extension field is constructible deterministically in polynomial time in n even by trying every monic degree-L binary polynomial and testing for factors of degrees up to ⌊L/2⌋, then using quotient arithmetic. This gives an explicit O(t² log n) fair-coin bound, matching the order of the nonexplicit Kushilevitz–Mansour benchmark for every fixed ε>0 in the range t≤n^(1−ε) (and separately, by the n−1 cap, when t=Ω(n)). It is not a full-range deterministic O(t² log(n/t)) statement.

## 5. Entropy of matching marginals with disjoint support

Let P,Q have disjoint supports on a common finite product of countable alphabets, and identical marginals on all ≤k coordinates, k≥1. Put M=(P+Q)/2. For any set S of at most k+1 words, a binary decision tree with depth at most |S|−1 isolates them: keep splitting any cell containing two marked words by a single equality test on a coordinate on which two differ. Both children meeting S have smaller marked size. Each terminal cell depends on at most k coordinates (inequality as well as equality tests are allowed) and contains at most one marked word. Its P and Q probabilities are equal, even though the queried coordinate can depend on earlier answers: each individual leaf is an event on its own fixed set of coordinates. Therefore the M probability of the marked word is at most half the M probability of its cell, since the word has only one sign. Summing gives M(S)≤1/2.

A countable probability law has its largest atoms in nonincreasing order: any positive threshold has finitely many atoms at or above it, so positive suprema are attained and one may recursively choose maxima. There must be more than k+1 atoms by the preceding inequality. For L=k+1, the top L have total mass ≤1/2, and every remaining atom has probability ≤(1/2)/L, with tail mass at least 1/2. By nonnegative summation,

    H(M) ≥ (1/2)log(2L).
    (H(P)+H(Q))/2 = H(M)−1 ≥ (log L−1)/2.

The entropy identity uses disjointness: the equiprobable sign is recovered from the word. For k≥1 one also has p_max+q_max≤1 by applying the marked-word statement to one largest atom of each law. Therefore the average entropy is at least −(1/2) log(p_max q_max)≥1. The combined lower bound is at least (1/3) log L: if log L≤3 use 1, otherwise use (log L−1)/2. All these arguments allow infinite entropy and can equivalently be obtained by tail monotone summation. Any input-independent tape mapping to P and to Q has entropy at least each output entropy, hence at least their average.

### A matching logarithmic-entropy encoder

For k≥1 take m=2k⁴ and use the distinct integer radii 0,1 and b_j=2j⁴ for 1≤j≤k. At each node z let c_z=1/Π_{u≠z}(z−u). Interpolating polynomials of degree ≤k on these k+2 nodes and extracting the degree-(k+1) coefficient gives Σ_z c_z z^ℓ=0 for 0≤ℓ≤k. (When ℓ=0 the term 0⁰ is interpreted as 1.) Let S₀=Σ_{c_z>0} c_z=Σ_{c_z<0}|c_z|. Choose the radius in the positive or negative class with probability |c_z|/S₀ and then a uniform binary word of length m and that weight. The sign of c_z gives a deterministic decoder on the support. For a fixed pattern of a ones in h≤k specified bits the probability conditional on radius z is

    (z)_a (m−z)_{h−a}/(m)_h,

where the falling factorial notation includes (x)_0=1. It is a polynomial in z of degree ≤h divided by a fixed nonzero denominator. All such marginal probabilities match by the moment equalities.

For the entropy bound let w₀=|c₀|. The ratio |c₁|/w₀ is Π_j b_j/(b_j−1) ≤ exp(Σ_j 1/j⁴) ≤ exp(4/3)<4; the sum bound follows by integrating x^(−4) from 1 onward, since b_j−1≥j⁴. For j from 1 to k, cancellation gives

    |c_(b_j)| / w₀
      = 1/(b_j−1) · Π_{ℓ≠j} ℓ⁴/|ℓ⁴−j⁴|
      ≤ 2^{2−j}/(b_j−1).

Indeed the corresponding square-power product is 2(k!)²/[(k−j)!(k+j)!]≤2 by factoring ℓ²−j². Each extra factor 1/(1+(j/ℓ)²) is ≤1, and is ≤1/2 at every ℓ<j, giving the bound. Multiplying by b_j increases the right side by a factor at most 2. Since S₀≥w₀ (the positive or negative sum containing 0 has this mass), the sum of the expected weights of the two output laws is at most 4+Σ_{j≥1}2^{3−j}=12. For each law H(word)=H(radius)+E log binom(m,radius) ≤ log(k+2)+E(radius) log m. An input-independent tape is the product of independent draws from the two full-word laws; select its requested half. The entropy cost is at most 2log(k+2)+12log m=O(log(k+1)). The distribution is rational and the result does not impose finite worst-case fair tosses for this tape. This construction shows that the exponential support bound of the fair-coin proof is not a linear Shannon bound for its general encoding primitive.

## 6. Lifting the entropy lower bound to actual protocols

For each fixed input x, let V_i(x) denote the full view of P_i, and M_i(x) its communications only, written as a product of n−1 records (one complete bidirectional record per counterpart, recording rounds and missing messages). An identical cut record of P_i cannot occur on two positive-probability executions of XOR whose P_i inputs differ and whose XORs agree. Indeed, one can splice the P_i input and tape from one execution into all other players' inputs and tapes from the other. The cut record matches; induction on rounds shows both sides of the cut keep their prescribed behavior. The tapes are in product support. Some party other than P_i still returns the previous value, but precisely one input has flipped in the new execution, a contradiction. This step uses zero error and the independence of private tapes, not equiprobability of tape outcomes.

Let X be uniform over even-parity inputs, independent of all tapes. For i=1,…,s set k=s−i+1 and Y(x)=(V₁(x),…,V_(i−1)(x)). Pair each even input x with x'=x+e_i+e_n, an involution without fixed points. This pair agrees on the first i−1 inputs and the XOR, so by joint t-privacy Y has the same law under both. Fix any value y with positive probability, necessarily positive under both. Their two conditional M_i laws have disjoint supports by the splice observation.

Take any ≤k counterpart indices E and put T=E∪{1,…,i−1}. Then i∉T, |T|≤s, and since s≤n−2 choose j outside T∪{i}. Set xhat=x+e_n+e_j; if j=n, this is just x. The pair x,xhat agrees on the first i inputs and on XOR, so by **joint** privacy for {1,…,i}, the joint law of (Y, M_i|_E) is equal under these two inputs. Also xhat and x' differ only at i,j, which are outside T; by **joint** privacy for T their (Y, M_i|_E) laws are equal, because the counterpart views in E each contain their corresponding record with P_i. Thus the original x,x' have identical joint (Y, M_i|_E) again. Dividing both sides by their same positive Pr[Y=y] proves the conditional marginal equality. No claim of independence after conditioning on the prefix views is needed; the conditioning values, not the tape law of the protocol, are auxiliary to the proof.

Apply the lemma of Section 5 at every such y and pair. Its average entropy bounds the average full-view entropy at those x,x' and y, since M_i is a function of V_i. Average first with the common Y law and then over involution pairs with their uniform weights. This gives

    H(V_i(X) | X, V₁(X),…,V_(i−1)(X)) ≥ max{1,(log(k+1)−1)/2}.

The distribution in this expression is precisely the experiment with uniform even X and the **original tapes**, not a reweighted choice of tape or conditioning branch. By the entropy chain rule and determinism given (X,R),

    H(R) = H(R|X) ≥ H(V₁(X),…,V_s(X) | X) ≥ L_s.

A proof with infinite entropy follows by the same extended nonnegative chain rule (or is trivial if H(R)=∞). The factorial form uses the uniform (1/3)log(k+1) lower bound from Section 5. The expression is Ω(t log(t+1)) for 1≤t<n and n≥3 since s≥t/2.

For adaptive independent fair coin tosses, conduct the same argument treating each private source as a full independent fair tape and each observed view as containing only the bits read. The argument for matching marginals is unchanged, and disjointness follows by splicing the finite consumed local tape prefixes of the two positive-probability records, an event of positive probability, then using correctness (or probability-one correctness, since a wrong terminating execution would have positive probability). If termination is almost sure, for fixed x interleave fair draws in deterministic execution order (round, party, then local order). Complete consumed strings form a prefix-free set under x, each with probability 2^(−length). Their entropy is exactly the conditional-on-x expected total tosses, even if infinite, and fixes the joint view at that input. The preceding chain-rule argument establishes the lower bound on the average over even inputs of this expectation, and therefore on at least one input. No statement compares that expected fair resource to the existing quadratic worst-case bound.
