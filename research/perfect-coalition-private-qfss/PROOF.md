# Perfect coalition privacy for quantum function sharing via synchronized estimation

## 1. Model and statement

Fix an n-qubit circuit family with a public L-bit description convention. Write C_w for the n-qubit unitary circuit indexed by an admissible description w in {0,1}^L. Invalid strings have a public default record, taken to be zero. The decoder for admissible strings is part of the public convention; membership in a more restricted chosen family need not be tested if we simply enumerate all syntactically valid circuits of the given format. If the format gives circuit cost bound G (including public interpretation and one supplied projector measurement), a single trial on one input copy costs at most G. We use the projector interface of Grilo–Movassagh Definition 1: each evaluator can apply the measurement {Pi,I-Pi} on its local data, and needs no classical description of the state or source of copies from the dealer. A finite executable public gate convention suffices. An arbitrary projector given only as a specification does not automatically have an efficient implementation; G includes whatever cost this interface has.

For a pure input |psi> and a projector Pi, the desired value is
`P_z = ||Pi C_z |psi>||^2`, with secret index z. The proof also works for independent copies of a fixed density operator rho, with P_z = tr(Pi C_z rho C_z*). Use a security parameter lambda >= 1 and additive output accuracy eta in (0,1]. Let t >= 0 be the maximum permitted number of colluders (not the source's strict threshold), and take p = Lt+1 parties. If L=0 or t=0 this gives p=1: the former describes only a single public circuit (privacy is vacuous even for the entire set), and the latter asks for no coalition privacy. Otherwise p>t. Public integers used below are

    B = ceil(1/eta),       D = 2^L,       M = 16 D,
    a = L+lambda+ceil(log2(p))+4,
    Q = 2 a B^2 M^2,     K = 8(lambda+1)+1.

Here eta may be replaced by the rational public precision 1/B. Use a finite field F of characteristic 2 with q=2^v > max(p,B), v=O(log(p+B+1)). Fix public nonzero distinct alpha_1,...,alpha_p in F and a public bijection iota:[0,q-1] -> F given by binary coordinate encoding, chosen so that iota(0)=0 and iota(1)=1. This is a label map, not the natural homomorphism of integers into a characteristic-two field.

**Theorem.** There is a perfectly t-private scheme for this family, with classical generation and reconstruction, no shared entanglement among evaluators and no inter-party communication, and independent local quantum evaluation. For each fixed admissible z, state, and projector, its classical reconstructed value differs from P_z by at most eta with probability at least 1-2^(-lambda). Its costs are:

* Generation: independent fair bits, t L v + K log2 M; each request contains L field symbols and K log2 M public-offset bits (the same offsets can be sent separately as public parameters of that execution).
* Each evaluation: at most ell = D Q copies of |psi>, once per evaluation of the entire K-vector of answers, not K times this amount. It returns K field elements.
* Classical reconstruction uses only the replies and fixed public parameters, not the secret, projector, state, dither, or generation tape. It runs in time polynomial in p,K,v and the bit length of B.

Copies per party are O(B^2 2^(3L) (lambda+L+log p)); the evaluator time is at most ell trials of cost G each, plus O(ell) exact counter updates and O(KDL) field operations. Counter, rational rounding, and field operations involve only polynomial bit lengths. In particular there is no exponential dependence on lambda for fixed L and eta, and no claim of an efficient evaluator as L grows. The same resource statement is polynomial in lambda,p for Gen and Rec as in the source when L, log(1/eta), and the public encoding parameters have the usual polynomial size; for t>=1, already L<p. Requests and responses are explicitly typed classical records in the source's general share spaces. The request is not required by Definition 1 to be a single n-qubit circuit; the source's particular Algorithm 2 has that additional form, which we do not claim. Outputs can also be transported as short rationals in [0,1] by injectively encoding field symbols; these rationals are not the individual estimated probabilities.

## 2. Defining the algorithms

Let the index bits z_j be interpreted as field elements 0 and 1. Generation samples independent uniform r_jk in F, for j=1,...,L and k=1,...,t, and forms

    c_j(X) = z_j + sum_(k=1)^t r_jk X^k.

Independently sample J_1,...,J_K uniformly in {0,...,M-1}, and define U_h=J_h/M. The request to party i is the tuple (c_1(alpha_i),...,c_L(alpha_i); J_1,...,J_K). All public values p,L,lambda,B and the alphas are fixed for the scheme or that publicly indexed parameter instance.

For each valid circuit w, party i runs C_w on Q fresh copies of |psi> and measures {Pi,I-Pi}, taking a sample frequency pHat_i(w) in [0,1]. The i-th party's invalid records are set to zero, with no trials. There are at most D Q trials. The party estimates the table once, and uses the same estimates for all h. For each h it computes the rounded local table

    bHat_i,h(w) = floor(B pHat_i(w) + U_h),   in {0,...,B}.

Because the frequencies have denominator Q and U_h denominator M, this rounding can be computed exactly with integers on the measured counts. The estimates are not sent. It then evaluates the multilinear database polynomial of this table at its query point v_i=(c_j(alpha_i))_j:

    y_i,h = sum_(w in {0,1}^L) iota(bHat_i,h(w)) Phi_w(v_i),
    Phi_w(V) = product_(j:w_j=1) V_j * product_(j:w_j=0) (1-V_j).

Thus each response is (y_i,1,...,y_i,K) in F^K. Circuit enumeration order and all post-processing are public. Each program is a fixed universal classical-control routine with the request record as classical data. Any public format needed to transmit fixed-size request/response values can use the tagged union (F^L times [M]^K) disjoint-union F^K as S_i. This explicitly accommodates the source's notation using the same S_i for shares and outputs.

For h=1,...,K, Rec takes the unique degree-at-most-p-1 polynomial through the p points (alpha_i,y_i,h), and evaluates it at 0. Equivalently, precompute public Lagrange coefficients and apply them to each field-symbol answer column. Map the recovered field element back to an integer a_h in [0,q-1], convert it to min(1,a_h/B), and output the median of the K resulting rationals. Interpolation and median are defined even if the parties' sampled tables differ. Since K is odd this median needs no tie convention; it is an element of the sorted list at the middle index. In characteristic 2, subtraction and addition coincide inside the polynomial, but inverse labels and the median are ordinary integer computations.

## 3. Exact joint share privacy

Fix any coalition I with k <= t. For k>0, the linear map (r_j1,...,r_jt) -> (sum_h r_jh alpha_i^h)_(i in I) is surjective. Its first k columns form the ordinary Vandermonde on the k distinct alpha_i, multiplied by diag(alpha_i), hence are invertible. A uniform vector on a finite field space has exactly the same number of preimages at each image point; therefore this evaluation vector is uniform in F^k. Adding the constant z_j to each component changes no distribution. Independence over j gives the complete coalition query uniform over (F^L)^k, not just its individual coordinates. The empty coalition is trivial. For L=0 there is no secret choice and no query coordinates, also trivial regardless of t.

The public dither tuple is independent of this constant-shift masking and z, so even conditional on that entire tuple all coalition requests have the same distribution for all z. This proves equality of joint views in the source IndQFSS game, and shows the same for arbitrary postprocessing of those requests with circuit-independent local information, including fixed quantum inputs and parties' own responses. It is not a claim of privacy against a coalition seeing the other parties' private channels or all server messages. No computational restriction, related-input assumption, or quantum shared randomness is used for this t-coalition privacy claim.

## 4. Shared quantization and correctness

Fix z, |psi>, and Pi before the random choices, as in Definition 1. For every w let P_w be the exact probability for the trial (zero for invalid w). Write b_h(w)=floor(B P_w+U_h) for the ideal rounded table. Since U_h is in [0,1), for every w one has

    0 <= b_h(w) <= B,          | b_h(w)/B - P_w | < 1/B.

No assertion needs to hold simultaneously for all possible quantum states with one fixed tuple of dithers. For each fixed table, call J good if the distance from B P_w+J/M to the nearest integer exceeds 1/M for every w. For a given w, the forbidden J/M lie in a closed arc of length 2/M on the unit circle. Among the M equally spaced points a closed arc of that length contains at most three points (using four is a convenient bound valid also by splitting at the wrap). Taking a union over D records gives a failure probability <=4D/M=1/4 for each independent dither. The fraction of good dithers has mean at least 3/4. Hoeffding's lower-tail bound yields

    Pr[# good dithers <= K/2] <= exp(-K/8) <= 2^(-lambda-1).

Separately let G_est be the event that all parties' estimates satisfy

    |pHat_i(w) - P_w| <= epsilon = 1/(2 B M).

Each frequency is the mean of Q independent Bernoulli trials on copies. Hoeffding gives per-estimate failure at most 2 exp(-2 Q epsilon^2)=2 exp(-a). The union bound over at most p D estimates gives

    Pr[not G_est] <= p D 2^(1-a) <= 2^(-lambda-3).

The union bound does not require independence across different circuits or parties; independence of fresh shots within each frequency suffices. On G_est, a good J_h ensures all local roundings agree with the exact b_h(w), because the argument of floor changes by at most 1/(2M) and started more than 1/M away from an integer. Thus for every good h all parties answer from exactly the same encoded table, even though they measured their copies separately.

Let F_h(V)=sum_w iota(b_h(w)) Phi_w(V). For Boolean z the selector Phi_w(z) is exactly 1 when w=z, 0 otherwise, so F_h(z)=iota(b_h(z)). The composed polynomial X -> F_h(c_1(X),...,c_L(X)) has degree at most Lt=p-1. Therefore for a good h all its values at the p public points are the received responses, so interpolation at 0 returns iota(b_h(z)), and clipping does not change b_h(z)/B. Every good rounded reconstruction lies in [P_z-eta,P_z+eta]. When more than half are good, their common interval contains the median regardless of the other reconstructions. Taking the union of the failure bounds gives total failure <=2^(-lambda-1)+2^(-lambda-3)<2^(-lambda). There is no interpolation of approximate real samples, so there is no unaccounted condition number: agreement on the rounded table makes the field interpolation exact.

## 5. Finite computation and optional tradeoff

A deterministic polynomial-bit way to choose the field suffices. Let v be the smallest power of two at least ceil(log2(max(p,B)+1)) and at least one; then q=2^v>max(p,B). Construct F_2 and iteratively double the extension degree. In a field of size 2^e use the absolute trace Tr(x)=sum_(j=0)^(e-1) x^(2^j). This F_2-linear map is nonzero because the displayed polynomial is nonzero of degree 2^(e-1)<2^e, and its values lie in F_2 by Frobenius invariance. Find a trace-one basis vector by checking the e standard binary basis vectors. The image of x -> x^2+x is the trace-zero hyperplane: its trace is zero, kernel has size two, and the hyperplane has half the field size. Thus U^2+U+a for trace-one a is irreducible and can be used for the next quadratic extension. Coefficient arithmetic, trace finding, and inversion are polynomial in v in this tower (e.g. by elementary repeated squaring and recursive polynomial multiplication). Evaluating each c by Horner and constructing the public interpolating weights therefore costs polynomial bit time. Encode independent uniform field samples by v fair bits and offsets by log2 M fair bits, with no rejection step. The exponents and all exact counters have bit length polynomial in L,lambda,log(p+B+1). In particular the number of trials may be exponential while its counter and the final rational have polynomial bit length.

If only one field response is wanted, use K=1, choose M=2^(L+lambda+4), and retain a and Q=2 a B^2 M^2 with that M. The same bad-arc union is then <=2^(-lambda-2) and the empirical bound is unchanged; a single good dither suffices for correctness. This reduces upload/response overhead but increases copy count by a factor 2^(2lambda) relative to the main variant. The median variant reuses a single sampled table, paying only a classical K-factor and not a K-factor in quantum copies.

## 6. What is and is not the contribution

For a pre-existing common classical table, Sections 2–3 are a standard polynomial-based multi-server PIR instance (see Kruglik–Dau–Kiah–Wang–Zhang, §2.2, protocol Π0, and the earlier PIR literature). The issue here is that the shared database does not exist before evaluation: only copies of an unknown quantum state and a supplied measurement are available to otherwise independent evaluators. The probability-table sampling, synchronized finite dither, exact field computation, and median argument give a full positive QFSS instantiation with deterministic polynomial classical reconstruction and perfect coalition privacy. The premise is the share-space interface of Grilo–Movassagh §3.1; the evaluator may be exponentially costly. Its Eq. (5) uses a strict |I|<t_source notation, while its prose and advertised singleton example use maximum-coalition terminology. Our at-most-t guarantee meets the literal equation with t_source=t+1, or the prose convention with maximum coalition size t, whenever the nontrivial parameters apply. This is a partial positive answer to §1.1.3's request for alternatives, not a claim about the party/time tradeoff of its specific Cayley implementation.

The result is decisional probability sharing, not a protocol returning an output quantum state. There is no claimed verifiability, active correctness, hiding of the number of parties/description format, promise for exponentially precise eta at polynomial cost, privacy from a dealer who knows the selected circuit, or direct practical blind computation. The state/measurement are the same input for each party in the correctness experiment, and no statement is made if these are chosen adaptively after learning the dithers. No original negative result is used or rederived.
