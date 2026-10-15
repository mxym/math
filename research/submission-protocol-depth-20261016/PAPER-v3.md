# Finite-block universal extraction, dimension growth, and the sharp cost of an unknown support

Author mathematics draft v3, 16 October 2026. Yongxian Zhang, South China University of Technology. OpenAI AI assistants assisted. No external funding. Original rights reserved; third-party mathematical inputs credited below. This is an ordinary written proof, not Lean certification or external human peer review. It strengthens the earlier state-aware and universal-Schur manuscripts without changing their resource model. No claim of an efficient ancilla-free circuit is made.

## 1. Model and three different quantifiers

Fix integers 2 <= m <= n, D=mn and k>=1. Write a=m^k, b=n^k, N=D^k. All logarithms are natural. A protocol is one fixed unitary U on the original a by b input, followed by a deterministic channel Lambda to K by K output. There is no extra system, discarded register, or measurement before U. Local ancillas and discarding after U are permitted. The fidelity is Tr(Phi_K Lambda(U rho^{tensor k} U*)), where Phi_K is the normalized maximally entangled projector. LO denotes local product channels; LOCC and completely PPT (cPPT) have their usual inclusions LO <= LOCC <= cPPT. Both Lambda and Gamma_out Lambda Gamma_in are channels in cPPT.

Three statements must be kept distinct.

1. The all-state universal family depends on m,n,k,K and is the same for every rho, including its spectrum, eigenbasis and rank.
2. A state-aware upper bound permits U and Lambda to depend on rho.
3. The rank-budget minimax value permits dependence on the specified integer s, but one common U,Lambda must serve every rho of rank at most s:

    G_C(k,K;s) = sup_(U,Lambda in C) inf_(rank rho <= s) F(U,Lambda;rho).

The rank-budget protocols below do not by themselves constitute the all-state universal family in item 1. In particular a constant-output Bell dimension suited to the worst rank-s state need not attain the larger capacity of a nonuniform rank-s state. No random choice of a state-dependent unitary is used in any achievability argument. Haar averages occur only in converses.

## 2. An all-finite-block universal Schur construction

Use the standard Schur--Weyl decomposition

    (C^D)^{tensor k} = direct_sum_lambda Q_lambda(D) tensor P_lambda,
    rho^{tensor k} = direct_sum_lambda Q_lambda(rho) tensor I_(v_lambda).

Here lambda ranges over partitions of k with at most D rows, J is their number, u_lambda=dim Q_lambda(D), v_lambda=dim P_lambda, r_lambda=u_lambda v_lambda, and u_star=max_lambda u_lambda. This decomposition, the Weyl/hook dimensions, and irreducibility are credited standard inputs [KW,BCH]. Bases are fixed without rho.

For every m,n,k,K the following unitary and local channels exist. Set a0=floor(a/J), b0=floor(b/J), N0=a0 b0. If a0=0 use the deterministic product-output channel. Otherwise allocate one disjoint a0-coordinate sector at Alice and one disjoint b0-coordinate sector at Bob to each lambda. Select

    v'_lambda = min(v_lambda, floor(N0/u_lambda)),
    S_lambda = Q_lambda(D) tensor span(e_1,...,e_(v'_lambda)).

Zero selected multiplicity is allowed and means that the selected subspace is empty. If r'_lambda=u_lambda v'_lambda>0, let d_lambda be the largest integer d<=min(K,a0) for which

    floor(a0/d) floor(b0/d) >= r'_lambda.

At least d=1 is feasible. Map a fixed basis of S_lambda to r'_lambda distinct vectors

    psi_(lambda,i,j) = d_lambda^(-1/2)
       sum_(t=0)^(d_lambda-1) |lambda,i d_lambda+t>_A
                                 |lambda,j d_lambda+t>_B.

All selected vectors are orthonormal. The selected domain dimension is at most J N0<=N, so this partial isometry extends to one unitary on the original N-dimensional input. No added ancilla is required for this existence statement.

On sector lambda, Alice's Kraus maps are

    A_(lambda,i) = sum_(t<d_lambda) |t>_K <lambda,i d_lambda+t|,

and |0><x| for every unused local coordinate. Bob uses the analogous maps. The Kraus adjoint products sum to the respective local identity, including outside all allocated sectors. These are deterministic product channels.

For all selected pairs,

    (A tensor B)(|psi_(i,j)><psi_(i',j')|)
      = delta_(i,i') delta_(j,j') Phi_(d_lambda).

Consequently every density matrix on the entire selected code space maps to Phi_(d_lambda), not just mixtures of the displayed basis projectors. This handles unknown coherences in Q_lambda(rho). The source state has no coherence between the selected and unselected multiplicity spaces, since its multiplicity factor is the identity; it also has no coherence between different lambda. Thus all unselected parts give positive contributions.

A whole block is extracted with full dimension K whenever

    K<=a0 and r_lambda<=G,
    G=floor(a0/K) floor(b0/K).

Indeed r_lambda<=G<=N0 implies u_lambda<=N0 and v_lambda<=floor(N0/u_lambda), so no truncation occurs; d_lambda=K is feasible. This remains true at equality and when other blocks have empty selections. Therefore, for the same protocol and every rho,

    F_univ(rho,K) >= sum_(r_lambda<=G) t_lambda(rho),
    t_lambda=Tr(Pi_lambda rho^{tensor k}).                         (2.1)

For K=1 one can always output the exact product target. Conditions involving a0 below are used only when a0>=K>=1, so G>=1 and log G is defined.

## 3. Explicit dimension-dependent information-spectrum bounds

Let p be the eigenvalue law of rho, zeros allowed. For X distributed according to p on its positive support, put Z=-log p_X and S_k=Z_1+...+Z_k. This scalar random variable is defined separately for each input state. It does not enter the protocol.

**Theorem 3.1 (finite-block sandwich).** The common protocol of Section 2 obeys, whenever K<=a0,

    Pr{S_k <= log(G/u_star)} <= F_univ(rho,K).                  (3.1)

For every state-aware unitary plus cPPT protocol, every integer K>=1 and every t>0,

    F_star(rho,K)
      <= Pr{S_k <= log(N/K^2)+t} + exp(-t/2).                 (3.2)

If a>=2J and K<=a0, then with

    h=log(16 J^2 u_star),  x=log(N/K^2),

we have the entirely explicit version

    Pr{S_k<=x-h} <= F_univ(rho,K)
       <= F_star(rho,K) <= Pr{S_k<=x+t}+exp(-t/2).            (3.3)

All assertions are simultaneous in finite m,n,k,K and every rho; there is no hidden fixed-dimension limit.

*Proof of the lower bound.* On a Schur block, v_lambda Tr Q_lambda(rho)=t_lambda<=1. Thus Q_lambda(rho)<=I/v_lambda, so every positive eigenvalue x_i in this block satisfies

    x_i <= 1/v_lambda = u_lambda/r_lambda <= u_star/r_lambda.

If r_lambda>G, then x_i<u_star/G. Therefore the spectral event -log x_i<=log(G/u_star) can occur only in fully extracted blocks. Equation (2.1) proves (3.1). Notice that the argument uses the distribution under rho^{tensor k}, not the spectrum of the block probabilities.

For (3.2), write M=Lambda*(Phi_K), before the input unitary. The Rains constraints give

    0<=M<=I, -I/K<=M^Gamma<=I/K,
    Tr M^2<=N/K^2, ||M||_infty<=min(1,a/K).                  (3.4)

The first two constraints and the Hilbert--Schmidt isometry under partial transpose prove the squared-trace bound. The norm bound follows by pairing M^Gamma with the partial transpose of a rank-one projector; its trace norm is at most a [R]. Conjugate M by U and take diagonal entries z_i in an eigenbasis of rho^{tensor k}. Then 0<=z_i<=1 and sum z_i^2<=Tr M^2<=r=N/K^2. The eigenvalues smaller than exp(-(log r+t)) contribute at most

    sqrt((sum_small x_i^2)(sum_small z_i^2))
       <=sqrt(exp(-(log r+t)) r)=exp(-t/2),

since sum_small x_i<=1. The other contribution is bounded by their total input probability. This proves (3.2), including singular rho and targets larger than a.

Finally a0>=a/(2J), b0>=b/(2J), and a0,b0>=K. Therefore

    G>=a0 b0/(4K^2)>=N/(16J^2 K^2),

which proves (3.3). Every floor loss has been retained. ∎

For computation without enumeration,

    J <= (k+1)^D,
    u_star <= (k+D)^(D(D-1)/2),
    h <= log16+2D log(k+1)+D(D-1)/2 log(k+D).                (3.5)

These bounds are intentionally conservative. Their constants remain visible when D grows.

**Corollary 3.2 (quantitative Gaussian sandwich).** Suppose V=Var(Z)>0, T=E|Z-H(p)|^3, sigma=sqrt(kV), beta=C_BE T/(V^(3/2) sqrt k), and y=(x-kH(p))/sigma. Under the hypotheses of (3.3),

    Phi(y-h/sigma)-beta <= F_univ(rho,K),
    F_star(rho,K)<=Phi(y+t/sigma)+beta+exp(-t/2).             (3.6)

This is the ordinary iid Berry--Esseen theorem [BE], applied within one row of the array; C_BE is any fixed admissible universal iid Berry--Esseen constant (one may take 1); no constant optimization is claimed. Both bounds are nonasymptotic and may be clipped to [0,1].

For a sequence of dimensions, states, blocklengths and target integers satisfying K<=a0, a>=2J, suppose

    k V -> infinity,
    T/(V^(3/2) sqrt k) -> 0,
    h/sqrt(kV) -> 0.                                       (3.7)

Then, uniformly over all rows meeting these conditions and their requested target values,

    F_univ - Phi((k(log D-H)-2log K)/sqrt(kV)) -> 0,
    F_star - Phi((k(log D-H)-2log K)/sqrt(kV)) -> 0.          (3.8)

More precisely, if sigma>1 and t=2log sigma, both absolute errors are at most

    beta + max(h,2log sigma)/(sqrt(2pi) sigma) + 1/sigma.    (3.9)

Thus fixed dimensions, a fixed state, and fixed positive varentropy are not needed for (3.8). Conversely none of (3.7), the local output constraint, or the positive-variance assumption may be dropped by appealing to the earlier pointwise CLT.

For a useful dimension-growth regime, assume V is between two positive constants times 1/D, and T<=C/D, uniformly along the sequence. Then beta=O(sqrt(D/k)). Condition (3.5) shows that

    D^5 [log(k+D)]^2 = o(k)                               (3.10)

is sufficient for (3.7). This is a sufficient, nonoptimal blocklength condition for this particular universal construction. It is not asserted to be a necessary sample complexity, nor to hold for every APPT near optimizer. Applying it to APPT requires separately proved spectral moment hypotheses. In contrast, (3.1)--(3.3) already apply to every APPT state without any such hypothesis.

## 4. A general unknown-support packing lemma

Let S be any known r-dimensional subspace of C^a tensor C^b. The unknown input can be any state supported on S. For every integer d<=min(a,K) satisfying

    floor(a/d) floor(b/d)>=r,                              (4.1)

there is one unitary on the original input followed by deterministic product channels which maps every state supported on S exactly to the embedded Phi_d. Its Phi_K fidelity is d/K.

Choose an orthonormal basis of S, map it to r distinct Bell-coded vectors d^(-1/2) sum_t |i d+t,j d+t>, extend the partial isometry to a unitary, and use the local discard maps from Section 2. The dyad identity there proves the assertion for all coherences. This is a coherent subspace code and no pre-unitary ancilla or shared randomization is present.

If r<=ab and w=min(a,K,sqrt(ab/r)), then

    d=max(1,floor(w/2))

satisfies (4.1) and d>=w/4. This follows from floor x>=x/2 for x>=1. Thus at least one fourth of the envelope min(1,a/K,sqrt(ab/r)/K) is uniformly attainable for every such subspace at every finite dimension.

If a=b, h_r=ceil(sqrt r) and d0=floor(a/h_r)>=1, the sharper choice d=min(K,d0) is feasible, so the lower fidelity is min(1,d0/K). The whole subspace is encoded together; knowing an eigenbasis of the unknown input is unnecessary.

### A general minimax principle for a common support

Let F be any family of density matrices on a by b dimensions, all supported on a known rank-r projector P. Let nu be any probability law on F with average Omega, and suppose supp Omega=P. The inputs need not be iid or pure. Define H_C(F,K) by choosing one U and one postprocessing channel before taking the infimum over sigma in F. Put

    w=min(a,sqrt(ab/r)),
    d=max{integer 1<=j<=a: floor(a/j)floor(b/j)>=r},
    eta=sqrt(r Tr Omega^2)>=1.

Then, simultaneously for every target integer K>=1,

    min(1,d/K)<=H_LO(F,K)<=H_LOCC(F,K)<=H_cPPT(F,K)
       <=min(1,a/K,sqrt(ab Tr Omega^2)/K).                 (4.2)

Moreover, uniformly in K,

    | H_C(F,K)/min(1,w/K)-1 |
       <=max(1-d/w,eta-1).                               (4.3)

The lower bound is the actual coherent subspace packing above. For the upper bound, an infimum is bounded by its average, and the effective cPPT fidelity effect M satisfies Tr M^2<=ab/K^2 and ||M||<=a/K even after conjugating by the chosen U. Hence Tr(Omega M)<=sqrt(Tr Omega^2 Tr M^2). This uses the probability law only as an adversarial converse argument, not as a free randomization resource. Formula (4.3) follows because min(1,d/K)>=d/w min(1,w/K), and the upper envelope is at most eta min(1,w/K).

Thus any sequence of families for which r Tr Omega^2->1 and d/w->1 has a sharp, relative, all-target minimax law with LO achievability and a cPPT converse. The collision condition has a direct geometric meaning:

    ||Omega-P/r||_1 <=sqrt(r Tr Omega^2-1).

It says that the chosen average approaches the uniform state on the actual common support. A support dimension alone gives the constructive lower bound; an appropriate sufficiently flat average is what closes the minimax converse. If all inputs are extracted exactly, positivity implies M=I on supp Omega=P, whence K<=a and K^2 r<=ab. This also explains why an arbitrary larger ambient rank cannot replace the actual support in a sharp conclusion.

## 5. The support of every rank-s iid input

Fix 1<=s<=D and define

    S_(k,s)=direct_sum_(lambda: ell(lambda)<=s)
               Q_lambda(D) tensor P_lambda,
    r_(k,s)=sum_(ell(lambda)<=s) u_lambda(D) v_lambda.        (5.1)

Every rho of rank at most s has rho^{tensor k} supported on S_(k,s), by Schur--Weyl duality and vanishing of Schur characters with too many rows.

Let P_s be one fixed rank-s projector in C^D and form the normalized Haar average

    Omega_(k,s)=integral_(W in U(D)) (W P_s W*/s)^{tensor k} dW. (5.2)

This is only a mathematical adversarial average. It is never implemented by the protocol. On a block with at most s rows, Schur's lemma gives the eigenvalue

    c_lambda = u_lambda(s)/(s^k u_lambda(D)),                (5.3)

with multiplicity u_lambda(D)v_lambda. Indeed the trace of Q_lambda(P_s) is the Schur value in s ones, namely u_lambda(s); unitary averaging divides this trace by u_lambda(D). Blocks with more than s rows have zero weight. Thus Omega is strictly positive on exactly S_(k,s). In particular this is the smallest common support subspace for all rank-at-most-s iid inputs.

For 1<=s<D put g=s(D-s) and

    C_(D,s)= s^(-g) / product_(1<=i<=s<j<=D)(j-i).           (5.4)

**Theorem 5.1 (rank-support asymptotics).** With fixed integers D and s<D,

    r_(k,s) ~ C_(D,s) s^k k^g,
    Tr(Omega_(k,s)^2) ~ 1/(C_(D,s) s^k k^g),
    r_(k,s) Tr(Omega_(k,s)^2) -> 1.                        (5.5)

*Proof.* For ell(lambda)<=s, pad lambda by zeros and cancel the Weyl products to obtain the exact ratio

    R_lambda=u_lambda(D)/u_lambda(s)
       =product_(1<=i<=s<j<=D)(lambda_i+j-i)/(j-i).          (5.6)

In particular R_lambda>=1. The Schur--Weyl law for the maximally mixed s-dimensional state is

    t_lambda=u_lambda(s)v_lambda/s^k,
    sum_lambda t_lambda=1.                                (5.7)

Equations (5.1),(5.3) give the exact identities

    r_(k,s)=s^k E_t R_lambda,
    Tr(Omega^2)=s^(-k) E_t(1/R_lambda).                    (5.8)

Under t, lambda/k tends exponentially in probability to (1/s,...,1/s). An explicit justification is the highest-weight estimate

    t_lambda <= (k+s)^(s(s-1)/2) exp(-k D(lambda/k || 1/s)),

combined with at most (k+1)^s diagrams. Outside any fixed neighborhood of the uniform vector, relative entropy has a strictly positive minimum by compactness. Thus the bad probability is polynomial times exp(-c k).

Uniformly in lambda, R_lambda/k^g is bounded by a constant depending only on D,s, for k>=1. On every shrinking-to-the-uniform-point good region it tends to C_(D,s), so boundedness and concentration imply E R_lambda/k^g -> C_(D,s).

For the inverse moment choose a fixed small delta in (0,1/(2s)) and the good event max_i |lambda_i/k-1/s|<=delta. On that event each lambda_i>=k/(2s), so k^g/R_lambda is bounded by a constant depending only on D,s, and its limiting value as delta decreases to zero is 1/C_(D,s). On the complement, R_lambda>=1 implies k^g/R_lambda<=k^g, whose expectation is bounded by k^g times an exponentially small probability. Therefore k^g E(1/R_lambda)->1/C_(D,s). Multiplying the two limits proves (5.5). This explicit bad-event argument supplies the needed uniform integrability; convergence in probability alone would not suffice. ∎

At s=1, S_(k,1)=Sym^k(C^D), r=binom(k+D-1,D-1), Omega=Pi_sym/r, g=D-1 and C_(D,1)=1/(D-1)!. The identity for Omega can equivalently be proved by integrating occupation-number monomials over the Haar unit sphere; each normalized symmetric basis vector has the same average squared coefficient 1/r.

At s=D, S is the whole N-dimensional input and Omega=I/N exactly. The asymptotic statement may be replaced by these exact identities.

### An effective exact formula for the support rank

The support count also admits a classical RSK/Toeplitz evaluation; we make no novelty claim for this enumeration. It is useful because the finite-block rank in the protocol and converse can be computed exactly, before any asymptotic replacement.

For fixed integers 1<=s<=D and indices 0<=i,j<s, set

    p_ij(q)=binom(D+q+i-j-1,D-1),
    H_ij(t)=sum_(ell=0)^(D-1) Delta^ell p_ij(0) t^ell/ell!,
    P_(D,s)(t)=det_(0<=i,j<s) H_ij(t).                    (5.9)

Here Delta is the forward finite difference, and the binomial is its polynomial value. The arguments at q>=0 are nonnegative integers, since D>=s. Then

    sum_(k>=0) r_(k,s) t^k/k! = exp(s t) P_(D,s)(t).       (5.10)

If P=sum p_j t^j, the exact all-k rank is

    r_(k,s)=s^k sum_j p_j (k falling j)/s^j,               (5.11)

where k falling j is zero when j>k. In particular r_(k,s)/s^k is exactly a polynomial in k. Its degree is g=s(D-s) and its leading coefficient is C_(D,s); at s=D it is identically one.

For completeness, the truncated Cauchy identity gives

    sum_(ell(lambda)<=s) s_lambda(1^D) f_lambda t^|lambda|/|lambda|!
      = det_(0<=i,j<s) sum_(q>=0) h_(q+i-j)(1^D) t^q/q!.

One obtains this identity directly by Cauchy--Binet on the infinite matrices of complete symmetric functions: strictly ordered selected column indices correspond to partitions with at most s rows, and the two minors are the Jacobi--Trudi determinants. On the second specialization h_q=t^q/q!, the second determinant is f_lambda t^|lambda|/|lambda|!. Formal power-series truncation makes the Cauchy--Binet calculation finite at every coefficient. This is the standard Gessel identity used by Tracy--Widom [TW99, Theorem 1]. Since h_l(1^D)=binom(D+l-1,D-1) for l>=0 and zero otherwise, each entry is sum_q p_ij(q)t^q/q!. For the finitely many q with q+i-j<0 the displayed binomial polynomial is also zero, as its top argument lies in {0,...,D-2}. Newton's finite-difference expansion gives this entry as exp(t) H_ij(t), proving (5.10) and (5.11). A priori the determinant degree is at most s(D-1); the already independently proved (5.5) forces its degree to be exactly g and its leading coefficient to be C_(D,s) s^g.

For example,

    P_(4,2)(t)=1+2t+2t^2+(2/3)t^3+(1/12)t^4,
    r_(k,2) at D=4 = 2^k (k^4+10k^3+59k^2+122k+192)/192;

    P_(4,3)(t)=1+t+t^2/2+t^3/6,
    r_(k,3) at D=4 = 3^k (k^3+6k^2+47k+162)/162.

The exact support count is classical; its use with the average-state collision moment in (4.2)--(4.3) is the operational matching argument here. No counting formula is used as a substitute for a physical extraction channel.

## 6. Sharp minimax fidelity and a logarithmic universality cost

The effect bounds (3.4) imply, for every common protocol serving all rank-at-most-s states,

    inf_(rank rho<=s) F(rho)
      <=Tr(Omega U*M U)
      <=min(1,a/K,sqrt(N Tr Omega^2)/K).                    (6.1)

The last inequality is Hilbert--Schmidt Cauchy--Schwarz. It does not twirl, randomize, or modify the chosen protocol. Since an infimum is at most its average, the same upper bound holds after taking the supremum over all fixed protocols, including cPPT.

Conversely Section 4 applied to S_(k,s) gives one common LO protocol for the entire rank-budget class. Let

    w_k=min(a,sqrt(N/r_(k,s))),
    d_k=max{d in {1,...,a}: floor(a/d)floor(b/d)>=r_(k,s)}.  (6.2)

Then for all K>=1,

    min(1,d_k/K) <= G_LO(k,K;s)
       <=G_LOCC(k,K;s)<=G_cPPT(k,K;s)
       <=min(1,a/K,sqrt(N Tr Omega^2)/K).                  (6.3)

The lower protocol uses Bell dimension min(K,d_k), and therefore works even if K exceeds both local input dimensions. It depends on s, not on the state within the class.

**Theorem 6.1 (entire sharp minimax profile).** Fix m,n,s with 2<=m<=n and 1<=s<D. Then, for every C in {LO,LOCC,cPPT},

    sup_(integers K>=1)
      | G_C(k,K;s)/min(1,w_k/K) - 1 | -> 0.                (6.4)

Thus the equivalence is relative and uniform over every target integer, including exponentially small fidelities. It is stronger than equality of capacities or first-order fidelity exponents.

*Proof of the floor asymptotics.* If n>ms, (5.5) gives r_(k,s)/(b/a)->0. Eventually floor(b/a)>=r_(k,s), so d=a is feasible. Here w_k=a exactly eventually, and d_k=w_k.

If n<=ms, then

    w_k=sqrt(N/r_(k,s)) eventually,
    w_k/a -> 0, w_k/b -> 0, w_k -> infinity.              (6.5)

For n<ms the first two ratios vanish exponentially; at n=ms the polynomial factor k^(-g/2) makes them vanish. Set epsilon_k=sqrt(w_k/a+w_k/b), and choose d=floor(w_k/(1+epsilon_k)). For large k this is positive. Using (a/d-1)(b/d-1) as a lower bound for the product of floors, divide by r=N/w_k^2 to obtain

    floor(a/d)floor(b/d)/r
      >= (w_k/d)^2 - (w_k/d)(w_k/a+w_k/b) + 1/r.

For 0<q_k=w_k/a+w_k/b<1, w_k/d>=1+sqrt(q_k), and z^2-z q_k is increasing for z>=1. Consequently the right side is at least

    (1+sqrt(q_k))^2-(1+sqrt(q_k))q_k
      =1+2sqrt(q_k)-q_k^(3/2)>1.

Thus d is feasible, d/w_k->1, and d_k/w_k->1. Also d_k<=w_k by (6.2).

By (5.5), eta_k=sqrt(r Tr Omega^2)->1. The upper envelope in (6.3) is at most eta_k min(1,w_k/K), while the lower envelope is at least (d_k/w_k) min(1,w_k/K). These bounds are independent of K, proving (6.4). ∎

For s=D the exact minimax value is 1/K for every k and K: the maximally mixed input and (3.4) give the upper bound; the deterministic product-output channel gives equality. This is not a positive-capacity statement.

### Exact and fixed-error targets

Let K_C^0(k;s) be the largest integer target dimension admitting one protocol with fidelity exactly one for every rank-at-most-s input. Exact performance implies that the effective fidelity operator is the identity on S_(k,s): averaging yields Tr Omega(I-U*M U)=0, and positivity with Omega strictly positive on S implies (I-U*M U)S=0. Hence

    K<=a and K^2 r_(k,s)<=N.                              (6.6)

The LO construction gives

    d_k<=K_LO^0<=K_LOCC^0<=K_cPPT^0<=floor(w_k).           (6.7)

In particular, in the entropy-limited and boundary regime n<=ms,

    log K_C^0(k;s)
      = k/2 log(D/s) - g/2 log k - (1/2)log C_(D,s)+o(1). (6.8)

If n>ms, the exact value K_C^0=a holds for all sufficiently large k. The polynomial support factor changes the boundary n=ms: its leading capacity equals log m, but its exact universal target still pays the logarithmic correction in (6.8).

For fixed 0<epsilon<1, define K_C^epsilon by requiring the worst-class fidelity at least 1-epsilon. Equation (6.4), or directly (6.3), yields

    log K_C^epsilon(k;s)
       =log w_k-log(1-epsilon)+o(1).                       (6.9)

Integer rounding contributes o(1), since w_k tends to infinity for s<D. The lower bound uses floor(d_k/(1-epsilon)); the upper bound follows from (6.1) and eta_k->1. These targets may exceed the original local dimension when epsilon>0; the model allows arbitrary K-dimensional output channels, exactly as in the preceding extraction manuscripts.

### Balanced unknown pure inputs

For m=n, D=m^2, s=1, put r_k=binom(k+D-1,D-1). Then uniformly over K,

    G_C(k,K;1) ~ min(1,m^k/(K sqrt(r_k))).                 (6.10)

At the full local target K=m^k,

    G_C(k,m^k;1) ~ 1/sqrt(r_k)
       ~sqrt((D-1)!) k^(-(D-1)/2).                        (6.11)

A known pure input can be mapped directly to the full Bell state and has fidelity one. Thus ignorance is free at the capacity scale but incurs a sharp polynomial loss at the full-output endpoint. This is a finite-block universality cost, not an impossibility of positive-rate universal extraction.

For fixed error,

    log K_C^epsilon
       =k log m -(D-1)/2 log k +(1/2)log((D-1)!)
          -log(1-epsilon)+o(1).                           (6.12)

For fixed m<n, unknown pure inputs instead permit exact K=m^k eventually, since the available b/a garbage dimension eventually exceeds the polynomial symmetric-space dimension. The balanced boundary is essential to (6.11).

## 7. Compatibility with a completely unknown-state family

The pure-state sharp profile can coexist with all the earlier pointwise fixed-state capacity, strong-converse exponent, strict direct reliability, and nondegenerate Gaussian conclusions. This assertion is limited here to s=1; a rank-budget minimax optimum is not automatically compatible with all-state optimality.

Modify Section 2 as follows. Put q=(k+1)J, alpha0=floor(a/q), beta0=floor(b/q). Give every non-symmetric Young block one alpha0 by beta0 sector. Give the symmetric block all remaining local coordinates,

    alpha_sym=a-(J-1)alpha0,
    beta_sym=b-(J-1)beta0.

For each lambda use its assigned local capacities, select only multiplicity factors, choose the maximal feasible d_lambda, and extend the joint partial isometry as before. All-finite-k construction is valid, allowing empty selections. For sufficiently large k at fixed D, alpha0 beta0>=2u_star and all capacities grow exponentially.

The proof of the prior universal exponent lower bound applies with the polynomial q in place of J: a selected block retains at least 1/(8q^2) of its mass, and its Bell dimension contributes at least 1/(8q) times the prior envelope. Thus the loss is at most 64q^3, whose logarithm is O_D(log k). Every block with r_lambda<=floor(alpha0/K)floor(beta0/K) is still extracted exactly, giving the same strict direct reliability and zero-error rates. Its information-spectrum overhead is at most log(16q^2 u_star), still O_D(log k), so the fixed-state Gaussian theorem is unchanged.

For a pure input only lambda=(k) is populated and v_lambda=1. For all sufficiently large k its entire symmetric subspace fits in the large symmetric sector. In balanced dimensions alpha_sym=beta_sym and alpha_sym/a->1. Choosing the largest feasible Bell dimension in that sector gives the lower bound

    F_univ(rho,K)>=min(1,floor(alpha_sym/ceil(sqrt(r_k)))/K)

simultaneously for every pure rho and every K. The upper bound (6.10) applies to every protocol, so this single completely unknown-state family also attains the sharp minimax pure-input profile uniformly in K. No promise about rank or purity is used by that family.

## 8. Implementation, literature boundary, and unresolved steps

The general mixed-state finite-block proofs give an explicit mathematical construction; a polynomial-size circuit for that full construction is not asserted in the original resource model. BCH gives polynomial-time Schur transforms with suitable working registers. Kirby--Strauch and modern algorithmic discussions explicitly retain ancillary registers; “efficient Schur transform” does not alone implement this paper's reversible packing and completion without a supplied pre-unitary ancilla. The separately proved pure-promise qubit implementation in ADDENDUM_PURE_CIRCUIT-v3.md now gives end-to-end accounting on the original 2k qubits, achieves the optimal integer Bell-pair target at every k, and has polynomial gate cost; it credits prior arbitrary-dimensional symmetric compression [CXXW]. It is a different pure-promise protocol, not a circuit implementation of the full all-state family. End-to-end efficient implementation of the full universal mixed-state construction remains unresolved. We do not infer it from basis computability or arbitrary partial-isometry extension.

Universal compression already identifies small representation spaces and symmetric-state compression; these are prior ideas [JHHH,PB,BE19]. Universal pure-state concentration [HM] operates under LOCC without the free global entangling unitary. The spectral Rains converse [R] and the maximally mixed quadratic converse [L] are prior principles. The classical Berry--Esseen theorem and source-coding Gaussian reduction are credited inputs, not new probability results.

The mathematical additions proved here are the all-finite-k coherent construction with empty blocks, its explicit dimension-dependent performance sandwich and triangular-array consequence, and the rank-budget minimax law with the exact support/average reciprocal-moment asymptotics and logarithmic universality correction. The bounded primary literature screen has not found the same combination of theorem and operation class. This is not exhaustive priority certification. In particular recent universal ordinary entanglement distillation and quantum coding papers must be compared by their free resources and quantifiers before journal submission.

## Primary references and read scope

[KW] M. Keyl and R. F. Werner, Estimating the spectrum of a density operator, Phys. Rev. A 64,052311 (2001), https://arxiv.org/abs/quant-ph/0102027. Existing repository proof read; primary paper representation inputs inherited with attribution.

[BCH] D. Bacon, I. L. Chuang, A. W. Harrow, The Quantum Schur Transform: I. Efficient Qudit Circuits, https://arxiv.org/abs/quant-ph/0601001. Primary abstract and algorithmic scope checked for this continuation; full resource-compatible circuit proof is not claimed.

[KS] W. M. Kirby and F. W. Strauch, A Practical Quantum Algorithm for the Schur Transform, https://arxiv.org/abs/1709.07119. Primary abstract and publication summary explicitly give ancillary-qubit counts.

[Krovi] H. Krovi, An efficient high dimensional quantum Schur transform, Quantum 3,122 (2019), https://quantum-journal.org/papers/q-2019-02-14-122/. Primary scope checked.

[CXXW] Z. Chen, C. Xiong, K. Khadiev and J. Wu, Efficient quantum compression for identically prepared states with arbitrary dimension, https://arxiv.org/html/2307.12024v2, revised 29 August 2026. Primary sections III--IV and the exact/approximate resource distinctions read; its arbitrary-D symmetric compression is the closest algorithmic predecessor, not a novelty claim here.

[BE] I. Shevtsova, On the absolute constants in the Berry--Esseen type inequalities for identically distributed summands, https://arxiv.org/abs/1111.6554. Primary abstract states a valid uniform constant smaller than 1; this standard probability theorem is an external input.

[JHHH] R. Jozsa et al., Universal Quantum Information Compression, Phys. Rev. Lett. 81,1714 (1998), https://arxiv.org/abs/quant-ph/9805017.

[HM] M. Hayashi and K. Matsumoto, Variable length universal entanglement concentration by local operations, https://arxiv.org/abs/quant-ph/0109028; and Universal distortion-free entanglement concentration, Phys. Rev. A 75,062338 (2007).

[R] E. M. Rains, A semidefinite program for distillable entanglement, IEEE Trans. Inf. Theory 47,2921 (2001), https://arxiv.org/abs/quant-ph/0008047. The effect bounds are reproved for the stated operation class in the predecessor.

[L] L. Lami, On PPT entanglement distillation, https://arxiv.org/abs/2610.12454. Credited predecessor converse, not a new input to the elementary finite-block effect argument.

[PB] M. Plesch and V. Buzek, Efficient compression of quantum information, Phys. Rev. A 81,032317 (2010), https://arxiv.org/abs/0907.1764v2. Primary full PDF sections I--IV and conclusions read in this continuation. It gives a unitary symmetric-qubit compression with quadratic elementary-gate cost; this prior mechanism is not claimed new.

[BE19] A. Baertschi and S. Eidenbenz, Deterministic Preparation of Dicke States, https://arxiv.org/abs/1904.07358. Primary abstract and introductory algorithm construction read; the no-ancilla symmetric compression is explicitly credited context, not an implementation premise in our general mixed-state theorem.

[TW99] C. A. Tracy and H. Widom, On the Distributions of the Lengths of the Longest Monotone Subsequences in Random Words, https://arxiv.org/abs/math/9904042v3. Primary full introduction and Theorem 1 read; its Gessel/RSK Toeplitz identity underlies (5.10).

[RLLLE26] J. Rizzo, L. Lami, J. Eisert and L. Leone, Universal quantum coding, https://arxiv.org/html/2609.38038v1. Primary abstract, introduction and initial main-results discussion read. It already proves universal local-Schur coding, finite-shot and second-order achievability, and rank-sensitive sample complexity under different free resources. Those achievements are not claimed as new here.

[MM26] S. Mandal et al., Efficient capacity-achieving entanglement generation with application to pure-loss Bosonic channels, https://arxiv.org/abs/2610.03674. Primary abstract checked as algorithmic context; no proof premise or comparison of full theorem scope is asserted.
