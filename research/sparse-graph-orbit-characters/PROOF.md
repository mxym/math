# Sparse character cancellation on a graph orbit

## 1. Setup and the two readings

Write E for the set of M=binom(n,2) unordered pairs on [n] and V=F₂^E. Addition is symmetric difference of edge sets, and the inner product is mod two. Vertex permutations act on V by relabeling endpoints. For H,α in V, put

    B_H(α) = (1/n!) Σ_(π in S_n) (-1)^<πH+H,α> .

This is the source's character sum divided by n!. Let 1 denote the full edge set. Every π preserves total edge parity, so B_H(0)=B_H(1)=1 and
B_H(α+1)=B_H(α) for every α,H. In particular the AICR c/0084 reading with maximum over every nonzero α is false for every H when n≥2. The original ePrint's Eq. (3) and preceding setup restrict α to at most D edges. We do not use the full-edge example against that sparse reading. Theorem 1 proves cancellation simultaneously over its nonzero frequencies (and, for the bare character sum, their complements).

## 2. Uniform sparse bound

**Theorem 1.** Suppose n≥2, H is uniform in V, 1≤D≤M is an integer and 0<η<1. With probability at least 1−η over H,

    max_{α: 1 ≤ min(|α|, M−|α|) ≤ D} |B_H(α)|
      ≤ min(1, sqrt((2D/M) [ D ln(2eD) + ln(2D/η) ])).           (1)

If the index set is empty, the assertion means all of its members satisfy (1), vacuously. The same bound, without using complements, holds for every α with 1≤|α|≤D, with the invariant full set allowed when D=M (then the bound is 1). If η=n^(−A) for any fixed A>0 and D=o(n/√ln n), the right side tends to zero. For D=ceil((ln n)^2) it is O_A((ln n)^2 √ln ln n / n).

**Proof.** Set ξ_e=(-1)^(H_e), independent fair signs. For α nonempty with w=|α|, let O be its orbit as a set of distinct edge sets, and L=|O|. A uniform π sends α to a uniform member of O (equal fibers by orbit–stabilizer). With χ_α(H)=∏_(e∈α)ξ_e,

    B_H(α) = χ_α(H) F_O(H),
    F_O(H) = (1/L) Σ_(β∈O) X_β,   X_β=∏_(e∈β)ξ_e.              (2)

Each X_β alone is a fair sign; they are not in general jointly independent. Every edge belongs to the same number r of the β by transitivity on pairs. Counting the Lw incidences gives r=Lw/M, a positive integer.

For completeness the needed product form of Hölder on a product space is as follows. If independent variables feed functions g_j≥0, with any variable used by at most r functions, then

    E ∏_j g_j^(1/r)  ≤  ∏_j (E g_j)^(1/r).

To prove it, integrate one variable first. For the factors depending on it, apply Hölder with exponent r for each and, if fewer than r factors occur, an extra constant factor 1 with the remaining reciprocal exponent. This replaces each such g_j by its expectation over that variable, and the upper bound still has the product of 1/r powers. The remaining dependence sets have not grown. Induct on the number of variables, using independence to do each partial integration.

Apply this to g_β=exp(λr X_β/L) for any real λ. Fairness gives E g_β=cosh(λr/L). Thus

    ln E exp(λ F_O) ≤ (L/r) ln cosh(λr/L) ≤ λ² w/(2M).

The scalar inequality follows by integrating tanh u ≤ u for u≥0 and using evenness. Exponential Markov with λ=Mt/w for the upper tail, and the negative sign for the lower tail, gives

    Pr_H[|F_O(H)| ≥ t] ≤ 2 exp(−Mt²/(2w))      (t>0).            (3)

By (2), absolute values are identical for all α in O; the signed B_H need not be constant on O. A graph with w edges has at most 2w nonisolated vertices, so the number of weight-w orbits on n vertices is at most the number of edge sets of size w on 2w vertices: remove all isolates, label the nonisolated vertices, then pad with isolates up to 2w even if 2w>n. The original orbit is determined by the resulting isomorphism type because n is fixed. The binomial bound gives at most binom(binom(2w,2),w) ≤ (e(2w−1))^w ≤ (2ew)^w possibilities. Summing w=1,…,D gives at most D(2eD)^D orbits. Equation (3) and a union bound give (1) on the weight-at-most-D range; the identity B_H(α+1)=B_H(α) then gives the claimed complement range. For D=M the displayed uncapped threshold exceeds 1, consistently with the full-set case. The asymptotics follow from M=n(n−1)/2 and, when η=n^(−A), D ln D + ln(D/η)=O_A(D ln D+ln n) for D≥1. 

As an order check, for w=1, |B_H(α)| is the absolute average of all M independent signs. Its second moment is 1/M and its fourth moment is (3M²−2M)/M⁴≤3/M². With Y the square of this average, split E Y at Y≥1/(2M) and apply Cauchy–Schwarz to that event to get Pr[Y≥1/(2M)]≥1/12. Thus a typical uniform bound cannot be o(1/n) even at D=1; we make no claim that (1) is sharp in D.

## 3. Exact orbit identities

These identities are not needed for the probability bound. For every nonempty α (including the full edge set), distinct Walsh monomials are orthogonal under uniform H. It follows from (2) that

    E_H F_O = 0,   E_H B_H(α) = 1/L,   E_H |B_H(α)|² = 1/L.

The mean of B_H is not generally zero because of the extra χ_α factor. For every H, summing over a whole orbit gives

    Σ_(α∈O) B_H(α) = L F_O(H)².

In particular, for any family of whole orbits and weights constant on each orbit, its weighted sum of B_H is the same weighted sum of L F_O², with expectation equal to the sum of the weights over the orbits. No claim about other factors in the source's Eq. (3) is needed.

## 4. Exact maximal frequencies

**Theorem 2.** Let n≥4. For u in F₂^n define the cut δu by (δu)_ij=u_i+u_j, and let d(H) be the vector of vertex-degree parities. Set C={δu+c1 : u in F₂^n, c in F₂}. The set of α with |B_H(α)|=1 is, exactly,

    H∈{0,1}:                         all α in V;
    H∈C but not in {0,1}:            all α with d(α) constant;
    H∉C and d(H) constant:           C;
    H∉C and d(H) nonconstant:        {0,1}.                       (4)

All attained unit values are +1. Consequently, for uniform H, the probability of at least one nontrivial maximal frequency (some α outside {0,1}) is

    n even:   2^(−(n−2)),
    n odd:    2^(−(n−1)) + (2^n−2) · 2^(−M).                     (5)

In particular, with high probability {0,1} are the only characters of magnitude one. This is not an assertion that the others are uniformly o(1).

**Proof.** Let W_H be the binary span of πH+H over all π. It is permutation-invariant since σ(πH+H)=(σπH+H)+(σH+H). The identity term of the character sum is +1, so magnitude one is exactly B_H(α)=1 and is equivalent to α∈W_H^⊥. Total edge parity already puts 1 in this orthogonal complement.

The orthogonal complement of the span of all 4-cycles is C. Indeed, every cut meets a cycle in an even number of edges and a 4-cycle has even length. For the reverse, suppose α is orthogonal to every 4-cycle. Fix a vertex z and put t_ij=α_ij+α_iz+α_jz for distinct i,j≠z. Applying the condition to the four edges between {i,z} and {j,k} gives t_ij=t_ik for all distinct i,j,k different from z. Since n−1≥3 and the edges of the complete graph on [n] without z are connected under sharing an endpoint, all t_ij equal a common c. Set u_z=0 and u_i=α_iz+c for i≠z. Then α=δu+c1.

If H∉C, there is a 4-cycle between {a,b} and {c,d} with odd intersection with H. Let τ=(a b), σ=(c d). Then (I+σ)(I+τ)H is precisely that 4-cycle: any edge missing one of the two vertex pairs is canceled by the corresponding swap, and at each crossing edge the coefficient is the parity of the four crossing edges in H. This vector lies in W_H by invariance, so W_H contains its entire permutation orbit and the span of all 4-cycles. Hence only α in C can be maximal.

For α=δu+c1 the inner product with any orbit difference is u·(π d(H)+d(H)), using δ transpose equal to the map d and cancellation of total edge parity. If d(H) is constant, this vanishes for all u. Otherwise the span of π d(H)+d(H) is all even-parity vertex vectors: every difference has even parity; swapping a zero and a one produces a vector with ones on any chosen pair up to permutation; these span that space. The orthogonal complement in vertex space is the constant vectors, where δu=0. This proves both H∉C cases.

If H=δv+c1, all differences are δ(πv+v). If v is constant then H is either 0 or 1 and every frequency is maximal. If v is nonconstant, the same swap argument shows that W_H is the image under δ of the whole even-parity vertex space. Its orthogonal complement consists exactly of those α whose d(α) is constant. This proves (4).

For (5), d sends one edge {i,j} to the vertex vector with ones at i,j, so it maps onto the even-parity vertex space and d(H) is uniform there. The constant word 0 always lies in that space, and the all-one word lies in it exactly for even n. Also |C|=2^n: δ has kernel the constant vectors, and 1 is not a cut since its sum on a triangle is odd. In C one has

    d(δv+c1)_i = (n mod 2) v_i + (Σ_j v_j) + c((n−1) mod 2).

When n is even all members of C have constant d; for odd n only 0 and 1 do. The event that one of the first three cases of (4) occurs is the union of H∈C and d(H) constant. In all three cases there is a maximal frequency outside {0,1} (for the second case the kernel of d has dimension M−n+1≥3; for the third, |C|=2^n). Counting the union proves (5).

The statements only concern this finite Fourier statistic. Neither (1) nor (4) implies a result for a planted-graph problem, its low-degree normalization, or a cryptographic protocol.
