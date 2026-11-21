# No reciprocal component with at most five prime factors per row

In a nontrivial [Bożek exceptional autonomous component](https://arxiv.org/abs/1909.09900), call the support reciprocal if every prime divisor q of N−p in the component also has p dividing N−q. Multiplicities on opposite arcs need not agree. **At every even center N, for every such reciprocal EAC, at least one row has Ω(N−p)≥6**, where prime factors are counted with multiplicity. No restriction on the number or size of labels is assumed. More locally, in a reciprocal EAC the maximum label M and its unique neighbor q cannot BOTH have row multiplicity ≤5. The known reciprocal two-label example at 2200 has multiplicities 3 and 7 and is not excluded. No inference about general nonreciprocal components or existence of Goldbach partitions follows.

### Tree geometry and the maximum

At every vertex p all neighbor primes in a reciprocal component have the same residue N mod p: p divides each neighbor's complementary row. Thus any two distinct neighbors differ by a nonzero even multiple of p, of magnitude ≥2p. In particular p has at most one smaller neighbor. A cycle of distinct vertices in the underlying undirected graph is impossible, since its largest vertex would have two smaller neighbors. Strong connectivity and absence of self-loops therefore make the support a tree. With the smallest vertex as root, all edges on each path from it are strictly increasing: after a smaller neighbor there cannot be a second smaller one. Consecutive labels u<p<r there satisfy r=u+2hp with a positive integer h. A vertex may have several larger children, but no two leaf children can have the same parent p: the two complementary rows would be distinct powers of p inside [2N/3,N]. We will only need local consequences at M and q.

Write d_p=Ω(N−p). At p the product of its neighbor labels with multiplicities gives N−p, all factors congruent to N mod p, so N^{d_p−1}≡1 mod p since gcd(N,p)=1. If d_p=2 or 3, that common residue is ±1, neither of which can be represented by an odd prime <p (p−1 is even and 1 is not prime). Hence at the largest label, with its one neighbor q<M, we have N=M+q^a, a=d_M≥4. We now suppose a,d_q≤5. M divides N−q, hence divides q^{a−1}−1. Let d=d_q and observe that ALL d factors of N−q are congruent to M mod q, with M^{d−1}≡1 mod q. Distinct primes satisfy M≥q+2.

### Three reciprocal quadratic invariants

We record short positive-integer Vieta descents to avoid assuming primality of a cofactor W. For σ,τ∈{0,1}, the conditions
     
    W | q²+σq+1,     q | W²+τW+1

imply gcd(q,W)=1 and the positive invariant
     
    K=(q²+W²+σq+τW+1)/(qW) ∈ ℤ .

Switching q to q′=(W²+τW+1)/q or W to W′=(q²+σq+1)/W preserves the invariant and the two congruences: it is the other root of the respective monic quadratic. If the larger variable q exceeds W>1, then q′<W. For τ=0 use q≥W+1; for τ=1 equality q=W+1 is impossible since q would divide 1, and q≥W+2 suffices. The same argument works for W>q>1. Equal variables are possible only at 1. Descent ends with one variable 1; the other must divide 2+σ if q=1, or 2+τ if W=1. Substitution at these possible divisors yields
     
    (σ,τ)=(1,1): K=5;   (0,1): K=4;   (0,0): K=3.

The first of these classical identities is [Bibby–Vyncke–Zelinsky, Lemma 5](https://math.colgate.edu/~integers/v115/v115.pdf); compare also [Cosgrave–Dilcher](https://www.mathstat.dal.ca/FQ/Papers1/51-2/CosgraveDilcher-1.pdf) on reciprocal quadratic prime congruences. The claim here is the indicated use of the complement factorizations, not priority for these Vieta invariants.

### Case a=4

Here M divides q²+q+1 since M>q and M | q³−1. Put W=(q²+q+1)/M. Then W is odd, 1≤W<q (M≥q+2), and MW≡1 mod q. Removing one occurrence of M from N−q leaves
     
    v=1+q(q−1)W .

The order of M modulo q divides d−1≤4, so is 1,2,3 or 4.

* Order 1 gives W=1, M=q²+q+1, v=q²−q+1. Every factor of v is an odd prime ≡1 mod q, hence ≥2q+1. Two such factors are too large, so v must itself be prime. For q≠3 one of q²+q+1 or q²−q+1 is divisible by 3 and exceeds 3. At q=3 we have M=13,N=94; the forced label 7 has N−7=3·29 with 29>M. Order 2 is impossible because W=q−1 would be even.
* Order 3 forces d=4 and q|W²+W+1. Here W>1, and the (1,1) invariant gives q+q′=5W−1 with q′<W, hence q≥4W and q≥13. The least positive residue of M modulo q is r=q−1−W, because W^{-1}≡−1−W. The three factors of v are each ≥r. But r≥3q/4−1≥(2/3)q for q≥13, while v≤1+q³/4 < (8/27)q³ ≤ r³. This is impossible.
* Order 4 forces d=5 and q|W²+1. The least positive residue of M is q−W, which is even, so each odd prime factor of N−q exceeds q. Their product exceeds q⁵, whereas N−q=q⁴+M−q≤q⁴+q²+1<q⁵.

### Case a=5

Here M divides q²+1 since neither q−1 nor q+1 has a prime divisor >q. Put W=(q²+1)/M, **even** and less than q. Then MW≡1 mod q and removing one M leaves
     
    v=1+q(q²−1)W .

Order 1 is impossible (W=1). Order 2 would give W=q−1 dividing q²+1, so q−1 divides 2 and q=3. Then M=5,N=248 and N−3=5·7² violates maximality.

* Order 3 forces d=4, q|W²+W+1. The (0,1) invariant gives q+q′=4W with q′>0. In particular q<4W and M=(q²+1)/W≤4(q²+1)/(q+1)<4q. Since N−q=q⁵+M−q>q⁵ and its four factors are ≤M, q<4⁴=256. Complete ordinary trial division on 3≤q<256, retaining odd primes q and prime M>q dividing q²+1 with exact order 3 modulo q, gives only (37,137). Its row N−q=23·59·137·373 violates maximality. The accompanying short checker verifies the full finite enumeration, not a heuristic cutoff.
* Order 4 forces d=5 and q|W²+1. The (0,0) invariant gives q+q′=3W, q′=(W²+1)/q<W. Hence q>2W and (since W≥2 and q≥2W+1) q′≤W/2: (W²+1)/(2W+1)≤W/2. Thus (5/2)W≤q<3W. The least positive residue r=q−W is odd, and 3q/5≤r<2q/3. All four prime factors of v are odd and congruent to r mod q, so their product is either r⁴ or at least (r+2q)r³. Neither is possible. In fact
     
       r⁴ < (16/81)q⁴ < (1−1/q²)q⁴/3 < v ,
       (r+2q)r³ ≥ (351/625)q⁴ > 1+(2/5)q⁴ > v .
     
   These inequalities hold already for q≥3. They use W>q/3 in the first line and W≤2q/5 in the second.

Both possible exponents at M have been eliminated under the stated local degree assumptions, proving the theorem. The proof used global factor-closure only at the explicit small contradictions, and only reciprocal congruences in the remaining local calculations.

For the related Goldbach graph literature, [Kelanemer’s 2026 terminal-component record](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) uses global counterexample hypotheses and low-dimensional exponent matrices. Its full latest text was not accessible for this comparison. The exclusion here uses reciprocal support and bounds on just two neighboring rows, with no restriction on dimension and no assumption that the center is unrepresented. The [exact checker](check_eac_reciprocal_five.py) confirms only the one small enumeration used in the proof.
