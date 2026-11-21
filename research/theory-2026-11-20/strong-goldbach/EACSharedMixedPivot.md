# A common prime in every mixed row: a bound independent of the number of rows

Use [the one-mixed-row theorem](EACOneMixedProjector.md) for terminology about EACs in [Bożek’s Goldbach factorization graph](https://arxiv.org/abs/1909.09900). Here there are arbitrarily many mixed rows. We impose a condition on their actual factorizations, not on the Goldbach exceptional set.

**Theorem.** Suppose the component has at least one mixed row, a prime t divides every mixed row, and there is a pure row N−u=t^β with u≤√N. Then for each ε>0 the even centers satisfying min C≥N^ε have a computable finite bound depending **only** on ε. In particular along an unbounded sequence of such components the minimum label is N^{o(1)}, with no advance bound on component size or on the number of mixed rows. The small shift u≤√N holds, for example, if u itself occurs as a pure-power base of another complementary row. We do not assert that every EAC admits a common prime, a pure occurrence of that prime, or a small shift for that occurrence. This result does not prove existence of a Goldbach representation.

There is also an unconditioned count for every EAC: with k labels, h mixed rows and all labels ≥N^ε,
    
    k ≤ 2h + π(⌊1/ε⌋).                                                (1)

Different pure rows have distinct output primes, since two distinct powers of the same prime cannot lie in [2N/3,N]. They give k−h *pure targets* (labels occurring as the base of a pure complement), all ≤√N. At least k−2h pure rows therefore have shifts/inputs which are themselves pure targets. The exponents of these pure rows are pairwise coprime: distinct powers sharing exponent divisor g≥2 differ by at least 2√(N−√N)>√N, larger than the difference of their shifts. Each exponent is at most 1/ε, and assigning any prime divisor to each gives the injection proving (1). In particular every directed path consisting of pure arrows before its first mixed source has length at most π(⌊1/ε⌋)+1: every pure source along the path except possibly its first is a pure target. A pure directed cycle is impossible in the presence of mixed rows, since it would be a proper factor-closed subset.

### The pivot arc and weights

The pivot's own row cannot be mixed, since t is coprime to N and would divide N−t. Follow the pure arrows from t up to and including their first mixed target, and name the arc in reverse order
    
    y₁^{a₁}=N−y₂, …, yₛ^{aₛ}=N−t ,

where y₁ is that mixed source and s≥1. All yᵢ are pure targets and ≤√N; so is t, by the hypothesis N−u=t^β. Thus the pure exponents a₁,…,aₛ,β are pairwise coprime by the small shifts, using the extra hypothesis u≤√N at β. Set L=∏_{i≤s}aᵢ and m=2L(1+β(s+1)). If M=max(2,⌈1/ε⌉), all exponents, total row multiplicities and β are at most M, s≤M+1, and L,m are bounded effectively in terms of M.

At t=0 the pivot annihilates the mixed complement of y₁, so y₁=n. On the arc the pure recursion yields F₀(n)=0, where B₁=n, Bᵢ₊₁=n−Bᵢ^{aᵢ}, and F₀=Bₛ₊₁. It is monic up to sign of degree L. For ν in the box 0≤νᵢ<aᵢ the L numbers β∑νᵢ/aᵢ are distinct modulo 1. As in the one-mixed theorem use monomials U=t^z∏ yᵢ^{νᵢ} having weight H=z+β∑νᵢ/aᵢ<m. Their number T satisfies T≥L(m−βs)>(L−1)m.

### Bounded-depth local reduction, without enumerating the entire component

We explain why no hidden dependence on the total number h of mixed rows survives. Treat n and t as indeterminates. For each graph label v needed in a calculation, compute a polynomial approximation Q(v,d) in ℤ[t,n]/(t^d) for d≤m, recursively. If d=0 return zero; if v is t return the indeterminate t modulo t^d. If a nonpivot v is a mixed source with N−v=t^b∏_{w≠t}w^{a_w}, compute
    
    Q(v,d) = n − t^b ∏_{w≠t}Q(w,d−1)^{a_w} mod t^d .
    
Here b≥1; the formula even works with a coarser one-order decrease when b>1. If v is a pure source with complement w^a, compute Q(v,d)=n−Q(w,d)^a mod t^d. Between successive order decreases there can be at most M+1 pure edges by (1)'s path argument; hitting the pivot stops a branch. Consequently these calls terminate, and their unfolding is a tree of depth at most (m+1)(M+2) and branching at most M. Repeated labels may be duplicated as tree nodes; one never needs a census of all labels or all mixed rows. Induction on the recursion shows v≡Q(v,d) modulo t^d at every actual tuple, and the same substitution is valid on formal solutions of the equations.

Because t's own row is pure with child yₛ, form
    
    G(t,n)=n−Q(yₛ,m)^{aₛ}−t mod t^m .

It vanishes mod t^m at the physical tuple. Its constant-t coefficient is precisely F₀(n), up to the harmless choice of sign just made. For every n^m U, substitute the Q(v,m) and reduce the resulting polynomial modulo t^m and G to Lm coordinates t^z n^l, z<m,l<L. A concrete procedure processes t-degrees z=0,…,m−1: divide the coefficient at z by the monic-up-to-sign F₀(n) and subtract the quotient times t^z G. This integral operation reduces the n-degree below L at this order and never changes earlier orders. No leading coefficient depending on t needs to be inverted.

The rank of the reduced columns is ≤(L−1)m. Indeed the full graph still has a formal origin x_v(n)=n+O(n²), by t-adic (with parameter n) contraction of x_v↦n minus its complementary monomial, whose degree is at least 2. The pivot coordinate has an integral inverse n=n(t)=t+O(t²). The just-defined substitutions and reductions preserve evaluation on it mod t^m, and n^m U evaluates to zero. As before the evaluation of all Lm output coordinates has rank m since it contains 1,t,…,t^{m−1}.

Rational elimination and denominator clearing give a nonzero integer polynomial P supported on the selected U and a bound A≥1 for its coefficients such that t^m divides n^m P at the physical tuple. Hence t^m divides P since gcd(t,N)=1. The weight-H value lies between (2/3)^{s+1}t^H and (3/2)^{s+1}t^H because yᵢ^{aᵢ}/t^β=(N−yᵢ₊₁)/(N−u) lies in [2/3,3/2], with yₛ₊₁=t. Weight separation by 1/L makes the highest term dominate the rest whereas the sum is <t^m, whenever t>(2TA(3/2)^{2(s+1)})^L. This contradiction bounds t and thus N≤(3/2)t^β.

Crucially this last bound can be taken **uniformly over every graph** at fixed M. The pivot arc, initial exponents and m have only finitely many choices, and the finitely many input Q(v,m) are determined by rooted expression trees of bounded depth and branching as above; all their exponent and pivot markers range over finite sets depending only on M. Enumerate these finite trees, the bounded arc choices and their finite integer reduction matrices. For every matrix having a nonzero integer kernel fix one vector via rational elimination; discard matrices without one since actual graphs meet the rank bound. The maximum of the resulting displayed thresholds is a computable function of M. This is a proof of an effective bound, not a practical proposed enumeration. No hidden bound on h is used.

For comparison, the coarser count k−2h without any lower bound on labels can be bounded by a direct application of a published result: the designated short-shift powers lie in [N−√N,N]. For sufficiently large N that interval is covered by two intervals of the form [Y,Y+√Y] with integer left endpoint, e.g. Y=floor(N−√N) and Y=floor(N−√N)+floor(√floor(N−√N)); the second begins no later than the end of the first. [Stewart, Acta Arith. 133 (2008), Theorem 2](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/aa133-2-01.pdf) with k=2 and θ=1/2 bounds each by exp(O(√(loglog N·logloglog N))) perfect powers. This is an application of Stewart, not a new general short-interval estimate, and not required for the projector.

The related [Kelanemer 2026 record](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) discusses structural invariants under a global counterexample assumption. The present condition is local and its height bound follows from finite-depth reduction at a specific common prime. The full latest text of that record was not accessible here, so no priority claim is made.
