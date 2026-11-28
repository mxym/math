# Product interpolation for repeated components

## 1. Inputs, parameter, and theorem

Fix integers k>=2 and A>=1. The only numerical inputs are odd N>=3 and T=phi(N), with at most k distinct prime divisors and largest/smallest prime ratio at most A. On its support S put p -> q when p divides q-1. A component means a weak component of this directed graph, and multiplicity means v_p(N). Write P=min S and L=bitlength(N).

In the large-prime case described below, suppose there are t components, all copies of one rooted out-tree. This is a promise about the actual graph, not an arbitrary selection of some edges. Corresponding edges across the copies satisfy the same integer relation q=m p+1; corresponding node types carry the same positive multiplicity e_v across copies. All these choices are unknown and will be enumerated. The roots are distinct primes x_1,...,x_t. For one template, its node forms l_v(z)=a_v z+b_v start with z and are built by composing the edge maps. Define a sample point xi_v=-b_v/a_v for each node type. Partition these points into groups indexed by the type's valuation profile rho_v=(e_v-1+outdegree(v))/e_v. Thus profiles may merge several distinct sample points.

Section 4 gives an explicitly computable integer s_* from this ordered grouped point set. **Theorem:** on the stated fixed k,A promise, if the true repeated template satisfies s_*>=t-1, the complete prime factorization with multiplicities of N can be determined deterministically in bit time polynomial in L. It suffices in particular that the closed convex hulls of t-1 groups are pairwise disjoint. Neither passing the test nor any graph structure is needed to trust a returned factorization; the algorithm verifies it directly. Nothing here computes T from N.

Trial-divide by primes through A. If a factor is found then all primes are <=A^2, so on the promise complete trial division through this constant suffices; no division of a guessed totient is involved. Otherwise P>A. A q-1 contains at most one prime factor of N counted with multiplicity, because q-1<AP<P^2. Edges strictly increase the prime, and an undirected cycle would give two parents to its largest vertex. The graph is indeed a forest, each tree with its unique indegree-zero root. Each edge multiplier is <=A and contains no support prime.

## 2. Root anchor and exact products

Let g=gcd(N,T), D=N/g and U=T/g. For any p|N, f_p=v_p(T)=e_p-1+d_p where d_p is its outdegree, since each child contributes just one p to the product of shifted distinct primes. Thus D is the squarefree product of the leaves and v_p(U)=max(d_p-1,0). Define
```
Y = U/gcd(U,N^L mod U).
```
Use gcd(U,0)=U if U divides N^L (in particular U=1 creates no ambiguity). Since U<=T<N, saturation removes the entire U-part supported on S. It does **not** remove any prime outside S.

More explicitly, start with U=D phi(rad N)/rad N. Each nonroot q contributes q-1=m p from its parent edge in the numerator. Multiplying by D/rad N cancels one copy of each nonleaf. Hence with C=(product of edge multipliers m in a **single** template)^t,
```
U = C product_i(x_i-1) product_(nonleaves p) p^(d_p-1).
```
Here C uses edge multipliers, not the generally different accumulated slopes a_v. Each root shift x_i-1 is coprime to N (otherwise it has a parent in the actual graph), and all edge multipliers are smaller than P. Therefore Y=C product_i(x_i-1), retaining shared outside primes of C and the shifted roots with full multiplicity. For F(z)=product_i(z-x_i), this supplies
```
(-1)^t F(1)=Y/C.
```
A guessed C not dividing Y is discarded.

For completeness, the numeric block N_rho of all N-prime powers whose p has f_p/e_p=rho is available without factoring. Enumerate reduced fractions b/a=(e-1+d)/e, 1<=e<=L and 0<=d<k. Set J=gcd(N^b,T^a), W=(N^b/J)(T^a/J), and N_rho=N/gcd(N,W^L mod N). This keeps precisely the full prime powers with b e_p=a f_p. The zero profile has b=0,a=1,J=1,W=T. Retain the nonunit blocks. These are classical proportional-valuation classes; the use made of them below is the point here.

Since l_v(x_i)>0 and a_v>0,
```
P_v(F) := (-1)^t a_v^t F(xi_v) = product_i l_v(x_i) > 0.
```
The numeric datum furnished by a profile j is exactly
```
product_(v in group j) P_v(F)^e_v = N_j.                                (1)
```
The separate individual values inside a nonsingleton group are not assumed known. If two distinct node types had equal xi, their affine forms would be proportional. In one true component the actual two distinct prime values p_v,p_w would then satisfy a_w p_v=a_v p_w, forcing p_v | a_v. But p_v=a_v x_i+b_v> a_v. This is impossible. Thus the sample points are distinct rationals, all <=0 (the root type gives 0). Discard duplicates in an invalid template by rejecting that template, not by asserting an extra evaluation.

## 3. Why equal positive products constrain signs

Take two real monic degree-t polynomials F,G satisfying (1), the same anchor at 1, and (-1)^t F(xi_v)>0, (-1)^t G(xi_v)>0 on all samples. No prior real-root factorization of F or G is needed for this uniqueness argument. If their difference is not zero, then F-G=(z-1)Q for a nonzero real polynomial Q of degree <=t-2. For t=1 the anchor already determines the monic polynomial.

For any profile group the values of Q on its samples must be all zero or include at least one positive and one negative. Indeed z-1 has constant negative sign on the sample points, and the scalar (-1)^t a_v^t has the same sign for every node type. If all the differences P_v(F)-P_v(G) in a group were weakly nonnegative with one strictly positive, its positive product with positive integer weights e_v would strictly increase; weakly nonpositive with a strict decrease is likewise impossible. This proves the sign restriction, including samples where the two polynomials agree and groups of mixed weights.

A useful sufficient test follows already: on the closed convex hull of every group, Q has a real zero by the intermediate value theorem (or it vanishes at all group nodes). With t-1 pairwise disjoint such hulls, a nonzero Q of degree <=t-2 is impossible. In that simpler case one may equivalently count zeros of F-G on the hulls and the separate anchor 1. Mere pairwise nonidentity of hulls is not a separation condition; the disjointness here is strict as sets.

## 4. Computable sign-degree certificate

Write the sample locations in strictly increasing order xi_1,...,xi_s; s<=k. Enumerate all words sigma in {-1,0,+1}^s satisfying the group restriction in section 3 (all zero or both signs in each group). Let Z be the indices assigned zero. For each i not in Z define tau_i=sigma_i (-1)^(number of j in Z with j>i). Set
```
d(sigma)= |Z| + number of sign changes in the sequence (tau_i)_(i not in Z).
```
The variation of an empty or one-letter sequence is zero. Define s_* as the minimum d(sigma) among these admissible words, including the all-zero word.

This integer is precisely the least degree a nonzero real polynomial can have while obeying the *sign restrictions* alone. Necessity: a polynomial with the word sigma is divisible by product_(j in Z)(z-xi_j); its quotient has the prescribed signs tau_i at all the other samples. Each successive change of nonzero sign requires a distinct real zero in the corresponding disjoint open gap. Sufficiency for the word: take the specified simple zeros and, for each change of tau, insert one root strictly between that pair of consecutive nonzero samples, avoiding all sample nodes if desired. Multiply by a constant sign to agree at the first nonzero sample. This polynomial realizes the word. If every sample is zero, the product of all distinct linear factors has the required degree s. This exact minimum is for the sign test, not a claim that failed certificates imply nonuniqueness for the original integer problem.

When s_*>=t-1, the hypothetical Q cannot exist. Thus, for each qualifying fixed template, **at most one** monic real F satisfies the positive product equations and anchor. The certificate itself is combinatorial once the rational nodes and profile labels are known. At most 3^k words are considered.

## 5. Deterministic bit computation

Enumerate t and a labelled rooted template of size s with ts<=k, edge slopes 1,...,A and each type multiplicity 1,...,L. This costs O_{k,A}(L^k). Build a_v,b_v (bounded for fixed parameters by (A+1)^(k+1)), reject repeated samples, mismatched present profile sets, C not dividing Y, or failing certificate. The definitions cover t=1 and a one-vertex template without changing the arithmetic.

Use free real coefficients c_0,...,c_(t-1) for the monic F=z^t+sum c_h z^h. Each P_v(F) is an integer affine form in these coefficients: a_v^t clears all denominators in F(-b_v/a_v). The anchor is linear. Equations (1) are polynomials of total degree O_k(L); their coefficients have polynomial bit length, by expanding products of integer affine forms with bounded coefficients in fixed dimension and adjoining the O(L)-bit constants. Impose P_v(F)>0 for all v. The admissible real coefficient system has at most one solution per retained guess by section 4. Real feasibility in fixed dimension (Renegar) is deterministic and polynomial in this representation.

An actual F has integer coefficients with absolute values <=2^k N^k since each root is <=N. Search that integer coefficient box by testing the real feasibility system on its integer-endpoint subboxes. Bisect [l,h] into [l,m] and [m+1,h] with m=floor((l+h)/2); the skipped gap contains no integer. At most one child at each level can be feasible. After O_k(log N) levels output the singleton integer tuple if it satisfies the equations and inequalities; otherwise discard. Wrong templates with a nonintegral or no solution cannot create an exponential search. List all integer roots of the resulting univariate F in [2,N] by exact root isolation or the same feasibility/bisection using its at most t real roots. Use only candidates with t distinct prime roots, all template evaluations distinct positive primes, and the specified powers reconstructing both N and T exactly. An invalid template cannot cause an incorrect factorization; the true template succeeds. All gcds, primality checks and integer arithmetic take polynomial bit time. No factorization of the totient and no additional oracle call or unknown constants of the particular input are used.

## 6. Three illustrative regimes, and scope

1. **Four trees, separate values.** Roots 1013,1103,1451,1481; each root p has two leaves 2p+1 and 6p+1, with type exponents (root, first leaf, second leaf)=(1,2,3). The three singleton profile samples are 0,-1/2,-1/6. Together with 1 they fix the monic quartic by ordinary interpolation. Here Y=49,626,861,318,144,000 and C=12^4=20,736. The recovered F is z^4-5048z^3+9470382z^2-7823175944z+2401084414609.

2. **Four trees, an actual product of values.** Roots 13883,14153,14303,15791, with leaves 2p+1,6p+1,12p+1 and type exponents (1,2,2,3) including the root. Now -1/2,-1/6 belong to a common profile, so their separate evaluations are not given. Its nondegenerate hull and the two singleton hulls at -1/12 and 0 are disjoint. There are sixteen distinct primes, max/min<14, and exactly the twelve intended edges.

3. **Five trees, contact pattern beyond separated hulls.** Roots 382069,421831,941249,1221113,1606859. Each root has the six leaves m p+1 for m=210,420,630,840,1050,1260, in that order, with leaf exponents 2,3,3,4,4,2 and root exponent 1. The increasing sample points have grouped pattern A,B,B,C,C,A,R; R is the root singleton. At most three group hulls are pairwise disjoint, short of t-1=4. Among the 27 admissible words, the minimum d is 4 (counts by d=4,5,6,7 are respectively 10,2,14,1). Thus the sign certificate passes. Exact trial division confirms all 35 node values prime; the full directed edge check gives exactly the 30 named edges and largest/smallest ratio <5300. The checker uses these fixed roots directly; it needs no search for examples.

These repeated-type valuation matrices have identical columns and rank one. In particular the four- and five-tree examples are not instances of the rank-at-least-t-1 criterion, the at-most-three-component theorem, or the monochromatic-leaf collision theorem (the stars have different multiplicities on their leaves). This comparison does not rule out all other methods on individual examples. Each is a finite mathematical witness; no assertion of an infinite family of simultaneous primes or a general oracle-free factoring result is made.
