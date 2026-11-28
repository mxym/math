# Terminal exponent classes and up to two collisions

## 1. Promise and exact inputs

Fix an integer k>=4 and an integer A>=1. Let N>=3 be odd, with unknown set S of at most k distinct prime divisors, unknown exponents e_p>=1, and max S <= A min S. The ordinary binary integers N and T=phi(N) are the only numerical inputs. Draw a directed edge p -> q on S precisely when p divides q-1. A leaf means a vertex of outdegree zero, including any isolated vertex; component always means weak component. Suppose:

1. Within each component, all its leaves have the same multiplicity in N. Label the component by that multiplicity.
2. Each label belongs to at most two components, and at most two labels belong to two. Call each such shared label a *collision*.
3. If there are two collisions, at least one of those four components is nontrivial (has an edge). No edge is required if there are zero or one collisions. An edge only in a component with an unshared label does not qualify in the two-collision case.

**Theorem.** The complete factorization with multiplicities of N is obtainable deterministically in time polynomial in L=bitlength(N), with constants depending only on k,A. There is no hypothesis on additive widths; exponents of nonleaves are unrestricted and unrelated to component labels. The graph, component labels and all primes are unknown. There is no further totient query or factored-totient input.

Write P=min S and H0=2(k+1)(A+1)^2, P0=H0^(k+1). These are proof constants apart from the unknown P. Trial-divide by primes through fixed P0. If any is found, all primes of N are <=A P0 on the bounded-ratio promise; finish by trial division there. We may now suppose P>P0. An edge always increases the prime. Two parents of q have product at least P^2 but dividing q-1<A P. Thus each vertex has at most one parent. An undirected cycle is impossible since its greatest vertex would have two parents. Each component is a tree with a unique indegree-zero root; the statement includes singletons.

## 2. Reading all leaf-level products

Let R=rad N, and H be the nonleaves. The classical equality T/N=phi(R)/R shows gcd(R,phi(R)) is the product of H. Thus g=gcd(N,T), D=N/g, U=T/g give D precisely the product of leaves, each once. V=N/gcd(N,D^L mod N) contains the full prime powers of nonleaves, since v_p(N)<=L. Define
```
G_0=1,     G_j=gcd(N,D^j mod N) for 1<=j<=L+1,
H_j=G_j/G_(j-1)                 for 1<=j<=L+1,
d_j=H_j/H_(j+1)                 for 1<=j<=L.
```
Indeed, v_p(G_j)=min(j,e_p) for leaves and zero otherwise. H_j is the squarefree product of leaves of multiplicity >=j; H_(L+1)=1; d_j is the exact product of those of multiplicity j. In particular the nonunit d_j are pairwise coprime and their product is D. Only polynomial-bit modular powers, gcds and exact divisions were used. The list J={j:d_j>1} is now known, not guessed.

Enumerate r<=k and labelled rooted forests on r vertices. For each forest enumerate slopes a=1,...,A on edges, and map its components onto J as in the promise, trying all eligible assignments of labels and both pairings/orders. Each leaf of a guessed component carries that component's label; enumerate e_p=1,...,L on each nonleaf. There are O_{k,A}(L^k) total possibilities: <=2^(k(k-1)) labelled graph choices, <=A^(k-1) slope choices per graph, <=k^k label functions (reject |J|>k), and <=L^k multiplicity choices. The numeric labels are just the indices already computed. No guessed pairing or label function is presumed correct.

## 3. Exact equations and peeling the unshared labels

Root x_i of component i determines each node by l_v(x_i)=c_v x_i+d_v, starting with x_i and composing edge maps z -> a z+1. Thus c_v>=1,d_v>=0, d_v>0 for nonroots. For true primes c_v<=A and d_v<=kA by comparability and the sum-of-suffix-products formula. Discard guesses violating these bounds. Let t_v be outdegree. Set
```
D_i = product of l_v over leaves in i,
V_i = product of l_v^e_v over nonleaves in i,
B_i = (x_i-1) times the product of l_v^(t_v-1) over nonleaves in i,
C   = product of all edge slopes.
```
Every guessed true root tuple satisfies
```
product_(i labelled j) D_i(x_i) = d_j  for every used j;
product_i V_i(x_i) = V;                    product_i B_i(x_i) = U/C.    (1)
```
For the last equality, phi(R)=product_v(p_v-1); a nonroot gives its incoming slope times its parent. Multiplication by D/R cancels one copy of every nonleaf. Thus root shifts and the excess outdegrees account for all factors. Discard C not dividing U.

Each D_i is nonconstant with D_i(1)>0. Each B_i is nonconstant and B_i(1)=0. All V_i(1)>0. For a nontrivial tree V_i(0)=0, V_i is nonconstant and D_i(0)>0. For an isolated vertex (D_i,V_i,B_i)=(x_i,1,x_i-1). We may test gcd(D_i,V_i)=1 over Q[x] and discard failures. The true guess passes: two node forms sharing a zero have proportional coefficients, giving c_w p_v=c_v p_w for distinct primes in the same tree; p_v would divide c_v<=A<P. All zeros of any D_i or nonconstant V_i lie in |z|<=kA, being roots of these affine forms. At any such z and at z=1 every node form has absolute value <=H0.

For each unshared j there is just one equation D_i(x_i)=d_j. The polynomial D_i is strictly increasing on x_i>=2, so a binary search on *integers* [2,N] finds at most one possible coordinate. Evaluate all its node forms immediately. Require positive distinct primes, exact divisibility in N with the guessed true valuations on nonleaves and valuation j on every leaf, and disjointness among all trees being peeled. For each candidate node q require gcd(N,q-1)=1 if called a root and exactly its proposed parent p otherwise. Indeed q-1<A P<P^2 after the small-prime fallback, so its gcd with N can contain at most one prime of N and that prime only to the first power. Thus this test certifies every actual incoming edge, including that the proposed root has no parent. It does not infer absence of children from a failed search.

Here is why these checks certify a whole component on the promised inputs, even if the guessing branch is wrong. The checked nodes form a connected true subtree. Since its prime leaves have product d_j, they are all true leaves (d_j is supported only on true leaves), of multiplicity j, and include every true leaf of multiplicity j in the entire graph. The actual component containing any one of these leaves is monochromatic at its leaves by hypothesis, so *all* leaves of that component are in the proposed subtree. Its actual root and the incoming path to every candidate leaf are correct by the gcd tests. Every vertex of a finite out-tree lies on a root-to-leaf path. Thus the proposed subtree misses neither a root ancestor nor a side branch. In particular, if the actual label j spans two components, a falsely proposed singleton cannot pass. No true singleton is discarded.

Remove only certified whole components. From their verified prime powers form the actual remaining integer N' by dividing N, and T' by dividing T by the known product of p^(e_p-1)(p-1); reject a nonexact division. These are coprime component removals, hence T'=phi(N') on the true input. With certain known factors saved, stop if N'=1. Otherwise recompute, from N',T', the reduced denominator, numerator, full nonleaf part and all exact leaf levels by section 2. There were no edges between the removed and remaining actual components. Require the surviving level indices to be precisely the candidate's shared labels; use their freshly computed products. For the remaining forest compute its C' (only remaining slopes), and let v be its freshly computed full nonleaf part and b its reduced numerator divided exactly by C'; reject if not a positive integer. In particular no numerical inequality below relies on a quotient by unknown complex roots. The controls also suffice on incorrect residual guesses: the explicit bound filters in section 5 are mandatory before finite-fiber reasoning.

## 4. Zero or one collision

No collision leaves no unknowns; verify the full answer as in section 6. One collision leaves two trees with equations D_1(X)D_2(Y)=d, V_1(X)V_2(Y)=v, B_1(X)B_2(Y)=b for nonzero constants. Two isolated trees give XY=d and (X-1)(Y-1)=b, hence X+Y=d+1-b. If only tree 1 is nontrivial, V_1(X)=v is nonconstant and D then fixes the isolated Y. If both are nontrivial, eliminate Y from V_1(X)V_2(Y)-v and D_1(X)D_2(Y)-d. At X=0 the first specializes to -v, the second retains full degree because D_1(0)>0. The Sylvester resultant is nonzero there: after usual homogenization in Y the first vanishes only at infinity and the second not at infinity. Only finitely many X occur, and each leaves finitely many Y by D. This finite-fiber argument is valid also for complex nonzero constants after later specialization.

## 5. Two collisions: all allowed arrangements

The two distinct visible labels yield separate, known constants d12 and d34, not just their product. Label the four coordinates so that equations are
```
D_1(X1)D_2(X2)=d12,       D_3(X3)D_4(X4)=d34,
product_i V_i(Xi)=v,       product_i B_i(Xi)=b.                           (2)
```
There is at least one nontrivial residual tree. For a guess let E be the sum of its *residual nonleaf* exponent guesses. Discard if d12<=H0^k, d34<=H0^k or v<=H0^E. No true guess is lost: each visible pair product contains at least two primes >=P, and v>=P^E with E>0. This explicit test matters for wrong guesses and unbounded exponents. We show the affine complex solution set of (2) is finite for **every** retained guess.

Whenever we use a projective specialization, homogenize each separate equation to its actual degree in each coordinate; a constant factor V_i=1 has degree zero, including at infinity. The product of four projective lines is proper in the last three coordinates, so the projection of the common homogeneous zero locus onto the first projective line is Zariski closed. If X1=1 cannot occur there, that projection is finite. At infinity a polynomial homogenized to its actual degree takes its nonzero leading coefficient at the point (1:0).

**A. Some pair contains two nontrivial trees.** Relabel so that it is pair (3,4), and specialize X1=1. From the first equation X2 is finite (D_1(1)>0 and D_2 has positive degree) and D_1(1)D_2(X2)=d12. Also V_2(X2) cannot vanish: at any of its roots |X2|<=kA and |D_1(1)D_2(X2)|<=H0^k, contrary to the filter. Thus V_1(1)V_2(X2) is finite and nonzero. Since B_1(1)=0, b nonzero forces X3 or X4 to be infinite. If X3 is infinite, D_3,V_3 both have positive degree, and the second and third homogenized equations force D_4 and V_4 to vanish together at X4. This is impossible at a finite point by coprimality and also at infinity by their nonzero leading coefficients. Interchange 3,4 for the other possibility. Consequently the projection omits 1 and only finitely many X1 occur. For an affine solution at such X1, D_1(X1) is nonzero and fixes finitely many X2. After these substitutions the (3,4) trees have a two-tree D,V system with nonzero complex constants, finite by section 4.

**B. Each pair contains one nontrivial tree and one isolate.** Let 1 and 3 be nontrivial, 2 and 4 isolated. At X1=1 the first pair equation again forces X2 finite. Crucially V_2 and V_4 are identically 1, so even at the projective boundary the V equation reads V_1(1)V_3(X3)=v in homogenized X3 coordinates. V_1(1)>0 and deg V_3>0, so X3 is finite. B_1(1)=0 now forces X4 infinite. The second pair equation then forces D_3(X3)=0, so |X3|<=kA. Accordingly |V_1(1)V_3(X3)|<=H0^E, contrary to the strict filter. Again the projection is finite. With any affine X1 fixed, the first D equation fixes X2; V fixes a finite set for X3, and the second D fixes X4.

**C. Exactly one nontrivial tree.** Its nonconstant V_i equals v, hence there are only finitely many choices for its root. Its isolated partner is fixed by their visible pair product; the remaining two isolates have both product and shifted product prescribed by the remaining D and B equations, as in the quadratic in section 4. Cases A, B and C exhaust the possibilities with at least one residual edge.

## 6. Effective deterministic bit bound and final checks

All polynomials have total degree O_k(L) and coefficient bitlength polynomial in L (in fact O_{k,A}(L+log L) before substituting peeled roots; their valuations at positive integer roots and all exact residual constants also have polynomial bitlength). Coefficients can be generated by polynomial arithmetic in at most four variables. The explicit filters H0^E have O_{k,A}(L) bits. For retained guesses with two collisions, the four equations in four variables have only finitely many affine complex points, hence O_k(L^4) by the isolated-point Bézout bound. For one collision use the finite D,V system, or the two isolated quadratic, giving polynomially many points there also.

To list integer solutions on [2,N]^s, s<=4, use fixed-variable existential real feasibility for the equations with real box inequalities (Renegar's bit model). Bisect each remaining integer coordinate interval [l,h] into [l,m] and [m+1,h], m=floor((l+h)/2); the open unit gap contains no integers. Keep only boxes containing a real solution, cycling through coordinates. Disjoint boxes at a level contain distinct feasible points, so the finite-point bound guarantees polynomial work per level, and there are O(sL) levels. Degrees, coefficient lengths, number of equations and box endpoints meet the fixed-dimensional polynomial-bit bound. No approximate-root, generic-rank or heuristic termination claim is used.

Evaluate all node forms for each candidate, including previously peeled roots. Check that their values give distinct primes by deterministic primality testing; divide them out of N to get their true exponents, and verify the labels/exponents, product and totient. Accept only a full prime factorization that exactly reconstructs N and T. On the promised inputs one true guess necessarily succeeds; a false guess cannot certify an incorrect answer. The proof makes no claim to obtain the totient from N or to establish an unrestricted deterministic factoring algorithm.

## 7. Necessity for this fiber proof, not hardness

An edge can be entirely in a peeled tree. For example take four isolated primes 101,103,107,109, two of exponent 2 and two of exponent 3, and add an unshared component 19 -> 191 (191=10*19+1, with leaf exponent 5 and root exponent 1). There are no additional edges among these six primes: this follows by testing the displayed primes against each q-1. The main theorem intentionally does not rely on such an edge after the unshared level has been removed.

After peeling, write the two isolated-pair products as d1,d2 and their total shifted product as b. The invariant v is 1. For any complex s other than d1+1, take s'=d2+1-b/(d1+1-s), then take the two roots of t^2-s t+d1 and the two roots of t^2-s't+d2. Their pair products and total shifted product are exactly the prescribed ones. Infinitely many s give different tuples. The original reduced equations therefore can have a positive-dimensional complex fiber in this case, even though the true values came from primes. This does not give distinct integer factorizations or a lower bound on any unrestricted algorithm.

The earlier single- or three-component results and classical two-prime cases are not claimed anew; the content here is the exponent-level reduction and its four-coordinate finite-fiber conclusion. Neither endpoint density, infinitely many promised inputs, nor a security claim is implied.
