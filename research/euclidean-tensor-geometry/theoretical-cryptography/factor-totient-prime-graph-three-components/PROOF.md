# A finite-fiber reduction for three components of a prime-divisor graph

## 1. Statement and reductions

Fix k >= 4 and an integer A >= 1. The input consists of an odd integer N >= 3 and the exact binary integer T = phi(N). Its unknown prime support S has size r <= k, and max(S) <= A min(S). On distinct vertices of S put p -> q precisely when p divides q-1. Suppose this graph has an edge and at most three weakly connected components (isolated vertices are components). Then one can compute the *complete prime factorization with multiplicities* in deterministic time polynomial in L = bitlength(N). Constants may depend on k and A. The values of r, the factorization of T, the graph, the primes, and the exponents are not supplied. No further totient values are requested.

First trial-divide by all primes through A. If there is such a divisor, then P=min(S)<=A, and every prime is at most A^2. Trial division through this fixed bound finishes the input on the promise. Henceforth take P>A. The odd-input restriction stands as written: deleting a vertex 2 from a different problem need not preserve its graph promise.

The directed graph is acyclic because an edge increases the prime. A vertex q has at most one incoming edge: two parents p,p' would give P^2<=pp'<=q-1<A P, impossible. Its underlying graph is a forest. Indeed in an undirected cycle the numerically greatest vertex would have two smaller neighbors both pointing into it. Each connected component is an out-tree: a tree on s vertices has s-1 incoming-edge counts in total, so exactly one vertex has indegree zero; all others have one parent, reached by a unique path from that root. An isolated vertex is both root and leaf. Consequently the component count is exactly r minus the number of directed edges. This proves the stated four- and five-prime corollaries, under the same size bounds.

## 2. Three exact invariants

Write H for the set of nonleaves (sources of at least one edge) and E for the leaves, that is, vertices with no outgoing edge. Let R=rad(N). The standard identity T/N=phi(R)/R and the squarefreeness of R give gcd(R,phi(R))=product(H). Define the following computable positive integers:
```
g = gcd(N,T);  D = N/g;  U = T/g;
V = N/gcd(N, D^L mod N).
```
Then D=product(E), U/D=phi(R)/R in lowest terms, and V contains precisely the full prime powers of N supported on H. For the last claim v_p(N)<=L and D is squarefree. One never needs to factor D, V or U.

On an edge write q=a p+1 with integer 1<=a<=A. For component i denote its unknown root by x_i. Its nodes have forms l_v(x_i)=c_v x_i+d_v, obtained by starting with x_i and composing these edge maps. All c_v>=1; for nonroots d_v>=1. On the correct assignment c_v<=A because the value of each node is at most A times its root, and d_v<=kA since it is the sum of at most k suffix products of slopes. Write t_v for the outdegree and e_v for the unknown multiplicity in N. Form univariate polynomials with integer coefficients:
```
D_i(x) = product over leaves v in i of l_v(x)
V_i(x) = product over nonleaves v in i of l_v(x)^e_v
B_i(x) = (x-1) product over nonleaves v in i of l_v(x)^(t_v-1)
C = product of all edge slopes a (over every component).
```
Empty products are 1. All three exact equations are
```
product_i D_i(x_i) = D,     product_i V_i(x_i) = V,
product_i B_i(x_i) = U/C.                                     (1)
```
To see the last identity, write phi(R)=product_v(p_v-1). For each nonroot v its factor is its edge slope times its parent; roots contribute x_i-1. Multiplication by D/R cancels one copy of each nonleaf. This accounts for branching, including a source with several children. In particular C divides U on the true guess.

For every component, D_i is nonconstant and D_i(1)>0. Each B_i is nonconstant with B_i(1)=0. A nontrivial tree has V_i nonconstant, V_i(0)=0, D_i(0)>0. An isolated tree has (D_i,V_i,B_i)=(x,1,x-1). In a true tree, different nodes have linear forms with different complex zeros. For if c_u x+d_u and c_v x+d_v share a zero, their values at the true root satisfy c_v p_u=c_u p_v. The distinct prime p_u must divide the positive integer c_u<=A<P, a contradiction. Hence gcd(D_i,V_i)=1 over Q[x]. In the algorithm discard guesses violating this coprimality or the displayed bounds on c_v,d_v. No true configuration is lost; the tests give the needed properties on every remaining guess.

## 3. Finite fibers over the complex numbers

Fix an admissible guessed forest, slopes and exponents, with at least one nontrivial tree, and nonzero constants d,v,b in place of the right sides of (1). We prove the set of affine complex solutions is finite; in particular we do not infer integer finiteness from a numerical dimension test.

**At most two components.** With one tree its nonconstant D_i gives only finitely many roots. With two, choose X to represent a nontrivial tree. If the other is isolated, V_1(X)=v gives finitely many X; D gives Y. Otherwise eliminate Y from F=V_1(X)V_2(Y)-v and G=D_1(X)D_2(Y)-d. At X=0 the first specializes to the nonzero constant -v, while the second keeps its full degree in Y since D_1(0)>0. The fixed-degree Sylvester determinant there is nonzero: in the homogeneous Y-line the first form's only zero is at infinity, and the second does not vanish there. The resultant is thus a nonzero polynomial in X. Each possible X with D_1(X) nonzero leaves a nonconstant equation for Y, and a zero of D_1 cannot be a solution. This proves finite fibers for arbitrary nonzero d,v, not only positive ones.

**Three components, two isolated.** V of the nontrivial tree determines finitely many roots X. For each admissible X let the remaining isolated coordinates be Y,Z. Their product YZ and shifted product (Y-1)(Z-1) are fixed by D and B. Their sum and then the unordered pair follow by a quadratic. The nonzero constants exclude zeros of the already-divided factors.

**Three components, at most one isolated.** Choose X to be the isolated coordinate if one exists, or any coordinate otherwise; write Y,Z for the other two. Both V_2 and V_3 are nonconstant. Homogenize each of the three product equations of (1) separately in each coordinate, using that factor's degree in that coordinate; thus a nonzero constant on the right acquires the corresponding powers of the three denominator coordinates. The common zero locus of these multihomogeneous equations is closed in the product of three projective lines over C. Its projection onto the X-line is Zariski closed (projection from projective space is closed, applied successively to Y,Z).

This projection omits X=1. Indeed B_1(1)=0 and b is nonzero; since B_2,B_3 have positive degree, at least one of Y,Z must be at infinity for the B equation. Suppose Y is infinite. Because D_1(1) and V_1(1) are nonzero and the leading coefficients of D_2,V_2 are nonzero, the homogeneous D and V equations now force the homogenizations of D_3 and V_3 to vanish together at Z. They cannot both vanish at a finite point by the tested coprimality, nor at infinity since they use their actual degrees. If Z is the infinite coordinate, interchange the roles. This proves the omission. A proper Zariski-closed subset of the projective line is finite, hence only finitely many X occur. For any possible *affine* X with a solution, none of D_1(X),V_1(X),B_1(X) vanishes. Dividing them out reduces the remaining Y,Z system to a two-nontrivial-tree fiber already proved finite. This finishes all cases.

## 4. Algorithm and bit bounds

Enumerate 1<=r<=k and all labelled out-forests on r vertices with an edge and at most three components; there are at most 2^(k(k-1)) labelled graph choices at each r. Enumerate integer slopes 1..A on their edges, and multiplicities 1..L on nonleaves (visible-node exponents need not be guessed). Use section 2's rejection tests and skip C not dividing U. The true forest, slopes and multiplicities are among the guesses. There are O_{k,A}(L^k) guesses. All polynomial products have total degree O_k(L); coefficients have bitlength O_{k,A}(L+log L), since evaluation of the absolute-coefficient majorants at 1 bounds every coefficient and all node affine coefficients are bounded. The constants on the right have O(L) bits. The dense representation in at most three variables therefore has polynomial bit size. Polynomial gcds, Sylvester resultants if used explicitly, and their arithmetic are polynomial here; e.g. a two-variable resultant of degree-d inputs in Y has degree O(d^2) in X and bit height O(d(B+log d)) for integer coefficient bit height B and X-degrees O(d), by its Sylvester determinant.

For clarity, an exact uniform way to list the integer roots of (1) does not require mixed resultants. On the box [2,N]^s (s=number of components), ask whether (1) has a **real** solution in the box. An existential real-algebraic feasibility test in fixed dimension with fixed constraint count is polynomial in degrees and coefficient bit sizes (Renegar). Bisect each integer interval [l,h] into the two intervals [l,m] and [m+1,h], m=floor((l+h)/2), testing and retaining only feasible child boxes. Discarding the open unit gap loses no integer. Do this cyclically over the s coordinates until singleton boxes; there are O(s L) levels. Disjoint boxes at a level each contain a distinct real solution. In the three-variable case the finite complex solution set of three equations has at most O_k(L^3) points by the affine Bézout bound for isolated solutions. In the two-variable case the already finite D,V pair has O_k(L^2) points; in one variable use D. Thus only polynomially many feasible boxes and children ever need tests. Boundaries are integer endpoints, so no floating-point precision assumptions or unbounded root-separation search enter. Cases with no feasible points simply exit that guess.

For every surviving singleton, evaluate the node forms; insist on distinct positive primes using deterministic primality tests. Divide N repeatedly by these primes to recover their actual positive exponents. Verify that the product with those exponents is exactly N, and that the computed totient is exactly T. Reject a candidate unless these checks pass. A valid factorization is unique. The graph does not have to be trusted to interpret any answer. This exhausts a deterministic polynomial bit algorithm on the promise, with no assumption about prime density and no large-integer factoring subroutine.

## 5. Why four components are not covered by the fiber argument

This is a limitation of the *equations over C*, not a complexity lower bound. Consider four labelled two-vertex trees, each x_i -> 2x_i+1, with unit multiplicities. The roots 23,29,41,53 and leaves 47,59,83,107 form an actual odd prime support with exactly these edges; one checks divisibility against the eight listed primes. For such a shape the three products in (1) determine only product(x_i), product(2x_i+1), product(x_i-1). Writing f(t)=product_i(t-x_i), these are equivalent to specifying the three values f(0),f(-1/2),f(1). The monic quartics f(t)+z t(t-1)(2t+1), z in C, agree at all three arguments. Each has four complex roots counted with multiplicity, and away from finitely many z they are distinct (the discriminant is nonzero at z=0). Distinct z give distinct root multisets. Thus the same three product equations can have infinitely many complex solutions even while their invariant values came from a real prime fixture. This neither creates infinitely many integer factorizations nor rules out additional information or methods in the four-component regime.
