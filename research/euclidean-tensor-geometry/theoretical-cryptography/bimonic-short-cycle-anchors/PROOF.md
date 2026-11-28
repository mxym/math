# Anchoring prime-support graphs by short bimonic cycles

## 1. Public setup and the promise

Let L=bitlength(n) for n>=2. A deterministic public rule on L alone returns a nonempty catalogue F_1,...,F_s of integer bivariate polynomials of positive degree in each variable with total dense encoding size polynomial in L, and integers d>=1 and h>=2. We allow s,d,h to depend on L. Each partial degree is <=d. The leading coefficient in X when the polynomial is viewed over Z[Y], and the leading coefficient in Y over Z[X], must both be **nonzero integer constants**. These constants need not equal one. We call this the bimonic condition here; it is a syntactically checkable finite-constant-fibre-degree hypothesis over C, not a claim of good reduction at every rational prime. Swapping the variables preserves it. Assume

  (2 s d)^h <= (L+1)^C

for some fixed public constant C, with the public rule also polynomial time. This includes fixed h and polynomial-sized catalogues and degrees, and h=O(log L) with constant s,d. The result is in the bit model.

The graph of n has the distinct positive primes dividing n as vertices. A pair of different vertices p,q can be joined by an exact relation F(p,q)=0 or F(q,p)=0 for a catalogue entry, retaining every label and each permitted orientation. Integer powers of the vertex primes in n are arbitrary. A labelled closed walk of length m>=2 follows m edges and returns to its first vertex, with a word of m oriented equations satisfied along the walk. Internal vertices may repeat, but there are no edges from a vertex to itself. Two different parallel relation constraints can give a circuit of length two. Using one constraint immediately in reverse has identically zero diagonal: for every complex starting value there is a step along the constraint and back. A single vertex is not sufficient.

For every word w, define its endpoint and diagonal polynomials by the recursion of section 2. A word is **anchoring** if its diagonal H_w is not identically zero; this can be tested using only the public word. The promise on n is that its graph is connected and has a labelled closed walk of length between 2 and h with an anchoring word. The prime support, cycle, word and multiplicities are not supplied.

**Theorem.** Complete factorization of a promised n can be found deterministically in polynomial time in L, and exact membership in this promise class can also be decided in polynomial time. This is not a result for unrestricted integer factorization or for general modular relations. In particular connectivity alone does not suffice for this proof. Prime powers lie outside this cycle promise; they can of course be handled separately by exact power checks and primality.

## 2. Exact endpoint polynomials, including reduction of multiplicities

For an oriented word F_1,...,F_m (the names here denote chosen equations, not necessarily distinct entries), put

  P_0(T,Y)=Y-T,
  P_{i+1}(T,Y)=Res_U(P_i(T,U),F_{i+1}(U,Y)),
  H_w(T)=P_m(T,T).

Let a_i be the leading Y-coefficient of P_i, and m_i its Y-degree. Initially a_0=1, m_0=1. Fix any complex T=t. If a_i is a nonzero constant, P_i(t,U) has exactly degree m_i. The Sylvester determinant agrees with the fixed-degree resultant at every specialized (T,Y), because the leading coefficients in U are constant and nonzero. By the root-product identity it is

  a_i^e times prod_{P_i(t,u)=0} F_{i+1}(u,Y),

where e=deg_U F_{i+1} and the roots of P_i(t,U) are counted with multiplicity. Each specialized factor in this product has the same positive Y-degree b=deg_Y F_{i+1} and constant leading coefficient c, by the bimonic hypothesis. Thus m_{i+1}=b m_i and a_{i+1}=a_i^e c^{m_i}, independent of t and nonzero. For each t, the **set** of roots of P_{i+1}(t,Y) is exactly the set of endpoints of one more allowable step from roots of P_i(t,U). By induction it is the endpoint set of all affine complex paths starting at t with those oriented relations. This specializes correctly at every t, not merely generically; ramification and repeated roots cause no problem. Contents multiply polynomials by nonzero scalars and do not change root sets. The proof never divides out a T-dependent coefficient.

In particular the set of first coordinates of complex closed paths of type w is exactly the zero set of H_w. If H_w is nonzero it has finitely many roots, after which each path has only finitely many choices per step. If H_w vanishes identically there is some such closed path for every complex t. This last assertion is about the full affine equations, which allow repeated or nonintegral values. In particular it does not assert the existence of a prime cycle or preclude isolated prime solutions in other components. The membership promise asks for an actual prime closed walk and a nonzero H_w, not just one isolated solution of some word with vanishing diagonal.

## 3. Uniform polynomial elimination even for logarithmic length

By construction m_i<=d^i, and the T-degree of P_i is also <=d^i. In the Sylvester determinant at step i+1, each term includes e<=d entries from rows of P_i and m_i<=d^i entries from rows of F_{i+1}. Only the former depend on T, so the T-degree multiplies by at most d. Only the latter can depend on Y, so the Y-degree is at most d m_i. Thus the diagonal degree is <=2 d^m.

For coefficient sizes, let ||P|| denote the sum of absolute values of a polynomial's integer coefficients. For a chosen catalogue entry let b bound log_2(1+||F||) across all entries; b is polynomial in L by dense encoding. Each coefficient entry drawn from P_i or F has norm at most the source norm, and the coefficient norm is submultiplicative. The Sylvester size is m_i+e, so

  ||P_{i+1}|| <= (m_i+e)! ||P_i||^e ||F_{i+1}||^{m_i}.

Writing B_i=log_2(1+||P_i||), this gives

  B_{i+1} <= d B_i + O(d^i b + (d^i+d) log_2(d^i+d+1) + 1).

For example dividing by d^{i+1} and summing shows B_i <= d^i poly(i,b,log(d+1)); the same bound for d=1 follows from the displayed recurrence directly. All these quantities are polynomial in L under the public bound. Taking a diagonal cannot increase the coefficient norm. The number of words of lengths 2 through h is polynomial as well: there are no more than (2s)^m at length m and h=O(log(L+1)) under the same bound.

These resultants can be computed by exact integer determinants and interpolation, as well as by any standard dense resultant algorithm. For example at each step evaluate the determinant on a rectangular grid of integer T,Y values with enough points to interpolate the two degree bounds, each bounded by d^{i+1}. The grid size is polynomial. Entries and determinants on that grid have polynomial bit size by the norm estimates and the polynomial bound on exponents. Exact fraction-free determinant computation, followed by rational interpolation on the distinct integers, has polynomial bit cost. Thus the proof of the time bound does not use a general high-dimensional solver or assume that growing word length is a fixed number of variables.

For a nonzero H_w, list its integer roots, keeping only primes dividing n. Deterministic univariate polynomial factorization over Q, for example, finds all integer roots by computing the linear factors and checking their root integrality; contents and multiplicities are irrelevant. Deterministic primality is standard. A constant nonzero H_w has no roots. For each retained p and its word, follow the word from p and certify whether it is possible to return to p after the prescribed number of steps: at step i solve the specialised univariate F_i(v,Y) at the current vertex v. Keep only roots that are primes dividing n and differ from v, as there are no self-edges in the promise graph. There are at most d choices per step even before this filtering. Thus testing one root-word pair branches at most d^m times up to polynomial factors; this is polynomial by hypothesis. The test permits repeated vertices at different steps. It can certify an actual labelled closed walk or discard an algebraic anchor candidate having no such walk. This filtering is a finite certificate test; it does not attempt to reconstruct all complex paths.

If n satisfies the promise, one tested integer root and word is the start of its actual anchoring walk, and the certificate search succeeds. Conversely a successful certificate consists only of prime divisors of n with the required exact edge equations and a nonzero diagonal word. If no pair gives a certificate, n cannot satisfy the promise.

## 4. Neighbour recovery and exact verification

Choose any one certified anchor p and traverse from it in both directions in the graph. From each validated prime v, every incident neighbour occurs among the integer roots of F(v,Y) or F(Y,v) for the public entries. These polynomials are never identically zero and have their original degrees by the two constant leading coefficients. List their integer roots as above and add only new primes >1 dividing n. Process each added vertex at most once. Record the full power of each visited prime by exact division. The checks can keep using the original n for recognition of factors; an earlier prime need not still divide the running residual. No prime not dividing n can be visited. Since n has at most L distinct prime divisors there are at most L vertex visits, each with polynomial work even allowing repeated roots or different labels at the same pair.

The visited set is exactly the connected component of the certified anchor in the actual graph, not just a subset of it, since all neighbours of every visited vertex were tried. Therefore a unit residual proves both complete factorization and graph connectivity; the anchoring walk has already been certified. A nonunit residual proves n is outside the promise because the actual graph has another component. There is no need to combine traversals from multiple seeds or to re-enumerate cycles in a graph reconstructed after the traversal. The input, if not in the promise, may be rejected without returning a full factorization. This proves exact membership and the asserted deterministic complexity. The result makes no factoring claim when all true short walks have identically zero diagonals.

## 5. Examples and a directed sufficient condition

Let the edge equations be Y^2-(2X+1)^2=0 and Y-3X-8=0. Both are bimonic, including after reversal; the first is genuinely multivalued and reducible. The primes 5,11,23 have the first two edges 5 -> 11 -> 23 and close via the reverse of the second edge. The two consecutive multivalued steps have possible endpoints
  ±(4X+3), ±(-4X-1).
The final reversal demands that the endpoint there equal 3X+8. No possible endpoint equals 3X+8 identically; hence the closed word has a nonzero diagonal. The branch 4X+3=3X+8 pins X=5. The same multivalued equation joins 23 to 47. Thus the actual support {5,11,23,47} is connected; the short cycle does not have to mention every prime. Conversely using an edge and its exact reverse yields a path back to every t, so such a diagonal is identically zero. The checkers test this distinction without attempting composite factorization.

A second two-edge circuit uses the multivalued relation Y^2-(2X+1)^2=0 followed by 3Y-X-1=0. Its diagonal is (3X-1)^2-(2X+1)^2=5X(X-2), hence the positive prime 2 is a possible anchor. The branch 2 -> 5 -> 2 is a valid closed prime walk, while the root -5 of the first step is not a positive prime. This example also distinguishes a genuinely different return relation from simply reversing the first.

For a narrower dynamic situation fix a constant number of nonconstant rational-coefficient polynomial maps (including affine maps with rational coefficients), encoded by bimonic equations Y-f(X)=0 after clearing constants. If the support graph using the **forward** map edges is strongly connected of directed diameter D and it contains an actual edge of degree >=2, that edge plus a shortest return path gives a simple directed cycle of length <=D+1. The resulting composition has degree equal to the product of the degrees, at least two (leading terms under nonconstant univariate polynomial composition cannot cancel). Hence its fixed-point equation is nonzero, and so is the diagonal for that forward word. In particular D=O(log L) puts it in the unified theorem for constant degrees and alphabet. This is only a sufficient route; the general multivalued theorem does not need a directed diameter bound. It does not permit substituting arbitrary rational maps with poles for bimonic equations.

For a finite check use f=x^2+x+1, g=(x-1)/3, h=2x+1, k=(x-1)/2 and true support {2,5,7,11,23,47}. The forward graph contains 2 -> 7 under f and 7 -> 2 under g, plus the bidirectional chain 2,5,11,23,47. Its directed diameter is five. The composed fixed-point equation is x(x-2)/3=0, so the prime seed is 2. The finite instance has product 832370 (L=20). Both examples are purely arithmetic and make no density or infinite-prime-tuple assertion.
