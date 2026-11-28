# A single-totient lifting theorem for unknown prime multiplicities

## 1. What is available

Fix an integer k >= 4, an integer A >= 1, and 0 < epsilon < 4/k (a smaller positive rational may always be used). Input is N >= 2 and T = phi(N) in binary. Write S for the unknown distinct prime divisors, r = |S| <= k, R = product S and P = min S. Define H = {p in S : p divides q-1 for some q in S}. A source with several outgoing edges counts once. Use width zero for an empty set or singleton.

**Normalization.** At algorithm entry, write N=2^j N_odd by exact division. For j=0 keep T_odd=T; for j>=1 set T_odd=T/2^(j-1). By multiplicativity T_odd=phi(N_odd). If N_odd=1, return (2,1) when j>0. Otherwise run the following argument on (N_odd,T_odd), reusing the letters N,T for that odd pair; on exit, multiply the radical by 2 if j>0 and leave its totient unchanged. Removing 2 only deletes incident edges: an odd prime cannot divide 2-1. Therefore the odd hidden set is exactly the original hidden set minus 2, its width cannot grow, its new least prime cannot decrease, and its ratio/max-count bounds persist. The exact elementary V conditions below refer to the number before the gcd step; the displayed identities hold even on even integers if used directly.

**Theorem.** If max S <= A P and the diameter of H is at most P^(4/k-epsilon), there is a deterministic algorithm polynomial in bitlength(N), with constants depending only on k,A,epsilon, returning R and phi(R). Neither the multiplicities nor r,H,P or a center for H need be given. If |H| <= 1, no size comparison or bound on r is needed for this same conclusion. This statement concerns the radical, not its factorization. It does not provide T from N.

## 2. Elementary gate and the one-outlier case

The classical identity T/N = phi(R)/R follows prime by prime. As R is squarefree, gcd(R,phi(R)) is the product of H. Reducing this rational number to lowest terms gives
```
D = N/gcd(N,T) = product of p in S minus H.
L = bitlength(N).
V = N/gcd(N, D^L mod N) = product of p^v_p(N) for p in H.
```
Indeed each visible prime has valuation one in D, its full valuation in N is <= L, and no hidden prime divides D. The largest prime of S is visible, so D>1. Consequently V=1 exactly when H is empty, and V is a prime power exactly when H is a singleton. Exact integer roots for exponents 1 through L followed by deterministic primality testing recognize the latter (including exponent 1). In those cases R is D or D times the extracted prime, respectively. In all cases after finding R, phi(R) = T R/N exactly. If the gate fails it reports at least two sources, not an obstruction to other algorithms.

For an exact geometric corollary, suppose S consists of odd primes in [u,v], v<2u, and at most one other odd prime q, with q-1<u^2 if it is present. There are no internal edges: if p divides r-1 for distinct odd primes then r >= 2p+1. If q is smaller than the interval, all edges can only start at q. If q is larger, any edges must end at q; two distinct internal sources would have product >=u^2 dividing q-1. If q lies inside, there are no edges. Thus |H|<=1. In particular this applies to one comparable outlier and a remaining cluster of relative width o(1), eventually. The normalization in section 1 handles an even input explicitly.

## 3. Terminal affine relations

An edge from p to q has q=a p+1 with positive integral a, and strictly increases the prime. Successive edges must reach a terminal prime q dividing D. Composing from any hidden p gives q=a p+b. Since p>=P and q<=A P, 1<=a<=A. The intercept is the sum of at most k-1 suffix products of the individual slopes; each is <=a, hence 1<=b<=kA. This remains true for the original directed graph even when intermediate primes have already been removed from the working integer. For P>A all candidate slopes 1<=a<=A are coprime to D.

## 4. The constructive grid

Keep D fixed and let V now denote the residual hidden part. Record each certified prime removed from V, including its entire multiplicity. Stop when V=1; use the elementary prime-power shortcut whenever available. The following loops require no unknown cardinality or real parameter:

* L = bitlength(N), g = ceil(log2(2A)). Enumerate integers 1 <= e <= E <= L. Set B = floor(V^(1/E)) by exact integer root. Put s=floor(log2 B)-g. Skip s<=0. Form M=V D^e, m=bitlength(M), beta=min(1,2 e s/m) exactly as a rational.
* Enumerate integers 1<=a<=A, 1<=b<=kA, skipping gcd(a,D)>1. Set C=B+V times the least nonnegative residue of b (a V)^(-1) modulo D. This is possible since gcd(V,D)=1. In particular C is B modulo V and B+b/a modulo D.
* Apply the univariate small-root theorem [CH, Theorem 1.1] to the monic polynomial f(z)=(z+C)^e with coefficients reduced modulo M, and this beta. It lists all integers w such that |w|<=M^(beta^2/e) and gcd(f(w),M)>=M^beta. Retain only p=B+w>=2 proved prime and dividing V. If found, remove the entire p-power, record p, and restart. A false guess cannot introduce a false prime.
* If the whole grid finds nothing, try division by primes through a fixed bound A P0, with P0 as below. If this does not finish, report outside the guaranteed case. No promise verification is required. At successful termination set R=D times the product of recorded distinct primes, and return (R,TR/N). The shortcut in section 2 likewise records its prime before terminating.

**Why the grid succeeds.** In the correct iteration let E be the sum of residual multiplicities, e their maximum, and p a prime attaining e. Both guesses occur since 2^E<=V<=N. Write h for the number of remaining hidden primes, t for the number of visible primes, and K=E+et. These quantities are for analysis only: K<=e(h+t)<=ek. The weighted geometric mean V^(1/E) lies between the smallest and largest residual hidden prime; both endpoints are integers, so its floor B still lies in the same closed interval. For w=p-B we have |w|<=diam(H).

Choose the terminal q and a,b of section 3. Then p and q are distinct, both divide w+C, and p^e and q^e divide M. Thus gcd(f(w),M)>=(pq)^e. For correct guesses 2^s<=B/(2A)<=P/2, even if P itself is visible rather than hidden. In particular 2es<=log2 M, so beta was not clipped, and M^beta<=2^(2es)<=(pq)^e.

It remains to bound the radius uniformly when e varies. Write x=log2 P. Since M is a product, counted with multiplicities, of K primes of S, xK<=log2 M<=K(x+log2 A), so m+2<=K(x+g+3) and s>=x-g-1. When x>3g+5 both lower bounds used below are positive. For m>=2, (m-1)/m^2>=1/(m+2). Therefore
```
log2(M^(beta^2/e)) = 4e s^2 log2(M)/m^2
  >= 4e s^2/(m+2)
  >= (4e/K) (x-g-1)^2/(x+g+3)
  >= (4/k)(x-3g-5).
```
The last step uses (x-u)^2/(x+v) >= x-2u-v and the positivity of x-3g-5. Take for instance P0 = 2^ceil(max(g+1,3g+6,4(3g+5)/(k epsilon)+1)). For P>P0 the radius covers P^(4/k-epsilon), so the true w is listed. For P<=P0 all primes of N are at most A P0, so the fallback finishes. Importantly, the same P from the original S works after every removal. There are at most k restarts.

**Complexity.** D and V are computed by gcd and fast modular powering. The double grid has O(L^2) pairs, the affine grid has at most k A^2 pairs. All integer roots are binary computations; M has O(L^2) bits, degree e<=L, and the rational beta has polynomial bitlength. CH Theorem 1.1 gives deterministic polynomial time in the modulus bitlength and degree; a monic polynomial of this degree is built by polynomial arithmetic. The bounded fallback is a class-dependent constant number of trial divisors, even if N has arbitrarily large multiplicities. Exact divisions take polynomial bit time. There is no factoring of T, no extra totient query, and no randomized or heuristic subroutine.

## 5. What composes

Any squarefree solver for a class defined on the distinct primes may be invoked with R and phi(R) provided its own promises hold. If it supplies all primes, recover the multiplicities by exact division into N. With a promise algorithm of cost F(bitlength R), the compositional cost is poly(bitlength N)+F(bitlength R). This implication does not itself prove a squarefree algorithm.

For example, consider two ordered comparable clusters, each of width o(P), with distinct primes in [P,AP]. There are no within-cluster edges for sufficiently large P, and any edge crosses from the lower cluster into the upper cluster. Thus H is contained in the lower cluster. If it has width at most P^(4/k-epsilon), the theorem lifts any squarefree result for these clusters to unknown multiplicities without changing its other hypotheses. In the pair-plus-rest setting with exactly k primes, the stipulated squarefree exponents for the pair and the (k-2)-set are respectively min(1/2,4/k) and min(1/2,2/(k-2)); both are <=4/k when k>=4. Fixed positive slack in each upper bound transfers to the theorem. The scale P concerns distinct primes, never N^(1/k) when multiplicities vary. This example is conditional on the separate squarefree theorem, not an independent priority claim for that theorem.

When |H|>1, replacing each distinct prime by repeated copies in the squarefree shifted-product identity is not legitimate: phi(p^e)=p^(e-1)(p-1), not (p-1)^e. Conversely, if all exponents coincide and are known, simply take an exact integer root; if unknown, polynomially many exponents may be tried and a candidate complete factorization verified. No novelty is claimed for the classical two-prime cases or the known three-prime unequal-exponent case. See UPSTREAM.md.
