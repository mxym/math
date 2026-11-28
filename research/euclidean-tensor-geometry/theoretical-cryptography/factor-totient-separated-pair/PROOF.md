# Pair-and-cluster totient theorem

## 1. Statement

Let k>=4 be fixed, n=k-2. Fix 0<c<C, delta>0. All k primes dividing the squarefree positive integer N lie in [cX,CX]. Their unordered set admits a partition P={p,q}, Q={r_1,...,r_n}. Write a=sqrt(pq), b=(product Q)^(1/n), U=|p-q| and V=max Q-min Q. Assume |a-b|>=delta X. The parameter X and the partition, the order of the two centers, and even the numerical constants c,C,delta are not required as inputs. Put

    A=min(1/2,4/k),    B=min(1/2,2/n).

For every *fixed* 0<epsilon<min(A,B), when U<=X^(A-epsilon) and V<=X^(B-epsilon), the entire factorization can be determined from the two ordinary integers N and T=phi(N) deterministically in bit time polynomial in log N. Constants in this assertion may depend on the fixed parameters. It is not asserted that T can be obtained from N, or that unpromised inputs admit such a running time. The claim is sufficient, not an optimality statement.

## 2. Matching the actual branch

Here allow general fixed multiplicities m,n>=1. On 1<x<N^(1/m), put

    y(x)=(N/x^m)^(1/n),
    G(x)=m log(x-1)+n log(y(x)-1).

The true geometric means a,b satisfy y(a)=b. The derivative is exactly

    G'(x)=m(y(x)-x)/[x(x-1)(y(x)-1)].

At both endpoints G tends to minus infinity; it increases until the diagonal x=N^(1/(m+n)), then decreases. To estimate G(a)-log T, apply Taylor's theorem to h(z)=log(exp z-1) at the arithmetic mean of the log entries inside each cluster. On the comparable range, -h''(z)=exp(z)/(exp(z)-1)^2 lies between positive constant multiples of 1/X. The linear terms sum to zero; the sum of squared log deviations is bounded above and below by constants times the squared log range, which is comparable to (diameter/X)^2 (and zero for a singleton). Therefore

    G(a)-log T = Theta((U^2+V^2)/X^3).

The difference is strictly positive here. If a<b, the unique solution s on the increasing side is to the left of a; if a>b the unique solution s on the decreasing side is to the right of a. Define t=y(s), **not the other root in x**. Every point between a and s has |y(x)-x|>=|b-a|. At a genuine solution,
T/N=(1-1/s)^m(1-1/t)^n=1-O(1/X), so s,t are both bounded below by a positive multiple of X. Since s^m t^n=N, both are also O(X). Monotonicity of y gives the same size estimates throughout the segment. Consequently |G'| is comparable to X^-2 there and |y'|=m y/(nx) is bounded above and away from zero. The mean value theorem gives

    |s-a|, |y(s)-b| = Theta((U^2+V^2)/X).

All implicit constants depend only on the fixed comparison, multiplicity, and separation parameters. For unequal multiplicities no statement comparing the other x-root to b follows; that root can simply be tried and verified like any other candidate.

## 3. Obtaining the sum of the unknown pair

Take m=2. Then S=p+q has S-2a=(p-q)^2/(sqrt(p)+sqrt(q))^2=O(U^2/X). Section 2 gives

    |S-2s|=O((U^2+V^2)/X)=O(X^(-2 epsilon)).

For large X this is less than 1/8. To list candidate sums using only the two input integers, eliminate y from

    x^2 y^n-N=0,    (x-1)^2 (y-1)^n-T=0.

Their resultant in y is a nonzero integer polynomial in x: at x=1 the first polynomial is monic of degree n and the second is the nonzero constant -T, giving (-T)^n. Degrees are bounded in terms of k, and coefficients have O_k(log N) bits by the fixed-size Sylvester determinant. Its real roots include s. Remove repeated factors via a polynomial gcd, and isolate and refine each real root to absolute error <1/16 using standard deterministic real root isolation. List the nearest integer to twice each approximation (ties may both be retained). The true S is in this list because its distance to twice the appropriate approximation is <1/4. No pairing of the other roots or transcendental numerical log evaluation is needed. Negative or other irrelevant candidates cause no problem.

## 4. Locating the product of the pair

Write D=pq and E=(p-1)(q-1)=D-S+1. All input primes are odd for large X. In any one cluster, the largest prime is less than twice the smallest. If a prime r divides a distinct prime l minus one, then l>=2r+1 for these odd primes. Thus gcd(D,E)=1; moreover every prime in g=gcd(N,T) lies in the lower cluster. Squarefreeness implies g is exactly a product of some primes in that cluster. If the pair is lower and g>1, then g=p, q, or D. For each candidate S try D=g and D=g(S-g); the correct value is present. Checking the extra branches is harmless.

In all other cases D divides R=N/g and gcd(R,T)=1. The latter follows from squarefreeness: every prime of N dividing T has been removed once. For the true even S put b0=S^2/4, an integer. Skip odd candidate sums. Then w=D-b0=-(q-p)^2/4. Apply the elementary Chinese remainder theorem to define an integer c0 by

    c0 = b0 (mod R),    c0 = b0-S+1 (mod T).

Since D|R and E|T, one has D|w+c0 and E|w+c0. Since they are coprime, DE divides both w+c0 and the **original** M=NT, not just a quantity whose size may vary with g. Here M is comparable to X^(2k) and DE is comparable to X^4. The linear small-root theorem stated as Cohn-Heninger, Theorem 1.1, lists in polynomial bit time all integers z with |z|<=M^(beta^2) and gcd(z+c0,M)>=M^beta, for fixed 0<beta<=1. Choose a rational eta with 0<eta<min(1/k,epsilon/4), and beta=2/k-eta. Then M^beta=o(DE), and

    |w|=O(X^(8/k-2 epsilon)),
    M^(beta^2) is comparable to X^(8/k-8 eta+2k eta^2).

Thus w is among the listed integers for large X. Collect candidates D=b0+z. Keep only D|N with S^2-4D a nonnegative square and distinct positive prime roots of x^2-Sx+D. Also require E=D-S+1>0 and E|T. One genuine pair survives by the foregoing argument. If an unrelated candidate also survives, do not assume the complementary cluster promise on that branch: simply test it, continue after unsuccessful branches, and accept only a certified full factorization.

## 5. The remaining close cluster

On the genuine branch the residual data are H=N/D and K=T/E=phi(H). For n=2 the sum of the remaining primes is H+1-K, so a quadratic suffices. For n>=3 put a0 equal to an integer approximation to H^(1/n) of absolute error <=1 (integer n-th root suffices). This root lies between smallest and largest residual primes, so for each residual prime r,

    |r-a0|<=V+1=O(X^(2/n-epsilon)).

The same separation-within-a-cluster observation gives gcd(H,K)=1. On a candidate branch failing this test simply skip it. Choose c1 congruent to a0 modulo H and a0-1 modulo K. Then for z=r-a0, r(r-1) divides both z+c1 and HK. Here HK is comparable to X^(2n) and r(r-1) is comparable to X^2. Choose rational 0<eta'<min(1/(2n),epsilon/4) and beta'=1/n-eta'. Then (HK)^beta'=o(X^2) and

    (HK)^(beta'^2) is comparable to X^(2/n-4 eta'+2n eta'^2).

All residual primes appear in one call of the quoted linear small-root theorem. Check primality of the listed candidate divisors, that the full product is N with precisely the specified number of distinct factors, and that their shifted product is T. This verification proves correctness independently of the behavior of false intermediate branches.

For completeness, k=4 has an elementary variant: perform the same sum-list procedure for both pairs (m=n=2); each actual pair occurs on its correctly matched side. For candidate sums S,J, put h=S-1, j=J-1. If D is the first pair product, N=DD' and T=(D-h)(D'-j), so

    j D^2-(N-T+hj)D+hN=0.

Try the integer roots and validate both pairs by their quadratics. No lattice theorem is necessary for this special case.

All divisions, gcds, polynomial arithmetic and deterministic primality/real-root tests above have polynomial complexity in the input bit length, and the small-root guarantee is stated only for fixed parameters. The output lists have polynomial size; products of a fixed number of such lists still have polynomial size. Handle bounded exceptional X without incorporating an unknown cutoff into the procedure: if the attempted construction fails, do trial division. On the promised family a failure is possible only for bounded X depending on the fixed constants, so this fallback contributes only a constant to the worst case on that family. It is not a polynomial-time claim for arbitrary unpromised inputs.

## 6. Shell count and meaning of the improvement

Let Y=X^k and take two separated fixed positive-length subintervals of [X,(1+h)X] where (1+h)^k<2. The coefficients implicit here can be chosen freely to specify one nonempty choice of comparison and separation constants; this is not a counting theorem for every preassigned c,C,delta. Partition the first interval into O(X/u) bins of length at most u=X^(A-epsilon), and the second into O(X/v) bins of length at most v=X^(B-epsilon). Each full interval has order X/log X primes by the ordinary prime number theorem for fixed proportional intervals; **no** short-interval prime number theorem is being invoked. For fixed d>=2, if a proportional interval contains P primes in J bins where P/J tends to infinity, the sum of binomial(h_i,d) is at least a constant times J(P/J)^d. Indeed at least P/2 primes belong to bins with h_i>=P/(2J), and each such prime belongs to binomial(h_i-1,d-1) distinct d-subsets, counted d times. This gives Omega(X w^(d-1)/(log X)^d) for width w. Apply it separately for d=2,n. Every resulting distinct N is squarefree in [Y,2Y]; the intervals distinguish the groups and prime factorization distinguishes the choices. Their number is at least a fixed positive multiple of

    X^[2+A+(n-1)B-n epsilon] / (log X)^k.

The limiting exponent in Y as epsilon decreases to 0 is e_k=[2+A+(n-1)B]/k: for k=4,5,6 it is respectively 3/4, 7/10, 2/3. These are sufficient exponents with a fixed margin, not exact endpoint counts or positive density. Within this constructed shell g=1, since the entire range has ratio less than 2; the general theorem did not need this.

For comparison, simple individual localization in the original product yields width exponent 2/k in X, as the useful divisor p(p-1) has size Theta(X^2) inside the modulus NT of size Theta(X^(2k)). For k>=5 both A and B strictly exceed 2/k. With small enough epsilon, fix 2/k<alpha<min(A-epsilon,B-epsilon). The number of constructed tuples having either actual diameter at most X^alpha is at most a constant times
    X^2 [X^alpha v^(n-1)+u X^((n-1)alpha)].
For the low-width group first choose its minimum and bound the other choices by its diameter; do the same for the other group, ignoring primality. This error has a strict power saving against the displayed lower bound. Thus many of the counted inputs have neither group as narrow as that direct sufficient individual-route width. This does not preclude that some individual primes are accessible by other centers or unrelated means. In particular the k=6 count improves the narrow-first 2+4 route with exponents (1/3,1/2) and resulting limiting count 23/36, **not** all possible two-cluster partitions, and not all known deterministic routes. At k=5 the width box (1/2,1/2) is incomparable with the basic narrower-pair/longer-complement box (2/5,2/3); at k=4 the symmetric half-width box itself is not an enlargement of the prior (1/2,3/4) basic bound. No comparison is claimed with every special case in the literature.
