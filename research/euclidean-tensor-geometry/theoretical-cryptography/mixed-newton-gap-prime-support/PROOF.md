# Newton-gap correspondences on connected prime supports

## 1. Public hypotheses and theorem

Fix coprime positive integers a>b and let lambda=a/b. Given the unary bit length 1^L, a public deterministic rule outputs a list of integer bivariate polynomials, of polynomial total binary length in dense coefficient encoding, in polynomial time in L. The list depends only on L, not on individual integers of that length. A label is written in its normalized order
```
H(X,Y) = Y^v - X^u + sum_(i,j) c_ij X^i Y^j,     u>=v>=1,
u/v belongs to {lambda^k:k>=0}.
```
One may swap the variables and negate the polynomial to put a label in this form. Each displayed sum uses nonzero residual coefficients only. Define
```
Delta_ij = u v - v i - u j.
```
Require Delta_ij>=v. For each label let C_H be a positive integer with |c_ij|^v <= C_H^Delta_ij for every residual term. Use the least such integer, or an explicitly verified one. The catalogue family is assumed to have a bound C_H numerically polynomial in L, not merely of polynomial bit length. This is a public hypothesis, not an extra argument or a hidden property of the input primes. The least bound is computable by exact integer root comparisons on |c_ij|^v; even before the bound is used, all exponents and intermediate bit lengths in these comparisons are polynomial in L. The condition does not require the individual coefficients themselves to be numerically polynomial. Let M_H count the residual monomials and put
```
B = max(1, max_H M_H C_H).
```
The inner maximum is omitted if the catalogue is empty. All public checks above are elementary: for example membership of a rational degree quotient in the prescribed cyclic group is tested by exact powers of fixed a and b.

Let N>=2 have binary length L. The vertices of its graph are the distinct prime divisors of N. If H(p,q)=0 with p and q distinct, add a labelled edge oriented from p to q, with signed degree increment k given by u/v=lambda^k. Reverse traversal has increment -k. Parallel labels are allowed; connectedness forgets orientation and labels. A singleton is connected.

**Theorem.** The connected-support class is recognizable in deterministic polynomial bit time from N alone, and every accepted input is completely factored by the recognition argument. Neither the support size nor the prime multiplicities are fixed. No tree, path, exponent, label on a designated pair, or prime size is supplied. The theorem concerns just the stated catalogue family and exact relation graph; inputs outside the class are rejected, not claimed to be generally factorable.

## 2. Weighted-gap estimate and cycle consistency

Use p and q here for the first and second coordinates of one oriented equality, not for primes ordered by size. Let Z=max(p^u,q^v). For positive coordinates with p>C_H, an individual residual term satisfies
```
|c_ij| p^i q^j / Z
 <= C_H^(Delta_ij/v) Z^(-Delta_ij/(u v))
 =  (C_H/Z^(1/u))^(Delta_ij/v)
 <= C_H/Z^(1/u) <= C_H/p.                                      (1)
```
Indeed p<=Z^(1/u) and q<=Z^(1/v), the base C_H/Z^(1/u) is less than 1, and Delta_ij/v>=1. Using the sum only after this weighted estimate is important when the raw coefficient magnitudes are large. On H(p,q)=0 it follows that
```
|p^u-q^v| / Z <= M_H C_H/p <= B/p.                               (2)
```
If p>2B, the smaller of p^u and q^v is at least (1-B/p)Z, and hence
```
|v log q-u log p| <= -log(1-B/p) <= 2B/p.                         (3)
```
This bound on the difference of two logarithms of powers avoids losing a factor converting first to a quotient with a possibly smaller denominator.

Let P be the actual minimum prime divisor of N, take A_0 to be the least positive integer with lambda^A_0>=2, and set B_0=16 A_0 L B. If P<=B_0 a small prime seed is covered separately in §4. Assume P>B_0 for the ensuing analytic argument. For an edge with increment k, (3) gives
```
|log log q-log log p-k log lambda| <= 4B/(P log P).                (4)
```
In fact write v log q=u log p+eta with |eta|<=2B/P, and use |log(1+eta/(u log p))|<=2|eta|/(u log p). Reversing an edge changes the sign of the entire discrepancy, so the same bound applies. We use log P>1.

Pick a spanning tree of the true graph for the proof only. Assign integer heights by accumulating signed edge increments along its paths. Each additional edge and its tree path give a fundamental closed walk of at most L steps, since the number of support vertices is at most L. This includes the two-edge case for parallel labels. Summing (4), the log-log differences telescope and the signed integer increment sum times log lambda has absolute value less than 1/(4 A_0), which is below log lambda because log 2>1/2. Hence that integer sum is zero. Thus all labelled edges are consistent with the same integer height differences in the large-prime case. Small-prime inputs need not satisfy this conclusion.

## 3. An additive position bound from an enumerable rational exponent

Subtract the minimum height from all heights, giving h_p>=0. For any height-zero vertex x set w_p=lambda^(-h_p) log p. On a true directed edge p to q, lambda^(h_q)=lambda^(h_p) u/v, so
```
w_q-w_p = lambda^(-h_q) (v log q-u log p)/v.
```
The bound from (3) is therefore at most 2B/P in absolute value in either traversal direction. This is the normalized bound; it is not a claim that an unnormalized forward error is invariant under reversal. Along a tree path, whose length is at most L,
```
|w_p-log x| <= delta := 2LB/P < 1/8.                              (5)
```
Since w_P<=log P, (5) gives x<=exp(delta) P<=2P. Also every w_p exceeds log 2 since x>=P>=3 and delta<1/8.

Writing e_p for the true multiplicities, define E=sum_p e_p lambda^(h_p). It is at least 1, and
```
log N = sum_p e_p lambda^(h_p) w_p.
```
Consequently E<=log N/log 2<L and log N/E is a weighted mean of the w_p. Combining (5) with exp(delta)-1<=2delta yields
```
|N^(1/E)-x| <= 4P delta = 8LB.                                    (6)
```
Choose H_* = max{h>=0:a^h<=L b^h} and D=b^H_*. Since each e_p>=1 and E<=L, each h_p<=H_*. Thus E=J/D for some integer D<=J<=LD. The number D is numerically polynomial in L: for b>1 choose a fixed c with b<=lambda^c, giving b^H_*<=L^c; for b=1 it is 1. The true E is in this short rational list without enumerating heights, witnesses or multiplicities. The logarithms have all been used in the proof, not in the evaluation of the candidate list.

## 4. Complete recognition and bit bound

The list includes every integer in [2,min(B_0,N)] and the integers up to distance 8LB+1 from floor(N^(D/J)) for D<=J<=LD, always clipped to [2,N]. The integer floor is found by the exact comparison t^J<=N^D and integer bisection. On a connected input the list contains a prime divisor: this is P in the small case and a height-zero x by (6) otherwise. There is no claim that every candidate is a true divisor, so keep only prime divisors using polynomial-time deterministic primality and exact division.

For a retained prime t, consider both specializations H(t,Y) and H(X,t) for every label. They have degrees exactly v and u and respective leading coefficients +1 and -1: Delta_ij>=v>0 implies i<u and j<v for every residual term. This holds even at zero or very small arguments. By deterministic rational univariate polynomial factorization, all positive integer roots can be listed via the linear factors; repeated roots are counted only once. Retain a root as a neighboring vertex only if it is a distinct prime divisor of N and satisfies the original oriented equality. Each closure processes a prime once. The set reached from a seed is exactly its component of the actual graph; both directions are needed. It contains at most L vertices, independently of the number of possible symbolic paths.

For each such closure divide N repeatedly by its listed primes to extract full exponents. Accept if the residual equals 1 for any closure, and reject otherwise. If it accepts, divisibility and primality certify the listed factorization, and the true edges of that closure connect the full support. If the true graph is connected, a listed prime seed has full closure, which ensures acceptance. Prime powers, including primes, use the singleton convention. N=1 is outside the model. One need not guess or verify heights to check membership: only the exact polynomial edges on the full support matter.

Here are explicit bit bounds. The seed list has no more than B_0+(LD-D+1)(16LB+3) entries with duplicates retained. It is polynomial in L. Integer root comparisons use exponents at most LD and integers of O(L²D) bits, with O(L) comparisons per center. If d_* and K_* are the maximum partial degree and maximum coefficient bit length, specialization at an integer at most N uses polynomially many bit operations and yields coefficients of bit length O(d_* L+K_*+log(d_*+1)). Both parameters are bounded by the dense input budget. Deterministic univariate factorization takes polynomial bit time in the resulting degrees and bit lengths. Each closure processes at most L nodes times the polynomial number of labels, and uses ordinary exact division and deterministic primality testing. This proves the bound without using a bivariate or modular small-root algorithm. The argument does not take as input any partial prime positions or results from a factoring oracle.

## 5. Subsuming the monic separated catalogue

An earlier statement uses pairs of monic integer polynomials F,G with roots in a polynomial-radius disk of radius R and degree ratios in the same cyclic group. Write the equality as G(Y)-F(X)=0 in the order u=deg F>=v=deg G, swapping and negating when necessary. For pure residual X^i with i<u, Delta_ij/v=u-i>=1. For Y^j with j<v, Delta_ij/v=(u/v)(v-j)>=1. The coefficient bounds from expansion into roots are |[X^i]F|<=(uR)^(u-i) and |[Y^j]G|<=(vR)^(v-j). Thus a common C_H=2 max(u,v) R suffices, including for the combined constant coefficient: its absolute value is at most R^u+R^v<=2R^u. The transformed catalogue retains the same graph, and signed traversals have the same increments. This shows that the present theorem includes all those promises, not just some numeric-small-coefficient subclass.

Conversely the format genuinely permits mixed terms. It also does not reduce to an unweighted numeric bound on the raw coefficients. For example, for m>=3 the polynomial (Y-1)^m-(X-1)^m+XY has u=v=m, satisfies the stated gap and admits C_H=m by binomial coefficient bounds. Its largest coefficient is exponential in m up to polynomial factors. This demonstrates scope for public polynomials, not the existence of any specified prime points on that particular curve.

## 6. A genuinely nonseparated equation and a separate large-branch check

First take the small-coefficient polynomial
```
H1(X,Y)=Y²-20XY-X⁴-124.
```
It has u=4, v=2 and lambda=2. The mixed term XY attains Delta_ij=v, and C_H=20, M_H=2 suffice. It vanishes at the two distinct primes (5,107), since 107²-20·5·107-5⁴-124=0. These constants were selected by a finite search over small integers, not by inserting an input prime as a parameter in a public rule.

The polynomial H1 is irreducible over Q[X,Y]. It is monic quadratic in Y, of discriminant 4(X⁴+100X²+124). Its value at X=0 is not a rational square. A rational square which is a polynomial is the square of a polynomial over Q, by cancelling coprime numerator and denominator. Thus the discriminant is not a square in Q(X); irreducibility over Q(X) and monicity yield irreducibility in Q[X,Y].

Moreover H1 does not divide any nonzero F(X)-G(Y) for univariate F,G over Q. For large positive real x the two branches are
```
Y_+(x)=10x+sqrt(x⁴+100x²+124)=x²+10x+O(1),
Y_-(x)=10x-sqrt(x⁴+100x²+124)=-x²+10x+O(1).
```
The bounded errors follow by rationalizing the difference between the square root and x². If H1 divided F-G then G(Y_+)=G(Y_-) on both branches. For G of degree n>=1 with leading coefficient c, when n is odd the difference has leading term 2c x^(2n). When n is even, the leading terms cancel but the difference has the nonzero term 20 n c x^(2n-1), as the two nth powers of x²+10x+O(1) and x²-10x+O(1) differ by that term. Lower terms of G grow at most as O(x^(2n-2)). A constant G forces F constant with F-G identically zero. This is a distinction of correspondence models, not a strict instance-set assertion about every conceivable way of selecting public dictionaries.

For a separate, tailored exercise of the large-prime branch use
```
H0(X,Y)=(Y-X²-u0)(Y+X²+X+u0)+(X-p0),
p0=1000003, u0=84.
```
Here u=4, v=2, lambda=2. The residual coefficients in positions (1,1),(3,0),(2,0),(1,0),(0,0) are 1,-1,-168,-83,-1007059. The XY term has Delta=v. It admits C_H=32, M_H=5, B=160. The primes p0 and q0=p0²+u0=1000006000093 obey H0(p0,q0)=0. On their two-vertex support there is no reverse directed edge for this label. With N=p0² q0, the bit length is 80 and p0>16LB=204800. The height-zero prime is p0, the relative height of q0 is 1, and the exact budget E=2+2=4 gives floor(N^(1/4))=p0. This artificial fixture deliberately encodes p0 in the displayed expression in order to verify the large-branch arithmetic. It is not evidence of a new infinite family of prime pairs or a computational benchmark.

Outside this theorem, arbitrary edges with no weighted gap, arbitrary leading faces, arbitrary groups of degree quotients, and disconnected support are not covered. No general decomposition or security inference is made.
