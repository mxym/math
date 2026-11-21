# All-height exponent restrictions on three-label factorization components

For a genuine three-label exceptional autonomous component in [Bożek's graph](https://arxiv.org/abs/1909.09900v1), use the [exact normal form](EACThreePrimeCurves.md)
    N=p+q^d,  N-q=p^e r^f,  N-r=p^b q^c,
where p,q,r are distinct odd primes, r>p,q, d>=2, b>=1, 0<=c<d, f>=1 and e+f>=2. The bounds below are uniform, including when the smallest prime is of subpolynomial size and the exponents vary. They require no linear form or integral curve estimates. In particular, the complete first-power branch has a pure-power last row, and the repeated-power branch has restrictions invariant under growing exponents.

### Power gaps in every branch

Set D=d-c and A=q^D-p^b=(r-p)/q^c. Then A is positive and even. The inequality pr<=p^e r^f=N-q holds: for e>=1 it is immediate, and for e=0 one has f>=2 and r>p. Substitution of r=p+q^c A gives (p-1)A<p^b. Because A>=2, b=1 is impossible. In particular b>=2 and
    N-q=q^c(p^b+A)+p-q < 2q^c p^b.
The last step uses 1/(p-1)+p^(1-b)<=1/2+1/3<1.

Write g=gcd(b,D), n=b/g and m=D/g, so q^m>p^n. Their difference is a positive even integer. Taking the difference of their g-th powers shows A>=2g p^(b-n). Since r>q^c A, we have
    p^e r^f > (2g)^f q^(cf) p^(e+f(b-n)).
Consequently `e+f(b−n)<b`, in particular `e<n`. When `f≥2` this forces `g=1`, since `g≥2` would give `f(b−n)≥b`. In either case `b` does not divide `d−c`: for `f=1` use `1≤e<n`, and for `f≥2` use `g=1<b`.

For f>=2 expansion of r^f=(p+q^c A)^f also gives p^e r^f>=2f q^c p^(e+f-1), so e+f-1<b. When c=0 the stronger e+f<b follows if we suppose e+f>=b: then p^e(p+A)^f >= p^b+f A p^(b-1), whereas N-q=p^b+A+p-q, and (f p^(b-1)-1)A>p-q. Finally gcd(f,b-e,c)=1 for every f>=2. If k>1 divides those three exponents, subtract the last two rows and divide by p^e to get
    (r^(f/k))^k - (p^((b-e)/k)q^(c/k))^k=(r-q)/p^e,
a positive difference strictly smaller than r. The difference of the k-th powers is at least r^(f(k-1)/k)>=r, a contradiction. Here b-e is positive by the earlier inequality. The same elementary comparison r^f-q^f>p also gives f<d for f>=2.

### The first-power branch has no q factor in its last row

Assume f=1, hence e>=1. Exact elimination gives
    (p^e-1)A=p^b-E/q^c,  E=p(p^e-1)+q.
Write b=ke+s, 0<=s<e, k>=1 by e<b. Put B=p^e-1 and S=p^(b-e)+p^(b-2e)+...+p^s, so p^b=B S+p^s. Thus
    B[q^c(A-S)+p]=q^c p^s-q.                                     (1)

Suppose c>=1. Then r≡p modulo q and the second row implies q|B. In particular q<=B. Consider the two possibilities for q^c relative to p. Equality is impossible for distinct primes.

- If q^c>p, oddness gives q^c>=p+2. Both p^s and E/q^c lie strictly between 0 and B, the latter because E/B=p+q/B<=p+1. Therefore A=S+(p^s-E/q^c)/B and integrality force A=S and E=q^c p^s. Reducing modulo p forces s=0, because E≡q modulo p. It follows that q^D=p^b+A=1+p^e+...+p^(ke). Since q is odd and divides p^e−1, the elementary lifting-the-exponent formula gives v_q(1+p^e+...+p^(ke))=v_q(k+1). Thus q^D<=k+1. The geometric sum is strictly larger than k+1, a contradiction.
- If q^c<p, then 0<=q^c p^s-q<B, because q^c>=q and q^c p^s<=(p-2)p^(e-1). Equation (1) forces q^c p^s=q, hence c=1 and s=0. The bracket then reads q(A-S)+p=0, which would make q divide p. This is impossible.

Therefore c=0 for every genuine f=1 component at all heights. This eliminates the whole varying-exponent mixed last row. Equation (1) becomes q≡p^s mod B. If q<B, both are strictly between 0 and B and equality q=p^s is impossible for either s=0 or s>=1. As B is even and q cannot equal the odd number p^e (distinct primes or an actual power), q>p^e. From A<p^b/(p-1) we have q^d<p^b p/(p-1), so b>=ed since q>p^e. Equality b=ed would yield A=q^d-(p^e)^d>=2d p^(b-e). The identity for A instead gives A<p^b/B<=1.5p^(b-e). Thus b>=ed+1.

In particular in the f=1 branch p is always the smaller of the first two primes, q>=p^e+2, and the entire residual system is
    N=p+q^d,
    N-q=p^e r,
    N-r=p^b,
    (p^e-1)(q^d+p)=p^(e+b)-q,
    q≡p^(b mod e) mod (p^e-1),  b>=ed+1.
This says exactly which branch remains. It does not exclude that branch, the f>=2 cases, or any Goldbach exceptions. The earlier [fixed-signature proof](EACThreeSubpower.md) can now bypass its geometry for `c≥1,f=1`. The [bounded-label result](EACRepeatedFixedLabel.md) separately uses logarithmic forms and integral points for `f≥2`.

### Parallel work and scope

A separate elementary residue-case proof independently obtained the same `f=1` orientation and mixed-row exclusion. This note records the shorter quotient proof and further exponent restrictions. [Kelanemer (SSRN 7274460, revised September 2026)](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) announces a wider terminal-component argument under the Goldbach-counterexample hypothesis. The accessible index does not establish its proof or whether it contains the particular exponent restrictions here. The present conclusions apply to genuine components without assuming their centers are unrepresented; no priority or resolution of the conjecture is claimed.
