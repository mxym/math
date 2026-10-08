# Parent proof: forward repaired tails for d>=1001

Internal auxiliary result. This closes only the forward quarter of the
remaining dimensions, not the full real-rootedness conjecture.
Use definitions and Lemmas 8.1–8.3 of de Castro 2609.06096v1.

The constant exp(140) in Lemma 8.2 can be replaced by exp(30), uniformly for
5/54<=x<=2. Keep the source's coefficient bound C=5000 unchanged.
Let q=E(x)^(-1)<49/64. For n>=2 the Robbins/product estimate gives
 L_n(x) E(x)^(-n) <= (9/2)n^(-5/2),
since sqrt(2*pi)>12/5 and x>=5/54. At n=1 the normalized term equals q.
The source's elementary tail bound sum_(n>=2)n^(-5/2)<3/8 therefore yields
 sum_n L_n(x) E(x)^(-n) <49/64+(9/2)(3/8)=157/64.
For each a, the divisor sum is bounded by
 sum_(h>=1) phi(h)/h^2 q^((h-1)a)
 <=1+q/(2(1-q))<79/30.
Hence the total normalized connected-series mass is
 A< (157/64)(79/30)=12403/1920<13/2.
Lemma 8.1 now bounds the exponential coefficient by
 5000 exp(A)(A^3+6A^2+7A+1) n^(-5/2)
 <5000*687*exp(13/2)n^(-5/2)
 <2^22 exp(13/2)n^(-5/2)<exp(30)n^(-5/2).
No finite approximation of the infinite series is used.

All other constants in Proposition 8.4 remain valid. Its two relative errors
are now bounded by 36 exp(30)(19/20)^d and
108 exp(30)(77/100)^d. For d>=1001, using exp(1)<4,
(19/20)^14<1/2, (77/100)^3<1/2, 36<2^6,108<2^7,
these are respectively less than
 2^(6+60-floor(1001/14))=2^(-5),
 2^(7+60-floor(1001/3))=2^(-266).
Their sum is <1. Thus every forward repaired tail S_(d,r)(2-sqrt(3)) is
strictly positive for d>=1001 and 1<=r<=floor(d/4).

Remaining target: the complementary reverse coefficient range. The source's
finite d<=1000 certificate still requires proper attribution/reproduction if
used in a final complete proof; this note does not claim it was rerun.
