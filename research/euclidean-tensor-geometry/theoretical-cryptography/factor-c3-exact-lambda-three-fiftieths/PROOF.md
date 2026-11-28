# Proof

Put (delta=3/50).  All logarithms in normalized inequalities are to base
(R).  Soft-O factors below are powers of (log(2R)).

## 1. C3 normal form from one exact lambda value

Let (R=pqr), where (p<q<r) are odd primes and (R) is Carmichael.
Korselt's criterion says that (R) is squarefree and every (p_i-1)
divides (R-1).  Define
[
 g=gcd(p-1,q-1,r-1),qquad
 p=1+ga, q=1+gb, r=1+gc.
]
The integers (a<b<c) are pairwise coprime.  For example, if (d) divides
(a) and (b), then (gdmid p-1,q-1).  Reducing
(p-1mid qr-1) modulo (gd) gives (requiv1pmod {gd}), so (dmid c).
This contradicts the maximality of (g) unless (d=1).  Hence
[
 Lambda:=lambda(R)=gabc,qquad L:=Lambda/g=abc.
]

Let (S=(R-1)/Lambda).  Expanding (R) gives
[
 S=g^2+gleft(rac1a+rac1b+rac1cight)
       +left(rac1{ab}+rac1{ac}+rac1{bc}ight).
]
Since (gge2), (age1,bge2,cge3), one has
(g^2<S<(g+1)^2).  Thus
[
 g=lfloorsqrt Sfloor,quad
 J=S-g^2,quad E=LJ,quad x=g/J
]
are all recovered from (R,Lambda).  The exact identities are
[
 E=(a+b+c)+g(ab+ac+bc),                                      	ag{1}
]
[
 J=rac ga+rac gb+rac gc+
   rac1{ab}+rac1{ac}+rac1{bc}.                         	ag{2}
]
They imply
[
 x<a<rac92x,qquad a+b+c<rac{3L}{x^2},qquad
 L<rac R{g^3}.                                              	ag{3}
]
For the first upper bound use
(J<3g/a+3/a^2le9g/(2a)), since (ga=p-1ge2).

We also need a two-sided constant comparison.  Pairwise coprimality and
oddness of the primes force (g) even, and therefore
[
 1<rac R{g^3L}
 =left(1+rac1{ga}ight)
  left(1+rac1{gb}ight)
  left(1+rac1{gc}ight)lerac{35}{16}.                 	ag{4}
]
Consequently, if
(gamma=log_R g) and (ell=log_R L), then
[
 ell=1-3gamma+O(1/log R),                                 	ag{5}
]
with an absolute effective constant.

## 2. A rigorous two-modulus LLL lemma

Let
[
 A=ab,qquad f(X)=X+gL.
]
Then
[
 Amid L,quad rmid R,quad gcd(A,r)=1,quad f(A)=Ar.       	ag{6}
]
The coprimality follows because the prime (r) is larger than both
(a) and (b).

Fix a dyadic bucket (Wle A<2W) and put (X_0=2W).  For fixed integers
(tge2) and (0le m_R,m_L<t), use the (t) polynomials
[
 h_i(X)=f(X)^i R^{(m_R-i)_+}L^{(m_L-i)_+},
 qquad 0le i<t.                                             	ag{7}
]
Embed the coefficient vector after replacing (X) by (X_0Z).  Because
(f) is monic, the basis is triangular and has determinant
[
 X_0^{t(t-1)/2}
 R^{m_R(m_R+1)/2}
 L^{m_L(m_L+1)/2}.                                            	ag{8}
]
At the true (A), every row is divisible by
[
 r^{m_R}A^{m_L}.                                              	ag{9}
]
Indeed, the factor (f(A)^i=A^ir^i) supplies the first (i) copies of
each factor, and the powers of (R) and (L) supply any deficit.
Equation (6) lets the two divisibilities be multiplied.

LLL returns a nonzero lattice polynomial (H) with
[
 |H(X_0Z)|_2le
 2^{(t-1)/4}det(mathcal L)^{1/t}.
]
Since (0<A/X_0<1),
[
 |H(A)|lesqrt t,|H(X_0Z)|_2.                             	ag{10}
]
On the other hand,
[
 r^{m_R}A^{m_L}>
 left(rac{gL}{2W}ight)^{m_R}W^{m_L}.                    	ag{11}
]
Define
[
 	au=log_R W,quad ell=log_R L,quad
 mu=log_Rrac{gL}{2W}.
]
Taking (m_R/t) close to (mu) and (m_L/t) close to
(	au/ell), comparison of (8)--(11) has leading positive gap
[
 rac t2left(mu^2+rac{	au^2}{ell}-	auight)log R.  	ag{12}
]
Therefore, for every fixed (eta>0), if
[
 G(gamma,	au):=mu^2+rac{	au^2}{ell}-	au>eta,         	ag{13}
]
then a fixed sufficiently large (t=t(eta)) makes (10) strictly
smaller than (9) for all sufficiently large (R).  Divisibility forces
(H(A)=0).  Deterministic factorization of (H) over the integers lists
(A), after which (6) gives (r).  False roots are rejected by exact
division and primality tests.

This argument is fully one-variable and uses only the standard proved
LLL length bound.  It has no algebraic-independence heuristic.  The
(O(1/log R)) effects from (4), the factor 2 in the bucket, the
integer roundings of (m_R,m_L), and the LLL constant are absorbed by
first fixing (t), then taking an effective constant threshold for
(R).  Inputs below that threshold can be factored by trial division;
this changes only the absolute constant.  Instead of computing real
logarithms, enumerate all (m_R,m_Lin{0,ldots,t-1}) for every
dyadic bucket and validate every output.  There are only
(O(log R)) buckets and a constant number of lattices per bucket.

## 3. The uniform 3/50 parameter margin

First, if (xle R^{2delta}), scan the progression
(1+ga) for the integer interval (x<a<9x/2).  A block polynomial of
degree (B=lceilsqrt Tceil), evaluated at the (O(sqrt T)) block
origins by monic product/remainder trees over (mathbb Z/Rmathbb Z),
finds a nontrivial gcd in
[
 O(R^delta(log(2R))^{O(1)})                                	ag{14}
]
bit operations.  Monic reversal and Newton inversion use no nonunit
division, so the composite modulus causes no gap.  A full block gcd is
resolved by recursively splitting that block.

Assume henceforth (x>R^{2delta}).  The cubic search from (1) enumerates
[
 s=a+b+cequiv Epmod g,qquad 0<s<3L/x^2.                   	ag{15}
]
For each (s), set (e_2=(E-s)/g) and test whether
[
 T^3-sT^2+e_2T-L                                             	ag{16}
]
has three positive integer roots.  Discrete differences split the
positive axis into at most three monotone intervals, so this test is
bit-polynomial.  The number of candidates is
[
 Oleft(1+rac{L}{gx^2}ight)
 =Oleft(1+rac{R}{g^4x^2}ight).                          	ag{17}
]
Thus, if (gge R^{7/40}), (17) is (O(R^delta)).

It remains to handle
[
 R^{3/25}<g<R^{7/40},qquad x>R^{3/25}.                      	ag{18}
]
Choose a dyadic (U) within a factor 2 below
[
 U_*=minleft{rac{g^3}{R^{3/25}},
                 rac{R^{47/50}}{g^4}ight}.              	ag{19}
]
Run the lemma of Section 2 on every bucket (Wle Ale U).
Let (gamma=log_Rg).  Ignoring the (O(1/log R)) terms already
accounted for in the lemma, every such bucket satisfies
[
 	aule	au_c(gamma):=
 min{3gamma-3/25, 47/50-4gamma}.                       	ag{20}
]
Put (ell_0=1-3gamma), (mu_0=1-2gamma-	au), and
[
 G_0=mu_0^2+	au^2/ell_0-	au.
]
On the range (18), (mu_0ge1/3) and
(z=	au/ell_0le3/4).  Hence
[
 rac{partial G_0}{partial	au}
 =-2mu_0+2z-1<0.                                           	ag{21}
]
It suffices to use equality in (20).  The two cutoffs meet at
[
 gamma_*=rac{53}{350}.
]
On the left branch, differentiating along
(	au=3gamma-3/25) gives
[
 rac{dG_0}{dgamma}
 =-10mu_0-3(1-2z-z^2)<0.
]
On the right branch, along (	au=47/50-4gamma),
[
 rac{dG_0}{dgamma}
 =4mu_0+4-8z+3z^2>0.
]
The displayed range bounds prove both strict signs.  Therefore the
minimum is at the meeting point, where
[
 (	au,ell_0,mu_0)=
 left(rac{117}{350},rac{191}{350},rac{127}{350}ight)
]
and
[
 G_0=rac{50339}{23397500}>0.002.                           	ag{22}
]
For sufficiently large (R), all actual buckets retain, say,
(G>0.001), so Section 2 recovers every (Ale U).

## 4. The two post-failure branches

Suppose the LLL buckets find no validated (A).  Then (A=ab>U).

If the first term of (19) is the smaller one, then
(Ugg g^3/R^{2delta}).  From (2),
[
 0<J-g/a<2g/b+2/(ab)+1/b^2.
]
Since
[
 a-x=rac{ax}{g}(J-g/a),qquad
 a<rac92x,qquad b=A/a>rac{2U}{9x},
]
one obtains, for the large-input range,
[
 0<a-x<100,rac{x^3}{U}=O(R^{2delta}).                    	ag{23}
]
(The harmless constant can be enlarged for the finite threshold.)
Apply the same batched progression search as in (14) only to the
interval (23); its cost is (O(R^deltaoperatorname{polylog}R)).

If the second term of (19) is the smaller one, then
(Ugg R^{1-delta}/g^4).  Because (a+b+c<3c=3L/A), the
residue-class search (15) now has
[
 Oleft(1+rac{L}{gU}ight)=O(R^delta)                    	ag{24}
]
candidates.  Test them with (16).  This proves the squarefree theorem.

## 5. Multiplicities and an even part

Let the odd part of the input be
(n=prod_{pmid R}p^{k_p}).  For a Carmichael radical, no prime
(pmid R) divides (q-1) for another (qmid R), because
(q-1mid R-1) while (R-1equiv-1pmod p).  The local exponent
formula therefore gives
[
 D:=gcd(n,lambda(N))=n/R.                                  	ag{25}
]
The odd part of (lambda(N)/D) is the odd part of (lambda(R));
only its two-adic exponent may have been enlarged by the component
(2^e).  Enumerate the (O(log N)) possible two-adic exponents,
run the squarefree algorithm, and retain only a complete prime-power
factorization whose product is (N) and whose exact Carmichael value
is the supplied (lambda(N)).  The true candidate occurs, while exact
validation excludes every false candidate.  Equation (25) also reveals
all multiplicities once the three odd primes are known.

All integer roots, primality claims, products, and Carmichael values in
the algorithm are checked exactly.  The result is unconditional and
deterministic.
