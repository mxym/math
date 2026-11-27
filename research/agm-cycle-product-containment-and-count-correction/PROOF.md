# The signed product of a periodic AGM recurrence

## 1. Statement and scope

Let K be a field of characteristic different from 2, let N>=1, and let
v_0,...,v_(N-1) be elements of K with v_i!=0 and v_i^4!=1, satisfying
the cyclic recurrence

    2 v_i v_(i+1)^2 = v_i^2+1,  with v_N=v_0.

Write w=prod_(i=0)^(N-1) v_i and D=2^N. There is an integer t with

    D w^2 - t w + 1 = 0 in K,  |t| <= 2 sqrt(D),
    t = 1+D (mod 4).                                              (1)

In characteristic p, the integer coefficients in this equation are
mapped to K; the bound and congruence on t are over the integers.
The t we construct is the trace of a particular normalized geometric
endomorphism, not necessarily a Frobenius trace. No supersingularity,
simple-cycle, or backward-lifting hypothesis is needed when the
nonsingular periodic v-tuple is already given.

For N>=2, the listed traces are exactly
t=(-1)^(k+1)(2k-1) for 1<=k<=floor(sqrt(2^N)+1/2). There is no rounding
tie, since sqrt(2^N) is either an integer or irrational. Therefore
(1) proves the product vanishing in [LM, §10, Conjecture 10.2, (33)].
The source's non-self-loop j-cycles with a periodic v-lift satisfy all
our assumptions, by (31) and (32) there. Our theorem presupposes the
v-tuple, and does not assert a stronger lifting or uniqueness theorem
at self-loops or double edges. It also covers repeated nonsingular
v-walks, without claiming they are simple j-cycles of the source.

## 2. Normalize the recurrence using ordered signed AGM parameters

Choose any nonzero a_0, put b_0=a_0/v_0^2, and define, for 0<=i<N,

    a_(i+1)=(a_i+b_i)/2,     b_(i+1)=a_i/v_i.                     (2)

All a_i and b_i are nonzero, and b_i/a_i=v_i^(-2): if this holds
at i, the recurrence gives

    a_(i+1)/a_i = (1+v_i^(-2))/2 = v_(i+1)^2/v_i,
    b_(i+1)/a_(i+1) = v_(i+1)^(-2),   b_(i+1)^2=a_i b_i.

In particular a_i^2!=b_i^2 because v_i^4!=1. The sign in (2) is
fixed by v_i, not freely chosen after the fact. Multiplying the
a-ratios around the cycle telescopes to w, so (a_N,b_N)=w(a_0,b_0).

Write E(a,b) for y^2=x(x-a^2)(x-b^2), with the elliptic identity O
at infinity. It is smooth because the three roots are distinct.
Scaling (x,y) by (a^(-2),a^(-3)) gives the Legendre parameter
lambda=b^2/a^2=v^(-4); its j-invariant equals j(v^4) by invariance
under lambda->1/lambda, matching (32) in [LM]. In particular the
shift in j-index convention in their theorem has no effect.

For a step (a,b)->(a',b') of (2), put h=ab. Define the pointwise
normalized isogeny by

    X=(x+h)^2/(4x),          Y=y(x^2-h^2)/(8x^2).                  (3)

Its codomain is E(a',b'), regardless of which square root b' of
h was specified in this step. This is because

    X-a'^2=(x-a^2)(x-b^2)/(4x),   X-b'^2=(x-h)^2/(4x),
    X(X-a'^2)(X-b'^2)=Y^2.

Equation (3) extends to the smooth projective curves. It takes O
to O, as the x-coordinate has a pole there, and hence is a
homomorphism. Its degree is two: the map x:E(a,b)->P^1 has degree
two, (x+h)^2/(4x) has degree two in x (h!=0), and the x-map on
E(a',b') has degree two. Its kernel is {O,T_0} with T_0=(0,0)
since precisely those two points are poles of X; the degree is
prime to the characteristic. Finally, for the invariant
differentials eta=dx/(2y) and eta'=dX/(2Y) on the two curves,

    dX/dx=(1-h^2/x^2)/4,
    (3)^* eta' = 2 eta.                                          (4)

In particular (3) fixes a sign convention, unlike a 2-isogeny
described only up to negation. Negating its y-coordinate would
change (4) and the trace convention.

Compose the N isogenies (3), then identify E(a_N,b_N) with
E(a_0,b_0) by (X,Y)->(X/w^2,Y/w^3). This isomorphism pulls the
target differential back to w times the source differential, so the
resulting endomorphism alpha has degree D and differential
multiplier D w. It kills the first T_0.

## 3. A fixed point of exact order four

Everything here can be checked over an algebraic closure of K.
For d^2=a^2-b^2 put

    P(a,d)=(a(a+d), a d(a+d)).

The point lies on E(a,b), and 2P(a,d)=T_a=(a^2,0).
For the latter, the line y=(a+d)(x-a^2) meets the cubic in
T_a and P(a,d) with multiplicity two: after factoring x-a^2
the intersection polynomial is [x-a(a+d)]^2. Thus the line is
tangent at P and the group law gives 2P=-T_a=T_a.
The points are distinct, and x(P), y(P) are nonzero, since a,b,d
are nonzero and (a+d)(a-d)=b^2.

The translation formula for T_0 is
(x,y)->(a^2 b^2/x, -a^2 b^2 y/x^2) when x!=0, obtained from the
line through (x,y) and T_0. Therefore

    P(a,-d)=P(a,d)+T_0.                                          (5)

Under (3) one has the exact, signed equality

    phi(P(a,d))=P(a',d'),         d'=(a-b)/2.                    (6)

Indeed d'^2=a'^2-b'^2, a'+d'=a, and the input satisfies
x+h^2/x=2a^2 and 1-h^2/x^2=2d/(a+d). Substitution gives the
output x=a'a and y=a(a^2-b^2)/4=a' d' a. The sign of d at
input has disappeared, as is also predicted by (5) and the kernel.

Starting from either choice of d_0, iterate (6). After the
closing scaling, the final point is P(a_0,d_N/w); the latter
square root equals d_0 or -d_0. Hence alpha(P)=P or P+T_0.
Because alpha kills T_0, the point Q=alpha(P) is fixed by alpha:
applying alpha again gives alpha(P) in either case. Equivalently,
choose d_0=(a_(N-1)-b_(N-1))/(2w) from the beginning, so that the
transported square root after closing is precisely this d_0.
This also shows Q is defined over K. It has exact order four by
(5) or (6) and 2Q=T_(a_0), distinct from T_0.

## 4. Integer trace, bound, and sign congruence

Use the 2-adic Tate module over an algebraic closure. Since the
characteristic is not two it is free of rank two. If M is the
matrix of alpha, det(M)=deg(alpha)=D by the Tate-module degree
formula (equivalently use the Weil pairing at every level).
Applying the same formula to 1-alpha yields
t=tr(M)=1+D-deg(1-alpha), an integer; the zero endomorphism has
degree zero. For integers n,m it likewise gives

    deg([n]-[m]alpha)=n^2 - t nm + D m^2 >= 0.

Taking all rational n/m shows that the real quadratic
u^2-tu+D is nonnegative, whence |t|<=2 sqrt(D). This norm argument
does not require alpha to be Frobenius.

Cayley-Hamilton yields alpha^2-[t]alpha+[D]=0 in End(E):
the Tate module action is faithful, since a nonzero geometric
endomorphism has finite kernel and cannot kill every 2-power
torsion point. Evaluate the identity at the fixed point Q of
exact order four. It gives [1-t+D]Q=O and hence t=1+D mod 4.
Equivalently, the mod-4 matrix in a basis starting with Q has
first column (1,0), so its trace is 1 plus its determinant
modulo four. For N>=2 the determinant is zero mod four; for N=1
it is two. Applying the same endomorphism identity to the
invariant tangent line, and using the multiplier D w from (4),
gives (D w)^2 - t(D w)+D=0. Division by the invertible scalar D
gives (1). This argument is valid directly in odd positive
characteristic, so no specialization of a rational identity
or lift of periodic solutions is needed.

## 5. The reverse assertion and the fixed-prime count are false

For N=3 the permitted traces are 1,-3,5. They are distinct
as elements of every field of odd characteristic (their pairwise
differences have absolute values four or eight). If w satisfies

    8w^2 - 5w + 1 = 0,                                           (7)

then w!=0 and the actual integer t of alpha must be 5,
by subtracting (1) from (7). Put beta=alpha-[2].
The degree quadratic gives deg(beta)=8-2*5+4=2, and substitution
into alpha^2-[5]alpha+[8]=0 gives beta^2-beta+[2]=0.
Consequently beta^3=-beta-[2]=-alpha.

The kernel of alpha has order eight and is cyclic. Indeed
alpha kills T_0 and fixes 2Q=T_(a_0), the other nonzero generator
of E[2]. Thus its kernel has exactly one nonidentity point of
order two; a finite abelian 2-group with that property is
cyclic. The degree-two separable beta has its kernel inside
ker(alpha) because beta^3=-alpha. Its kernel, of order two, is
therefore the kernel {O,T_0} of the first step. Two separable
isogenies with the same kernel have isomorphic target curves,
so the first step is a self-loop in j because beta has target
E(a_0,b_0). A simple length-three j-cycle cannot contain it.
The proof includes characteristic seven, where (7) has a
double algebraic root.

The excluded roots are real possibilities for nonsimple walks.
The nonsingular fixed points of the v-recurrence solve
2v^2+v+1=0, since 2v^3-v^2-1=(v-1)(2v^2+v+1).
These roots are nonzero and none have v^4=1 in characteristic
different from two. Tripling that fixed walk gives
w=v^3=(1-v)/4, which satisfies (7); conversely this affine
change maps the two quadratics onto each other. Thus (33)
includes roots from a tripled self-loop, not roots from a
simple 3-cycle. This disproves the reverse/root-realization
sentence after (33), independently of graph counting conventions.

The fixed-prime assertion that the number of N-cycles is
2 k_M also fails outright: the prime p=7 is allowed in
[LM, §2], and the supersingular 2-isogeny graph in characteristic
seven has only one vertex. For completeness over an algebraic
closure take the Legendre form of any elliptic curve and apply
the standard supersingularity criterion that its Legendre Hasse
polynomial vanish. At p=7 it is

    sum_(i=0)^3 binom(3,i)^2 lambda^i
       = (lambda+1)(lambda-2)(lambda-4)   in F_7[lambda].

All three roots -1,2,1/2 give the same j=1728 (read in F_7).
Hence there are no simple length-three j-cycles at this
admissible prime, whereas 2 k_M=6. No convention about
orientation or base point can change zero. These corrections
are separate from the affirmative boxed containment and are
not a general cycle enumeration.
