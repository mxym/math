# Arbitrarily slow critical covering excess in Banach nonembedding obstructions

7 October 2026. Secondary research proof draft, extending entry 003.

## Theorem

Let h:[1,infinity)->[1,infinity) be nondecreasing and tend to infinity.
There is a numerical constant C, independent of h and the Banach space, such
that every infinite-dimensional real Banach space contains a countable
compact set K with all the following properties:

- upper box dimension zero;
- Assouad dimension exactly two;
- doubling constant at most 1+5*76800^8;
- no bi-Lipschitz embedding into any finite-dimensional normed space;
- for every x in K and 0<r<R,

    N_r^K(B_K(x,R)) <= C (R/r)^2 h(R/r);

- nevertheless there is no finite critical exponent-two covering constant:

    sup_(x,0<r<R) N_r^K(B_K(x,R))/(R/r)^2 = infinity.

One can take C=350000. The last two properties say the excess above the planar
covering rate can be forced to diverge arbitrarily slowly, while remaining
necessarily unbounded for this construction. This does not show that Assouad
dimension two is the smallest possible nonembedding dimension, and it does
not exclude some other obstruction having a genuine exponent-two bound.

## Controlled scale choice

Use exactly the scale-flexible sheet construction S(rho) from entry 003.
Its inherited nonembedding proof permits every schedule with
rho_(j+1)<=rho_j/1000. Its refined intrinsic covering estimate is

  N_r^S(B_S(x,R)) <= 1089 (R/r)^2 5^m,
  m=#{j:r/16<rho_j<=R}.                                (1)

Choose rho_1=2^(-10). For every n>=1 choose T_(n+1)>=1 with
h(T_(n+1))>=5^(n+1). Choose nondecreasing dyadic integers Q_n such that

  Q_n>=1024,     Q_n>=2^n,     Q_n>=128 T_(n+1),

and put rho_(n+1)=rho_n/Q_n. All rho_j are reciprocal dyadic integers.
The adjacent ratios tend to infinity, which independently gives Assouad
dimension two exactly as in entry 003.

If the active interval in (1) has length m>=2 and starts at index a, then

  R/r > rho_a/(16 rho_(a+m-1))
       = (Q_a ... Q_(a+m-2))/16 >= Q_(m-1)/16.

The final inequality follows from a>=1, Q_n nondecreasing and every factor
at least one. Thus (R/r)/8>T_m and h((R/r)/8)>=5^m.
For m<=1 the bound 5^m<=5 h(max{1,(R/r)/8}) is automatic. Therefore

  N_r^S(B_S(x,R))
     <=5445 (R/r)^2 h(max{1,(R/r)/8}).                  (2)

All constants are independent of h. This is a quantitative refinement of
003, rather than merely its statement that every exponent s>2 is available.

## Exact finite packing witnesses for nonattainment

For j>=1 put q_j=1/rho_j, an integer. Let the planar points be

  p_(k,l)=((k+1/3)rho_j,(l+1/3)rho_j),
  0<=k,l<q_j.

At each level v<=j the y-coordinate belongs to an open horizontal strip,
since rho_v/rho_j is an integer and (l+1/3)/(rho_v/rho_j) is not an integer.
Choose that strip's color i_v(p). Over each p include all 2^j sheet points
with vth coordinate either zero or rho_v e_(v,i_v(p)), independently.
Call their finite set P_j. Then

  |P_j|=q_j^2 2^j,
  P_j subset B_S(o,2),
  distances between distinct points of P_j are at least rho_j.             (3)

The radius assertion follows from the planar square [0,1]^2 and
sum rho_v^2<=rho_1^2/(1-10^(-6))<1. Different planar grid points are
rho_j-separated; points over the same planar point differing in a sheet
coordinate are separated by some rho_v>=rho_j. These checks are rational
and exact (squared distances may be used). The finite object has an exact
compressed specification, although its cardinality need not be practical.

Choose the finite nonembedding witnesses X_j in entry 003 and enlarge each
by P_j and o. Enlargement cannot remove nonembedding. The qualitative
Dvoretzky transfer T_j into the ambient Banach space is normalized to

  ||u||_2 <= ||T_j u|| <= 2||u||_2.

Thus T_j(P_j) lies in the radius-four ball about T_j(o), and is
rho_j-separated. At covering radius rho_j/3, any ball, even one centered
outside this cluster, can contain at most one of its points. For a
translated and scaled cluster with scale tau_j, take

  R_j=4 tau_j,       r_j=tau_j rho_j/3.

The corresponding K-ball therefore satisfies

  N_(r_j)^K(B_K(x_j,R_j)) >= q_j^2 2^j,
  N_(r_j)^K(B_K(x_j,R_j))/(R_j/r_j)^2 >= 2^j/144.       (4)

Here x_j is the image of o and belongs to K. Additional points and centers
elsewhere in K cannot defeat a packing bound. Equation (4) proves the
critical exponent-two content is unbounded.

## Transfer of the upper gauge through sparse assembly

Let Y_j=T_j(X_j). Recenter the source balls used to cover the preimage of a
Y_j-ball at source radius r/4, precisely as in 003. Equation (2) gives,
with A0=5445*16=87120, the uniform cluster estimate

  N_r^(Y_j)(B_(Y_j)(y,R))
     <= A0 (R/r)^2 h(max{1,R/(2r)})     (0<r<R).       (5)

Place the translated and scaled clusters C_j within
B(a_j v,a_j/100), with a_(j+1)<=a_j/2. Also require

  a_j<=exp(-j^2),     a_j<=M_j^(-j),
  M_j=sum_(i<=j)|X_i|.

Let K={0} union the clusters. Entry 003's separation argument gives
||p-q||>=97 a_i/200 for p in C_i,q in C_j,i<j. Its compactness,
zero-upper-box-dimension, universal doubling and nonembedding proofs
apply unchanged. Adding P_j only changes the finite cardinalities M_j.
The Assouad upper bound two still follows from the adjacent sheet ratios
Q_j tending to infinity and the same geometric assembly estimate in 003;
it does not rely on h being subpolynomial. Equation (4) gives the matching
lower bound two directly.

For completeness, (5) yields a universal quantitative K-bound. Put t=R/r.
If B_K(x,R) meets a cluster with a_i>5R, separation prevents it meeting
another cluster or zero. Its intersection lies in a C_i-ball of radius
2R; (5) covers this by at most

  4 A0 t^2 h(t) =348480 t^2 h(t).

Otherwise all intersected cluster scales satisfy a_j<=5R. Clusters with
a_j<=r/4 are covered by one radius-r ball at zero. For every remaining
cluster, diameter(C_j)<=a_j/50. If its diameter is at most r, one ball
suffices. Otherwise (5) gives a cover costing at most

  (A0/2500)(a_j/r)^2 h(max{1,a_j/(100r)}).

The h-factor is at most h(t), since a_j<=5R. For a_j>r/4, the one-ball
cost is at most 16(a_j/r)^2 h(t). Sum over the geometrically decreasing
scales, using

  sum_(r/4<a_j<=5R)(a_j/r)^2 <= (100/3)t^2.

Including the tail ball, the second case costs at most

  [1+(16+A0/2500)*100/3] t^2 h(t) <1696 t^2 h(t).

The advertised C=350000 handles both cases.

## Scope

The dimensional and nonembedding dependency is the scale-flexible source
argument already checked in 003. The extra finite packing (3) is an exact
certificate of critical-covering nonattainment, not a standalone finite
certificate of nonembedding into every dimension or of Dvoretzky transfer
into an arbitrary Banach space. Upper box dimension zero comes from sparse
*global cluster placement*. Assouad dimension and its critical covering
content come from *within-cluster scale ratios and branching*. They must
not be interchanged.

Primary context: OpenAI family 098, pinned at
adc7f1241b42e322a6451854ab7e4b4c146bf78a, supplies the sheet crossing
nonembedding argument. Naor and Neiman, Assouad's theorem with dimension
independent of the snowflaking, explains why doubling gives embeddings after
snowflaking but does not ensure a bi-Lipschitz embedding of the original
metric. This refinement neither changes that theorem nor claims a new
embedding threshold.

https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-doubling-Hilbert-subset-with-no-finite-dimensional-bi-Lipschitz-embedding-September-25-2026/build/main.tex
https://web.math.princeton.edu/~naor/homepage%20files/assouad-N%28K%29.pdf
