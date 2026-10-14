# Complete Caccetta–Häggkvist written attempt

Author: Yongxian Zhang, South China University of Technology; mxymmxym1@gmail.com; ORCID0009-0000-3864-3536.
All rights reserved. No funding. OpenAI AI assistants assisted this internal ordinary written research.

## C0 Original complete scope and activation

The sole active breadth target is the entire [CH0/CH1 map](CACCETTA_HAGGKVIST_THEOREM_MAP.md): all finite digraph orders and every positive minimum-outdegree parameter. Antiparallel arcs are permitted. Every proposed reverse example must be an actual binary loopless adjacency matrix and must have no directed cycle through the conjectured length bound.

Current primary-source screening is recorded in [the source record](CACCETTA_HAGGKVIST_SOURCES.json). No complete resolution was located. The source-reading bounds are explicit; original1978 full text was not retrieved. Known small-degree, regular and path results do not become new major outcomes.

Map prepared before mathematical phase. Source-phase start04:02:48UTC; map/commit preservation excluded. No mathematical solution or witness at this checkpoint.

## C1 Planned exact full-domain routes

Work from the full binary out-regular formulation, using closed-walk traces, determinant/cycle expansions and actual row-degree constraints; any analytic relaxation must retain a proof of realizability before it can refute the conjecture. In parallel within this single role, inspect exact shortest-cycle/vertex deletion and directed-distance constraints that apply to every hypothetical counterexample. No graph-class theorem or finite experiment is an acceptance substitute.


## C2 Complete trace, entry and determinant formulation

Choose exactly r outgoing arcs per row and then a sink strongly connected component, as in CH5–CH6. Write A for its actual binary adjacency matrix and P=A/r. This reduction preserves the complete target and imposes no equality of indegrees. P is nonnegative, has row sum1, diagonal0, and every nonzero entry is1/r.

For every j>=1, tr(A^j) is the exact nonnegative number of length-j closed directed walks. Absence of directed cycles of length<=k is therefore equivalent to tr(A^j)=0 for every1<=j<=k. A shortest closed walk is a simple cycle. This formulation neither replaces actual arc counts with expected counts nor admits fractional matrices as reverse witnesses.

All entries of P^j are at most1/r: row-stochasticity and the bound on the last factor prove this by induction. Consequently0<=tr(P^j)<=n/r for every j. The eigenvalues satisfy lambda1=1, |lambda_i|<=1, and, by unitary triangularization,
sum_i |lambda_i|^2 <= ||P||_F^2=n/r.
Every one of these constraints is necessary. They do not recover the binary matrix.

For |z|<1,
log det(I-zP)=-sum_{j>=1} tr(P^j)z^j/j.
Thus girth>=g gives det(I-zP)=1+O(z^g), while det(I-P)=0. The determinant's exact combinatorial expansion sums over vertex-disjoint directed cycle collections, with sign(-1)^(number of cycles). This standard identity does not give one sign for every coefficient.

## C3 Exact obstruction to a spectrum-only proof

This is an inadmissible spectral relaxation, explicitly not a CH reverse graph.

Let a be the unique positive root of
16a^3+(1+2a)^3/4096=1.
The defining expression is strictly increasing for a>0 and has opposite signs at39/100 and2/5 after subtracting1. Put
epsilon=(1+2a)/64,
tau=1-4a^2+64epsilon^2,
delta=sqrt(tau/128).
Use the195-entry conjugation-invariant spectral list
1; a+i sqrt(3)a,a-i sqrt(3)a;
64 copies of -epsilon;64 pairs i delta,-i delta.

Its first three power sums are exactly
p1=1+2a-64epsilon=0,
p2=1-4a^2+64epsilon^2-128delta^2=0,
p3=1-16a^3-64epsilon^3=0.
It has a simple Perron value1, with all other moduli below1. The exact interval bounds give
0<9/25<tau<17689/40000,
delta^2<17689/5120000<(3/50)^2,
epsilon<9/320,
sum |lambda|^2=2+4a^2+128epsilon^2<2193/800<3.
For every j>=4, the real power sum obeys
p_j >= 1-2(4/5)^4-64(9/320)^4-128(3/50)^4
=18339950063/102400000000>0.
An upper triangle bound also gives p_j<2 for every j>=4, so the entry-derived necessary trace bound p_j<=n/r=3 is respected. The list therefore passes the vanishing low traces, all subsequent trace signs, Perron and squared-energy conditions at formal n195,r65, yet violates the hoped-for spectral energy lower bound>3.

It cannot be the spectrum of A/65 for any integer adjacency matrix A. The primitive cubic
21848a^3+4a^2+2a-1365
has no root modulo11 (its values at0,...,10 are10,7,2,7,1,7,4,4,8,6,10); its leading coefficient is nonzero modulo11, so it is irreducible over the rationals. The fourth power sum reduces modulo this cubic to
962318435/954670208
-(473058235/477335104)a
-(7268495/119333776)a^2.
This nonconstant degree-at-most-two expression is irrational because a has degree3. Hence65^4 p4 cannot be the integer tr(A^4). There is no actual binary witness here. The obstruction shows exactly why a proof from the listed spectral constraints alone cannot close CH.

## C4 Actual strong/out-regular positive-coefficient control

Take two copies of the seven-vertex circulant with arcs i->i+1,i+2 modulo7. In the first copy replace0->1 by0->8; in the second replace7->8 by7->1. The resulting14-vertex graph is actual, loopless, strongly connected and2-out-regular. Its girth is4, so it satisfies CH's length bound7.

Each original copy has seven4-cycles: a length-four sequence with three2-steps and one1-step. Removing the stated1-step removes exactly one, leaving six in each copy. There are36 vertex-disjoint pairs of these4-cycles. A cycle using the two crossed arcs has length at least8; at length8 the two internal three-step paths are uniquely the all2-step paths. There is exactly one such8-cycle. Therefore the z^8 coefficient of det(I-zA) is36-1=35>0. The exact verifier confirms this both by Newton identities using all14 closed-walk traces and independently by summing all3003 order-eight principal determinants.

Thus even after the complete strong/out-regular reduction, nonconstant determinant coefficients need not all be nonpositive. This actual graph is a shortcut control in an already known small-degree regime, not a new CH theorem or counterexample.

## C5 Actual distance-layer control

Use vertices {v},A={a0,a1,a2,a3},B of size3,C of size4,D of size4. Add v->A, the directed4-cycle on A, complete arcs A->B,B->C,C->D, and, from each D-vertex, arcs to v,a0,a1,a2. Every vertex has exactly four outgoing arcs, and the16-vertex graph is strongly connected. No directed cycle of length below4 exists; the A-cycle gives girth4. It satisfies CH with ceil(16/4)=4.

At v the exact distance layers have sizes1,4,3,4,4. In particular the second layer has size3<r4, and the radius-three ball has size12<1+3r=13. The global exact girth is confirmed independently by BFS and closed-walk traces0,0,0,580. A proof cannot assume every layer, or every root's cumulative ball, has the conjectured growth. A suitable vertex or coupled global estimate would still need proof.

## C6 Random mapping and remaining full-domain obligation

Independently choose one outgoing neighbor at each vertex using the row probabilities P. Every resulting finite functional digraph has a directed cycle. Distinct cycle events that can occur together are vertex-disjoint. Inclusion–exclusion over them recovers det(I-P)=0. More generally, retain each chosen row arc with probability z and otherwise kill the row; then det(I-zP) is the probability that no directed cycle survives, for0<=z<=1. This proves determinant nonnegativity on this real interval, not coefficientwise nonpositivity.

The hoped-for upper bound on the total cycle contribution at n<=r(g-1) is still unproved. The cap P_ij<=1/r and low-trace identities alone do not provide it. Row/arc realizability and cycle overlap must remain in the argument; no inference from the inadmissible spectrum in C3 is adopted.

## C7 Global minimal-counterexample deletion constraint

Suppose a CH counterexample exists, and choose one with the smallest vertex count across all original parameters. After choosing exact r outgoing arcs, a proper sink component would itself violate CH at smaller order; hence an actual strong r-out-regular minimum-order counterexample may be chosen. Let its girth be at least g, put L=g-1, and write n<=rL.

For any nonempty proper S, the smaller induced graph D-S obeys the full CH bound by minimality. If it has minimum out-degree d'>0, then n-|S|>=d'L+1; if d'=0 the same conclusion d'<=floor((n-|S|-1)/L) is trivial. Therefore some v outside S satisfies
r-|N^+(v) intersection S| <= floor((n-|S|-1)/L).
This is a conditional exact covering constraint, not a new proof of the conjecture.

For a singleton S={x}, the right side is at most r-1, so every x has a predecessor in the exact-r graph. For |S|=L, the right side is at most r-2, so every L-subset has an outside vertex with at least two outgoing neighbors in it. Proving the existence of a proper L-subset with no such outside fork would finish this minimality route, but that universal statement is not established. Counting all L-subsets gives only a weak covering bound; it does not force a contradiction. Research continues on the actual coupled neighborhood structure.

## C8 Current honest checkpoint

No complete all-n/all-r proof or legal binary counterexample. C2,C6,C7 are exact whole-target formulations/conditional constraints; C3–C5 reject shortcuts. The two actual finite controls satisfy CH and remain auxiliary. All data and the independent coefficient comparison are in exploration/caccetta_haggkvist_exact_controls.py and caccetta-haggkvist-exact-controls.json.

Effective source work04:02:48–04:04:29 is1m41; resumed mathematics04:06:48–04:20:42 is13m54, for15m35 at this safe preservation boundary. Map/commit preservation04:04:29–04:06:48 and this checkpoint preservation are excluded. No requested service has interrupted CH yet. Its clock will continue, not reset.
