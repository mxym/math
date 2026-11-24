# Complementary one-overlap sums force four-cocliques and shorten the rank-42 cost-21 face

On the rank-42 selected-unit face contained in {018,121,125}, there is now only **one aggregate control**: r=10, N18=236, M=27, S=0, G444=8. It is a necessary control, not a graph. The intermediate cubic obstruction leaves five controls at r=10 and three at r=11. The new input uses actual Hoffman cocliques, not a theta inequality on relaxed populations.

Let A be the simple one-overlap graph on the M actual Hoffman 22-cocliques, and e its edge count. As in the [integer filtration](cost21-integer-filtration.md), f=0, so every distinct pair meets in one or eight; the (4,46) shell consists exactly of y one-positive fields and E−y one-double fields, where E=W446. Every A-edge {C,D} maps injectively to g=−1_C−1_D with unique double at x=C∩D. The two shores C−{x},D−{x} partition 42 of the 84 nonneighbors of x. For d_x=(3I−A_graph)e_x, the map
```
g' = −g−d_x−1
```
is a fixed-point-free involution on the one-double subtype: g'_x=−2, all 14 neighbors of x have value zero (also for an arbitrary one-double field, because the row at a −2 in charge four has neighbour sum zero and all other entries are nonpositive), and the minus-one set off the closed star is complemented among the 84 nonneighbors. Charge/eligibility are preserved (negate the class and shift by an original graph mark with the usual charge fold). In the present rank-42 isotropic shell this is the original sector. In particular at least 2e−(E−y) images have a partner that is also an image.

For each such paired image the second pair {F,H} is disjoint from {C,D} as a pair of cocliques. All four share x and their 21-shores partition the entire second neighborhood of x. They form a K4 of A. Conversely, for any of its six edges, the complementary image is exactly that of its opposite edge. By injectivity at each edge, it belongs to only one such four-coclique configuration. Thus these configurations have disjoint edge sets, and their four triangles apiece are distinct as well. Writing k for their number, the literal estimates are
```
k ≥ max(0,ceil((2e−E+y)/6)),    6k≤e,    tr(A³)≥24k.
```

For each attainable signed norm-18 class size a,b from the previous filtration, put c=42−d(a)−d(b) and l=M−c, where d(j)=ceil(24(j−1)/(j+24)). The common hole in all Hoffman cocliques gives at least l eigenvalues exactly 2 for A. Strip any l of them. The remaining shifted eigenvalues lambda+2 have square sum B=2e+4M−16l and cube sum tr(A³)+12e+8M−64l. The sum of their cubes is at most the sum of absolute cubes, in turn at most B^(3/2). So if z=24k+12e+8M−64l is positive, z²≤B³; necessarily B≥0 in either case. No radical approximation or large fourth-walk bound is needed.

The [standalone checker](cost21_four_coclique_walk.py) imports only the previous native model, regenerating the 41 and 17 prior marginal controls, then testing all integer e and every possible signed class size. In counting at each (a,b,e), using y_lo weakens all tests monotonically: it maximizes E−y and minimizes the forced K4 count. There is no assumption that the first surviving edge number from the previous checker was exhaustive. The intermediate cubic stage keeps exactly (r,n=N18/4,M,S,Q=G444):
```
10: (59,27,0,8), (59,28,0,0), (60,28,0,24), (60,28,1,12), (60,28,2,0)
11: (56,28,1,8), (57,29,1,24), (58,29,3,24).
```
No other support or seven-rank is addressed.

## The physical four-coclique configurations cannot occur on this face

For any physical K4 as above, the uncentered sum of its four negative indicators is −1−d_x: at x this is −4, at its 14 neighbors it is zero, and at every nonneighbor it is −1. Every eligible (1,21) field u has u·c_D=4 at all four cocliques by the [cost-21 Hoffman angle theorem](cost21-hoffman-edge.md), since raw G337=0. Its sum is −11 and u·d_x=7u_x+2. Therefore
```
16 = u·(−1−d_x) = 9−7u_x,
```
so u_x=−1. Its [positive-edge reflection](cost21-hoffman-edge.md) u′ also satisfies u′_x=−1. Since u+u′=d_p+d_q, x must be the unique common neighbor of that positive edge pq. Only seven edges are capped by x, the disjoint edges on its 14 neighbors. Each supports at most four fields by the [rank-42 physical edge bound](cost21-cycle-edge-cap.md). This would give 8r≤28, impossible. Hence no paired coclique images exist and **2e≤E−y**.

## A fourth walk controls the residual density

Reserve l copies of the eigenvalue 2 and a Perron eigenvalue rho. If rho>2 these reservations are distinct. If rho=2, its nonnegative Perron vector can be taken with nonzero coordinate sum, whereas the l dependence directions above lie in the zero-sum subspace; thus an additional copy is available. Let L=rho+2 and B=2e+4M−16l≥L². The other shifted eigenvalues x=lambda+2 have sum of squares V=B−L², and therefore
```
tr((A²−4I)²) ≤ (L²−4L)²+(4+sqrt(V))² V.
```
Indeed lambda²−4=x(x−4), and |x|≤sqrt(V). From the actual simple graph, (A²)_ii=d_i and (A²)_ij is a nonnegative integer common-neighbor count. Replacing each off-diagonal square by that count gives tr((A²−4I)²)≥2 sum_i d_i²−18e+16M. For j=floor(2e/M), rem=2e−jM, put Q_deg=(M−rem)j²+rem(j+1)², the integer lower bound on the squared degree sum.

Set L0=max(4,2+2e/M), since rho≥2 and rho≥2e/M. If L0²>B reject directly. Otherwise the displayed upper bound is convex in z=L² on [L0²,B]. Its first term is z²−8z^(3/2)+16z, with second derivative 2−6/sqrt(z)>0 there; its second is 16(B−z)+8(B−z)^(3/2)+(B−z)², convex as well. Evaluate only its two endpoints and compare their maximum to 2Q_deg−18e+16M. The checker uses upper rational bounds: for sqrt(v) it uses the bounding interval [h/100000,(h+1)/100000] from h=isqrt(floor(10^10 v)), taking the lower end for terms with a negative coefficient. All comparisons are exact and conservative.

On testing every edge count at every admissible pair of signed class sizes, only (r,n,M,S,Q)=(10,59,27,0,8) remains; the allowed splits are (a,b)=(33,26) or (30,29) with e=55,…,60, and c=16 in both. Here E=120, so necessarily y≤120−2e≤10. No assertion of actual existence or sufficiency is made.

The [26-point tight-frame argument](cost21-26-tight-frames.md) excludes the `(33,26)` signed split in the sole aggregate, leaving `(30,29)`; the [eight signed 44-sets](cost21-eight-signed-44.md) are a further necessary feature of that aggregate. No whole-rank or whole-support exclusion is asserted.
