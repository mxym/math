# One sign and almost one sign of a unit norm-26 field

Let A be the adjacency matrix of an SRG(99,14,1,2), with A²=12I−A+2J. A neutral marking here means an integral A-eigenvector of eigenvalue −4. Write b=1_P−1_N for a unit such marking of squared norm 26, so |P|=|N|=13. This note proves literal support overlap constraints. The shared-sign result below also applies to neutral squared norms at most 30. These results do not bound the total population sufficiently to remove a palette.

We use the public [nonzero neutral squared minimum 14 and norm14/16/18 support descriptions](https://github.com/mxym/math/blob/main/research/conway-99/short-support-packing/README.md), [norm16 heights](https://github.com/mxym/math/blob/main/research/conway-99/unpublished-neighbor-sieve/shared-norm-18/exclusion.md), and [norm18 heights](https://github.com/mxym/math/blob/main/research/conway-99/unpublished-neighbor-sieve/shared-norm-18/height-three.md).

## Exterior budget for any two-sign difference

If a unit neutral difference has d sites in either sign, each sign induces equal e edges, by the opposite-neighbor degree equation. Let Q be the sum of squared same-sign induced degrees across both signs. At any exterior site z let r_z count neighbors in either sign (the two counts agree); let H_j be the number of exterior sites of height j. Then

* ∑ r_z=10d−4e;
* ∑ choose(r_z,2)=d(d−7)−7e−Q/2, by counting common neighbors of pairs in one sign and subtracting the witnesses from the two sign sides;
* putting T=∑_{j≥3}choose(j−1,2)H_j and D=∑_{j≥3}(j−2)H_j, one has H0=99−19d+d²−3e−Q/2−T and T≥D.

In particular, any set of s exterior sites has at most 2s+D incidences into one sign, by bounding each height by 2 plus its positive excess.

## A single 13-site sign determines every unit norm-26 field

Suppose two different such b,b' share their whole positive set P. Let C be their common negative sites, of size 13−d, and use d,e,Q,r,T,D for their neutral difference (which has no sign conflicts). Let E=∑_{c∈C}r_c≥13−d−H0. Count the contacts into P of the moved negatives in either original marking. Each moved negative has four positive contacts plus its original negative degree. Among these negative contacts, the total within the moving side is 2e and the total into C is E. Hence P accounts for exactly 4d+2e+E of the chosen sign's height and for at most 26+D. Substitution gives
`5e+Q/2+T−D ≤ (d−8)(d−14).`
Since 7≤d≤13, d=9,…,13 are excluded. At d=7 the Fano height at every exterior site is at most one, so 13 fixed positives cannot receive the necessary 28 contacts. At d=8 every norm16 exterior height is at most two, so 13 sites cannot receive the necessary 32 contacts. Thus no distinct fields have the same P. This holds without any assumption on the (3,37) shell, stronger in scope than the previously known matching-side argument.

The same proof for a neutral signed-unit marking of sign size s replaces the displayed right side by d²−22d+99+s. For s≤15 this is negative throughout d=9,…,13, while d=7,8 still fail their height bounds. At d=14 or 15, the full common positive set would receive at least 4d contacts; pad its height vector by zeros to 15 sites if needed. The discrete convex function F(h)=max(0,(h−1)(h−2)/2) for h≥1 and F(0)=0 has values 0,0,0,1,3,6,… . A sum at least 56 or 60 over 15 sites costs at least 37 or 45 in T, respectively, while H0≥0 gives T≤29 or 39, respectively. Thus every fixed neutral unit norm at most 30 is uniquely identified by one complete sign.

## Almost all signs shared under G(3,37)=0

Let d_i=3e_i−Ae_i. If three positive sites span two edges, subtracting their d_i yields charge −3, squared norm 37; spanning three gives norm 23, below the charge-three minimum 33. Therefore under G(3,37)=0 both signs of every U026 field induce matchings. The missing shell assumption may equivalently be phrased U(3,37)=0 because every such field is unit, by the [public short-shell classification](https://github.com/mxym/math/blob/main/research/conway-99/unpublished-neighbor-sieve/short-shell-moments.md). The same formula with a triangle having two positives and one zero also gives squared norm 37, so every positive edge has its graph triangle cap negative, and vice versa. For the formula here, if S has three vertices, the translated norm is 107−14(e(S)+∑_{i∈S}b_i).

Take two distinct b,b' whose positive sets intersect in 12 sites P*. Write P=P*∪{x}, P'=P*∪{y}. Neither x nor y is opposite-signed in the other field: a positive x has at most one neighbor in P* and at most one more in P', whereas a negative in b' needs at least four such neighbors. The full difference is thus signed-unit. Put X=N\N', Y=N'\N, C=N∩N', and write d=|X|+1=|Y|+1 for the half-size of its support. The difference signs are Y∪{x}, X∪{y}. Use e,Q,T,D,r,H as above, E=∑_C r≥14−d−H0, and K=e(X,{y})+e(Y,{x})≤2e. Here e(S,T) counts the edges between disjoint sets S,T and e(S) denotes internal edges.

The height sum over P* is e(X,P*)+e({y},P*). By the negative equation on X, e(X,P*)=4(d−1)+2e(X)+e(X,C)−e(X,{x}). By the zero equation at y, e({y},P*)+A_xy=e({y},X)+e({y},C). Since E=e(X,C)+e({y},C), since e=e(X)+e({y},X), and since at x the difference equation gives e({x},X)+A_xy=4+e({x},Y), combination gives
`∑_{p∈P*}r_p=4d−8+2e+E−K.`
Bound the left side by 24+D and substitute H0:
`5e+Q/2+T−D−K≤(d−9)(d−13).`
The left is nonnegative, so d=10,11,12 are excluded. At d=7,8,9 the difference signs are independent, giving e=K=0. Its exterior 12-site height sum is at most 12,20,25 respectively: the Fano heights are at most 1; at norm16 the eight height-two sites are the only sites above one; at norm18 there is at most one height-three site and no height ≥4. These are below 4d−8=20,24,28. The remaining possibilities d=13 and 14 also fail:

* At d=13 the displayed inequality has right side zero. Hence e=Q=K=0, T=D (no exterior height above three), and the original two bounds are equalities: E=|C|−H0 and the common positives P* contain all height-three sites. Therefore H0=21−H3≥21−12=9. But |C|=1, giving E<0.
* At d=14 the common negative set is empty, so E=0. The exact height sum over P* is at least 4·14−8=48 since K≤2e. By the same discrete convex cost F, these twelve sites alone contribute at least 12F(4)=36 to T. Yet the height budget H0=29−3e−Q/2−T gives T≤29.

Thus **no two different oriented unit norm-26 markings have any 12 positive sites in common** under G(3,37)=0, irrespective of how many same-sign matching edges they have. In particular every 12-subset from an actual 13-positive side determines that oriented marking uniquely in this branch.
