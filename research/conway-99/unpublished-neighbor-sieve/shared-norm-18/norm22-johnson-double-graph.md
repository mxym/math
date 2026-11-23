# Double norm-28 differences and a graph on norm-22 lines

Work only on the still hypothetical rank-42 two-type face, with oriented neutral norm-18 labels in each of eight nonzero seven-classes on a norm-four circle. Inner products here are the **ordinary integral graph-coordinate** inner products. A line of fields means the two actual vectors ±v, not all vectors on a discriminant line. Write μ(q) for the number of unordered decompositions q=a+b into actual norm-18 fields. Negation preserves μ. A double c is a norm-28 zero-class field with two distinct unordered norm-18 decompositions.

The established inputs on this [two-type face](two-type-true-hoffman.md) are: norm 14,16,20 and 26 do not occur; all norm-18 and norm-22 neutral fields are signed units; reduction of inner products modulo seven is the anisotropic plane (with square determinant); and the norm-four circle has eight classes. In particular distinct nonantipodal norm-18 fields have absolute inner product at most 7. Indeed absolute value ≥12 gives a neutral field of squared norm at most 12, the globally forbidden range; 8,10,11 give norms 20,16,14. Value 9 would give circle vectors with Gram determinant 18²−9²≡5 (mod 7), a nonsquare, impossible in this plane. In one signed class the only remaining possible distinct products are 4 and −3.

**Local dictionary.** If c=x+y=x'+y' is a double then x·c=y·c=14. Thus x·x' and x·y' sum to 14, and both equal 7; all four cross products equal 7. Their source residues therefore lie on perpendicular lines, with opposite residues within each decomposition since c is zero-class. No third decomposition exists in a plane. The fields q=x−x'=y'−y and s=x−y'=x'−y each have norm 22, two decompositions and q·s=0. Their two nonzero residues also lie on perpendicular lines. Changing signs or swapping either partition only interchanges or negates q,s. Conversely a fixed unoriented q,s gives at most one unoriented c, because c≡q+s coordinatewise modulo 2. Two nonantipodal candidates with equal parities would give two nonzero integral neutral fields (c+c')/2, (c−c')/2, of total squared norm 28, whereas each has squared norm at least 18.

Fix a particular oriented q with μ=m>0. Its source residues are one unordered pair u,v with u²=v²=4, u·v=0, u+v=β(q). Indeed u on the norm-four circle must satisfy u·β(q)=4, a non-tangent line which already contains both u,v. Orient all decompositions as q=a_i+b_i with [a_i]=u and [b_i]=v. All a_i are distinct, all b_i distinct. Since a_i·q=11, for i≠j the two bounds a_i·a_j∈{4,−3} and a_i·b_j≤7 force a_i·a_j=b_i·b_j=4 and a_i·b_j=7. Then
```
c_ij = a_i−a_j = b_j−b_i,
s_ij = a_i−b_j = a_j−b_i = a_i+a_j−q.
```
The c_ij are double norm-28 lines; all C(m,2) are distinct because a fixed double has at most one decomposition in source direction u and ±c identifies precisely the unordered pair i,j. Their second norm-22 endpoint is s_ij. Applying the first construction to a double c and either endpoint q gives back this same edge (take the two original sources of residue u in the q decompositions). Thus the graph on unoriented norm-22 fields, with one undirected edge per double norm-28 line, is simple, has degree C(μ(q),2), and
```
2 · #double norm-28 lines = Σ_q C(μ(q),2).
```
It splits over the two perpendicular pairs of projective norm-one directions into bipartite blocks. Each neighborhood admits coherent orientations with all s_ij in the signed class u−v, and s_ij·s_kl=−6+14|{i,j}∩{k,l}|, i.e. oriented products 8 or −6 at distinct vertices. This is a geometric Johnson neighborhood; no literal graph automorphism is assumed.

**Uniqueness of the positive-inner-product two-step.** Fix one bipartite block and signs on its two classes. Two distinct vertices Q,R on one side with signed dot 8 have at most one common neighbor. For any such center s, the local formula, up to a common sign (the neighbor orientation changes globally, not vertex by vertex), writes Q=a_i+a_j−s and R=a_i+a_k−s. Hence Q−R=a_j−a_k=b_k−b_j, where b_h=s−a_h. For this fixed double and fixed signed source u, the ordered a_j,a_k are determined uniquely by its one decomposition in direction u; similarly the ordered b_k,b_j of signed class v are determined. The source pair for the specified signed center class is unique, so s=a_j+b_j is determined. Changing the block signs or exchanging the two choices of source orientation cannot create a second center line. Consequently
```
1 + 2 Σ_{s adjacent to q} (μ(s)−2) ≤ #actual lines in q's projective norm-22 class,
Σ_{s on the other side} 3 C(μ(s),3) ≤ C(#lines on this side,2).
```
Indeed a fixed local 2-subset has exactly 2(m−2) Johnson neighbors and all local counts of dot-eight pairs are disjoint between different centers.

**Actual site capacity.** On the 22 support sites of the signed unit q let P_i be those where a_i=q. Then |P_i|=11 because a_i·q=11. Off q no a_i,a_j may agree nontrivially: s_ij=a_i+a_j−q is a signed unit. Thus
```
|P_i ∩ P_j|=4+d(c_ij),   d(c)=#{k: |c_k|=2}.
```
All ±2 sites here are outside q. If m=5 or 6, counting occupancy of the P_i as evenly as possible on 22 sites gives total d at least 4 or 6, respectively: for m=5, 11·C(2,2)+11·C(3,2)−4C(5,2)=4; for m=6, 22·C(3,2)−4C(6,2)=6. The [established norm-22 multiplicity bound](two-type-n22-six-decompositions.md) gives m≤6. On the present rootless face the unoriented ±2-slot mass in ALL zero-class norm-28 fields is at most 6S, where S is the number of extra unit (1,23) fields: a distinguished +2 coordinate i maps c to b=d_i−c of (1,23) with positive unit entry at i, no norm-14/Fano exceptional translates; ordinary d_j marks have no +1 and each of S unit labels has exactly 6 positive sites. Summing over antipodal c exchanges +2 and −2, so the unoriented slot mass is the oriented +2 count, at most 6S. Every double counts its d twice in the endpoint bound, hence
```
4·#{q: μ(q)=5} + 6·#{q: μ(q)=6} ≤ 12S.
```
These are true norm-18/22/28 incidence conditions, not an exclusion of the two-type face or any remaining rank.
