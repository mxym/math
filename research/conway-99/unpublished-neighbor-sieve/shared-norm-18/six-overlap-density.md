# The six agreeing sites in an exceptional norm-18 pair

For any two true neutral norm-18 fields on a Conway 99 graph with absolute inner product six, reverse one input so that t·u=6. The difference q=t−u is signed-unit: a doubled site of a neutral norm-24 field would translate to a charge-one field of norm at most 24+23−28=19, below its minimum 21. Thus F=supp(t)∩supp(u) consists of six agreeing sites. The split by sign is 4/2 or 3/3. The number of graph edges induced by F is at least e(q)+3 in the 4/2 case and e(q)+2 in the 3/3 case, where e(q) is the common number of edges within either sign of q. No rank, symmetry or shell absence is assumed.

Indeed, six common positives and no shared negatives is impossible: the six distribute 24 neighbor incidences in each of two disjoint nine-site negative sets, giving at least 2·21 common-neighbor pairs versus the quota 2 C(6,2)=30. For five positives let r≤4 be the number adjacent to the common negative. In the other eight targets of each negative set, 20−r incidences remain. For r=0,...,4 the sharp lower bounds on the number of pair witnesses, C(r,2) plus twice the minimum obtained by balancing 20−r integers on eight sites, are respectively 32,28,25,23,22. All exceed 2 C(5,2)=20.

For clarity write k=|F|=t·u here, m=Σ_F t, h=e(F), and a=h−e(q). Generalizing the calculation in [the seven-site result](unconditional-seven-overlap.md), each exclusive set induces 36−4k+h edges, and the union of the exclusive sets is the support of q, inducing 4(18−k)+4e(q) edges. Thus (1_{supp(t)})ᵀA1_{supp(u)}=12k−4a. The genuine norm-36 construction z_t=s(t)+s(−t) gives z_t·z_u=7(36−9k+4a) and z_t·u=z_u·t=7m. In particular
```
||s(−t)+s(−u)||²=198−31k+14a−7m.
```
Orient the majority shared sign positively. At least two common negative sites i,j remain, are nonadjacent, and the displayed sum y is +2 at both. As in the seven-site argument y−d_i−d_j has squared norm y²−6, coordinate sum +22 and values −1 at those two sites. Consequently y²≥32. Taking k=6 and m=2 or 0 proves a≥3 or a≥2, respectively.
