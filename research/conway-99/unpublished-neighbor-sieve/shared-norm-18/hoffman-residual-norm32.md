# Two-site reconstruction of an exceptional zero-on-coclique norm-32 field

Use the two-type hypotheses and H,C of the [Hoffman residual-theta note](hoffman-residual-theta.md). Write d_i=3e_i−Ae_i, let B_i=N(i)∩C on block vertices, and let m_2 count H-eligible oriented norm-18 fields t with two positive and two negative sites on C. There are at most **2m_2** H-eligible oriented nonunit norm-32 neutral fields vanishing on C, even before restricting to one residual maximal 3-extension. In fact their count is an explicit sum of quantities in {0,1,2} over these t.

Let v vanish on C, ||v||²=32, Av=−4v. If a coordinate has magnitude at least 3 one of d_i±v has charge 1 and squared norm 32+23−14|v_i|≤13, impossible by the charge-one minimum 21. If v has a coefficient +2, form b=d_i−v of type (1,27), with b_i=1. On this face all such H-eligible b are precisely the site translates b=t+d_j of norm-18 fields at a negative site j of t, with a unique j recognizable by its +2 coefficient. This is the charge-(1,27) translation of the short-shell sieve; the residual seven-class of d_i is zero. The negative support of t is independent. The positive sites of t+d_j outside j are those positive sites of t missing j, independent and all missing j. Hence i is a positive site of t not adjacent to j, and
```
v=d_i−d_j−t
```
has exactly the two exceptional coefficients +2 at i and −2 at j. Indeed off i the entries of d_i are nonpositive and b≥−1, so no other +2; the only other possible −2 would require a positive neighbor of i in b, of which there is none. The same argument after negation shows that a vector with −2 only is impossible.

In particular both i and j are block vertices, since v|C=0. Write X=C∩supp(t_+),Y=C∩supp(t_-); restriction to C gives X=B_j minus B_i and Y=B_i minus B_j. Each four-block is distinct and two blocks meet in at most two points. A genuine norm-18 field has |X|=|Y|≤3, so the candidates are 2 and 3. In the case 3, each of the three positives on C has four neighbors among the six negatives of t outside C; the three four-subsets of six must intersect pairwise in at most two. Thus their complements are disjoint pairs partitioning the six sites. Each negative outside C has exactly two neighbors among X. But j would have all three as neighbors, impossible. We conclude |X|=|Y|=2.

Conversely, given an H-eligible t with these signed pairs on C, count the two-subsets Z of C outside X∪Y for which the actual distinct blocks Y∪Z and X∪Z are represented by i∈supp(t_+) and j∈supp(t_-) respectively. Every Z determines both ordered sites uniquely by simplicity of the block design. They have two common neighbors in C, so they are nonadjacent. The formula v=d_i−d_j−t vanishes on C. The difference d_i−d_j is a genuine neutral eigenfield (individual d_i's have charge 1); it has squared norm 42 because i misses j, and pairs to 14 with t since t_i=1,t_j=−1. Thus ||v||²=42+18−28=32, with the two exceptional entries. H compatibility follows because d_i−d_j is in the graph lattice at seven. Recovering i,j and then t from v gives a bijection. The pair Y occurs in precisely two blocks in the 2-(22,4,2) design, so there are at most two possible Z, proving the count.

When D16 denotes the number of such norm-32 fields in one residual dual (now including unit fields), and E16 counts the exceptional subset in that dual, the actual fourth-coordinate sum is therefore
```
sum_v sum_b v_b^4 = 32 D16 + 24 E16,       0≤E16≤2m_2.
```
Here the 24 comes from the two squares 4 each changing to fourth powers 16. The formula does not assert that every one of the 2m_2 possible reconstructions occurs or lies in the selected 3-extension.
