# Two 12-fiber obstructions inside the partial K6 triangle array

Use the triangle-array model and elementary grid and population arguments of [the 13-fiber theorem](partial-k6.md). The present note concerns the two three-edge subsets of a pentagon, not all 12-fiber arrays. In both cases start with pairwise disjoint graph triangles indexed by the 12 present edges of the abstract K6 on 0,...,5. Two indexed triangles have a perfect matching across them if the indices are disjoint and no cross edges otherwise. No automorphism is assumed.

**Theorem.** Neither missing-edge pattern P4=(01,02,13) nor P3+K2=(01,02,34) is possible. A Berge pentagon in the good-prism grid incidence structure therefore has at least four bad secondary prisms. With the charging convention in the 13-fiber note it follows that its total count is at most 24B (B counts bad prisms).

**Necessary classes.** Write D_fg=1 when present indices f and g are disjoint, zero otherwise, and C=D+2I for core neighbor counts by fiber. An exterior vertex contacts each present K6 perfect matching of three triangles exactly once by grid 1-domination; enumerating these 12-bit words produces exactly 9 words: W_a(f)=1[a in f] for 6 stars and W_e(f)=1[e disjoint f] for 3 missing indices e (exceptionals). For each e, take a disjoint present pair f,g complementary to e. Their 15 common-neighbor slots have 12 core witnesses counted with multiplicity: six from each of the two fibers' own triangles, i.e. twelve in all because no third disjoint fiber is present. Only word e contains both indices. Consequently its population is 3. A site in f has 2 core neighbors in f and one in every disjoint present index; thus its exterior degree is 6+#{e disjoint f}. Counting exterior contacts at f then gives p_a+p_b=18 on every present f=ab. The present index graph is connected and contains an odd cycle, so each star population is 9.

**Individual exterior rows.** The nine-tuple h of counts of exterior neighbors by type of a source word w is componentwise nonnegative integral, h_i at most the corresponding class size (one smaller for one's own class), and
[
 \sum h_i=14-|w|,\qquad
 \sum_i W_i(f) h_i= 6-3w(f)-\sum_{g:D_{fg}=1} w(g).
]
Indeed, all two-walks from that vertex to the 3 sites in f total 6−w(f); intermediate core sites contribute 2w(f)+Dw(f). Enumerate h by testing the three exceptional coordinates in 0..3 and recovering each ordinary h_a from the pair sums h_a+h_b on each present edge ab. Any present triangle of abstract indices containing a recovers 2h_a. The code rechecks all equations after recovery.

**Missing P4.** There are two untouched ordinary indices, 4 and 5. Each vertex of either of these star types sends at least one edge to the exceptional union; every exceptional vertex sends at most one edge to each of the untouched star types. These exact row facts are checked exhaustively. There are 18 star vertices and nine exceptional ones, so every such source sends exactly one. Its allowed rows now force exactly one neighbor within its own star class. A nine-element class cannot be 1-regular.

**Missing P3+K2.** Write E for the number of edges between star 5 and the exceptional union. For every y in star 5, the rows give 2h_5(y)+sum_e h_e(y)=3 with h_5(y) either 0 or 1. Summing over the nine vertices gives E>=9 and E=3 modulo 4, since the sum of within-class degrees is even. Hence E>=11.

To obtain the opposite bound we need two-walk sums between whole exterior classes. First enumerate the possible rows of any source *core* site in fiber f exactly as above, with restrictions h_i=0 unless W_i(f)=1 and
[
 \sum_i h_i=14-\sum_g C_{fg},\qquad
 \sum_i W_i(g)h_i= (16[g=f]+5[D_{fg}=1]+6[g\ne f,D_{fg}=0])-(C^2)_{fg}.
]
These are sums of all graph two-walks to the sites in g, less the intermediate-core contributions. In the same fiber the sum is 14+1+1, in a disjoint-index fiber 1+2+2, and otherwise 2+2+2.

Now form four exterior classes in order (star 0; stars 1,2,3,4; star 5; all exceptionals), of populations p=(9,36,9,9). Write h_i(v) for the number of neighbors of v in the ith such union. No equitability is assumed. Each of the 99 vertices contributes exactly one of the enumerated rows. In addition to the populations, contact incidence for any present fiber f and exterior class i is fixed: its three sites contribute one for each vertex in i with word containing f. Reciprocity gives sum_{v in i} h_j(v)=sum_{v in j} h_i(v). By A²=12I+2J−A,
[
 \sum_{v\in V} h_i(v)h_j(v)+\sum_{v\in i} h_j(v)=2p_i p_j+12[i=j]p_i .
]
The adjacent term on the left is directed, even on the diagonal. The script [partial-k6-12.py](partial-k6-12.py) gives small signed integer coefficients of precisely these equalities. For every individual allowed row its weighted left side minus 15 times its contribution to E is nonnegative. The weighted right side is 153. This proves 15E<=153, inconsistent with E>=11. Run `python3 -B partial-k6-12.py` (Python 3.10+, standard library). Verification uses only integer arithmetic; linear optimization was used for discovery only. The two surviving inner-fiber 4-row domains are retained, not assumed balanced.

Finally, the five prospective secondary completions of a Berge pentagon supply five distinct missing edges making a pentagon in K6, as in the 13-fiber argument. If at least two secondaries are good, keep them; this leaves exactly a three-edge subset of that abstract pentagon, of one of the two types just excluded. Thus at least four are bad. Each bad secondary can be charged by at most 96 cycles by the earlier reconstruction; 4 times the number of pentagons is therefore at most 96B. This is a necessary local restriction and does not decide global existence.
