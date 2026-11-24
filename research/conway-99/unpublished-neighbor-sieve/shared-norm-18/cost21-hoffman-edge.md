# The cost-21 positive edge and Hoffman angles

Fix one maximal determinant-49 seven-extension H. Use literal eligible fields throughout. Let u have charge one and cost 21; write c_D=−1_D for an eligible Hoffman 22-coclique and d_i=(3I−A)e_i. The congruence u·c_D≡4 (mod 7) holds because D has trivial residue in the terminal anisotropic plane. The conclusions apply, for example, to every graph U121 tested against every original coclique coeligible in H. No assumption on N14 or on the rank is made.

A (1,21) field is unit: a coordinate ≥2 in u leads, by subtracting d_i, to a neutral cost at most 12 (not the zero vector), and one ≤−2, by adding d_i, gives a charge-two field of cost at most 20. Consequently its positive and negative sets P,N have sizes 5 and 16. Write e_P,e_N for their internal edge counts. At a positive point its N-degree is six plus its P-degree; at a negative point its P-degree is two plus its N-degree. Thus e_P=e_N+1. Count unordered pairs of positives with common neighbor x: over all x the sum is 20−e_P, while the contribution from N alone is at least 16+4e_N. Hence e_N=0 and e_P=1. Denote its unique edge by e=pq.

The only possible angles δ=u·c_D are −3 and 4. For δ≤−10, u+c_D has charge three and cost at most 23<33. For δ≥18, c_D−u has charge one and cost at most seven. At δ=11 this last difference is another unit (1,21), whose positive sites must all be in N. This is impossible because N is independent and each (1,21) has a positive edge.

Writing E=d_p+d_q, one has E²=36, E·u=18, and u′=E−u is another (1,21) with positive edge e. This reflection preserves H and reverses the terminal residue. It acts without fixed points because E has an odd coordinate at a neighbor of p outside {q} and not adjacent to q. Now
```
(u+u′)·c_D = 8−7|D∩e|.
```
If D misses e, both angles are four. If D meets e, the two angles are {−3,4}. Moreover u↦u+c_D is a bijection between (1,21) fields at −3 and (3,37) fields at 19.

Consequently, let n_e be the number of all eligible (positive charge) cost-21 fields with positive edge e, and let h_x count eligible cocliques through x. In **raw counts** the following identity is exact:
```
sum_D # {eligible (3,37) g : g·c_D=19} = (1/2) sum_{e=pq} n_e (h_p+h_q).
```
Each side counts the nontrivial angular incidences once, via the two-element reflection orbits. If raw 337 is absent, every endpoint of a positive edge from any eligible (1,21) field is excluded from all eligible Hoffman cocliques; equivalently u·c_D=4 for every such pair.

There is also a bound before any absence assumption. A fixed g counted on the left has at most two eligible extreme cocliques. Two extremes at intersection k=1 or 8 would produce c_D+c_F−g of charge one, cost 5+2k; k=1 is impossible and k=8 gives (1,21) at angle 11 against c_D, already excluded. Thus distinct extremes must meet in 15. A 15-overlap pair has no third simultaneously meeting both in 15, by the [Fano endpoint intersection table](../../marked-coset-shells/README.md). In particular sum_e n_e(h_p+h_q)≤4G337(H), with G337(H) denoting the literal H-eligible population, not its division by eight.
