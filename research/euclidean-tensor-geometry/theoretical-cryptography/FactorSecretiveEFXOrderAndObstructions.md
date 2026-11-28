# Secretive EFX: an order-sensitive guarantee and a sharp two-known-agent obstruction

A fixed partition must be prepared without the valuations of the secretive agents. After they select distinct bundles, the remaining bundles can be assigned to the public agents. A public agent must satisfy her fairness inequalities in comparison with **all** bundles, including the selected ones.

There are two conclusions.

1. With \(n-1\) public agents and one secretive agent, approximate agreement on a common order gives a complete, efficiently computable \(\alpha_i\)-EFX\(_0\) allocation for each public agent \(i\). The order factors may differ by agent; their feasibility and the largest common factor are computable exactly. In particular, four agents admit complete exact EFX\(_0\) for any number of goods if three have the same weak item ranking. The fourth may have an arbitrary monotone valuation, unrevealed until she chooses a favorite bundle; she receives an envy-free bundle in her own view.
2. Fix \(n\ge4\), and let just two agents be public, with a shared strict item ranking and positive additive valuations. Requiring both to be EFX\(_0\) after **every** deletion of \(n-2\) bundles is universally possible through \(m=n+2\) goods and can fail already at \(m=n+3\). For four slots, the first obstruction is at seven goods. This is an impossibility for a deletion-robust partition, **not** a counterexample to ordinary four-agent EFX existence.

The secretive model and the separate broad EF1 theorem with one secretive agent are due to [Arunachaleswaran–Barman–Rathi](https://doi.org/10.1609/aaai.v33i01.33011732), whose Algorithm 2 and Lemma 8 choose a bundle safe for insertion. The exact common-order case also follows by selecting the next common least-valued good in their mechanism, so we do not claim that special case as an independent priority result. We give a direct one-reserve-unit proof, the order-factor formulation, and the sharp obstruction for two public agents. The [Markakis–Santorinaios common-tier theorem](https://arxiv.org/abs/2308.04860) has an ordinary full-information model, and the [Alkassar–Fouz–Mehlhorn theorem through nine goods](https://arxiv.org/abs/2608.08590) is for ordinary complete EFX\(_0\), not robustness to unknown prior bundle choices. The order factor here is also different from a ratio of values assigned to a fixed good by different agents.

## 1. The one-reserve-unit insertion

For a partition \(B_1,\ldots,B_n\) of the currently placed goods, call column \(j\) acceptable to public agent \(i\) if
\[
 v_i(B_j)\ \ge\ T_i,\qquad
 T_i=\alpha_i\max_{b,\,g\in B_b} v_i(B_b\setminus\{g\}) .
\]
Use threshold zero if every bundle is empty. Additive valuations are assumed nonnegative, so a public agent also passes the trim inequality against her own bundle. For a final set of retained columns a matching into acceptable columns gives exactly the public guarantees, including comparison with bundles that were removed.

Keep a nonnegative integer matrix \(X\) supported on the acceptable entries, with row sums \(n+1\) and column sums at most \(n\). Since there are \(n-1\) public rows, the total mass is \((n-1)(n+1)=n^2-1\), so exactly one column \(c\) has a spare unit. With all slots empty, place one unit in every entry and one additional unit at each \((i,i)\) for \(i=1,\dots,n-1\).

Before each insertion, freeze all current values and thresholds. Whenever \(c\) is acceptable to \(i\) and \(X_{ij}>0\) with \(v_i(B_j)<v_i(B_c)\), move one unit in row \(i\) from \(j\) to \(c\), making \(j\) the new spare column. This preserves the load constraints. Give each row's columns integer ranks from \(0\) to \(n-1\) that increase with value; the sum of ranks weighted by \(X\) increases strictly each time and is at most \((n^2-1)(n-1)\). Thus the process stops in polynomially many moves. At termination any occupied \((i,j)\) satisfies
\[
                     v_i(B_j)\ge \max(T_i,v_i(B_c)).             \tag{1}
\]
Indeed if \(c\) was itself unacceptable to \(i\), \(v_i(B_c)<T_i\); otherwise a strict violation of (1) would allow another move.

Fix an order \(g_1,\ldots,g_m\) such that each public additive row satisfies
\[
                        v_i(g_a)\ge\alpha_i v_i(g_b)
                        \quad\text{whenever }a<b,                 \tag{2}
\]
where \(0\le \alpha_i\le1\). Insert the next good \(g\) into the spare slot \(c\). All older goods \(h\in B_c\) satisfy (2), and additivity gives
\[
 \alpha_i\,v_i((B_c\setminus\{h\})\cup\{g\})
 \le \alpha_i v_i(B_c)+(1-\alpha_i)v_i(h)
 \le v_i(B_c).
\]
Removing \(g\) itself gives \(\alpha_i v_i(B_c)\le v_i(B_c)\). This also covers the case in which \(B_c\) was empty. Other trimmed values did not change. The new threshold is at most \(\max(T_i,v_i(B_c))\), and no own bundle value decreased. Hence (1) shows that the old \(X\) remains feasible. Empty slots, ties, and zero goods are allowed. For \(\alpha_i=1\) the same argument works for nonnegative monotone public valuations with a common **contextual** ordering: replacing any selected older good by any later good never increases the value of the set, regardless of the context. The additive common weak ranking is a special case.

When all goods are placed, let \(S\) be a nonempty set of public rows and let \(N(S)\) be their union of positive-support columns. Then
\[
             (n+1)|S|\le n|N(S)|,\qquad |N(S)|\ge |S|+1 .
\]
After any single deletion, Hall's theorem gives a matching for all public agents. If the secretive agent chooses a favorite complete bundle by her monotone valuation, she herself has no envy, because every trimmed other bundle is worth at most its complete value. The procedure needed no valuation information from her when preparing the partition.

There is no global linear-programming step: each insertion has fewer than \(n^3\) rank-increasing unit transfers and a polynomial scan for a legal transfer. The proof uses exact comparisons and integer ranks. With rational additive input the computation is polynomial in the input size, as are the value comparisons; for the contextual variant it uses polynomially many oracle comparisons with the contextual order supplied.

## 2. Optimal order agreement is a bottleneck over directed cycles

For prescribed factors \((\alpha_i)\), introduce an arc \(g\to h\) between different goods if \(v_i(h)<\alpha_i v_i(g)\) for some public \(i\). A valid order satisfying (2) must obey every arc, and a topological order of these arcs is sufficient. This remains exact with ties because the arcs use a strict inequality.

For a common factor \(\alpha_i=\gamma\), give the directed pair \(g\to h\) weight
\[
                     \rho(g,h)=\min_{i:\,v_i(g)>0}
                                     \frac{v_i(h)}{v_i(g)} .
\]
Take \(+\infty\) for an empty minimum. The arcs are the pairs with weight strictly less than \(\gamma\). Therefore the greatest permitted common factor **for this order condition** is
\[
 \gamma_*=\min\left(1,\min_{\mathcal C}
                        \max_{(g,h)\in\mathcal C}\rho(g,h)\right),
\]
where \(\mathcal C\) ranges over directed cycles, and an absent cycle is interpreted with \(+\infty\). At the critical value no cycle has all its edges strictly below threshold, so the bound is attained. For rational valuations, scan the finitely many ratios in \([0,1]\) and topologically sort at each tested threshold; no explicit cycle enumeration is needed. This is a sufficient fairness guarantee through (2); it is not a hardness statement about better algorithms. Cycles longer than two can matter: public valuations \((4,3,2),(2,4,3),(3,2,4)\) have a directed three-cycle of weight \(1/2\) on each edge, while every directed two-cycle has bottleneck \(2/3\).

## 3. A sharp goods bound for two public agents

More generally there are \(n\) slots, \(t\) public agents, and \(n-t\) slots may be deleted arbitrarily. We ask only for the public agents to remain exact EFX\(_0\) relative to **all original slots**. For two public agents, this requires that each agent accept at least \(n-1\) slots (otherwise a pair of unacceptable slots can be left) and that their union of acceptable slots be all \(n\) (otherwise a universally unacceptable slot can be left). These two conditions are also sufficient by Hall's theorem on any retained pair. No fairness constraint between two secretive agents is asserted.

### Up through \(n+2\) goods

For any number \(t\ge1\) of public agents with additive valuations in a common descending order, a robust partition exists through \(n+2\) goods. With at most \(n\), use singleton and empty slots; with \(n+1\), pair the last two, making every other bundle a singleton. All slots are acceptable to every public agent because the trim threshold is at most the earlier singleton values.

For \(m=n+2\), number goods in common order \(1,\dots,n+2\). Make singleton slots \(1,\dots,n-2\), and the pairs \(\{n-1,n+2\}\) and \(\{n,n+1\}\). For each public agent \(i\) the trim threshold is \(v_i(n-1)\). All but possibly the pair \(\{n,n+1\}\) are acceptable to everybody. If even one public agent accepts that pair, assign it to such an agent if it survives, and match the rest arbitrarily. If nobody accepts it, instead make the last three goods a triple and leave \(1,\ldots,n-1\) singleton. The new trim threshold is \(v_i(n)+v_i(n+1)<v_i(n-1)\) for every public agent. All slots are again acceptable to everyone. This covers all deletions independently of which secretive agents might have made them.

### Failure with seven goods and four slots

Use two public agents with strict common order \(1>2>\cdots>7\) and additive rows
\[
                 u=(10,9,8,7,6,5,4),\qquad
                 v=(14,13,5,4,3,2,1).
\]
If any slot contains at least three goods, \(u\)'s EFX trim threshold is at least \(6+5=11\), attained as the minimum of the two largest goods in any three-good set. Thus no singleton or empty slot is acceptable to \(u\), and accepting at least three slots forces size multiset \((3,2,2,0)\). If all slots have size at most two, seven goods force \((2,2,2,1)\). In both possibilities at least one of goods 1 and 2 belongs to a nonsingleton, so \(v\)'s trim threshold is at least 13, by deleting a different good from that slot. A slot containing neither 1 nor 2 is worth at most \(5+4+3=12\) to \(v\). Only two slots can contain either of those goods, so \(v\) accepts at most two slots. This contradicts robustness. Combined with the upper result, seven is the first possible size.

### Padding to \(n\ge4\) slots

Retain the two public valuations and add \(n-4\) new goods listed before the seven original ones. Give these new goods the same strictly decreasing values in both rows, all greater than both total old-row values. If any of these high goods shares its slot with another good, both trim thresholds are greater than either total old value. At least four slots contain no high good, hence cannot be acceptable to either row, contradicting acceptance of at least \(n-1\) slots. Thus every high good must occupy its own singleton. The four remaining slots partition the original seven goods, and each public agent must accept at least three of them. This is the obstruction just proved. The instance has exactly \(n+3\) goods. This padding holds with two public agents and \(n-2\) possible deletions, not with arbitrary public multiplicities of the two rows.

## Reproduction and limits

Run `python3 verify_factor_secretive_efx_order.py`. It checks the reserve-unit construction on small exact and approximate order examples, optimizes common order factors against exhaustive permutations, independently tests all \(4^7=16{,}384\) labeled partitions by actual retained-bundle matchings, and checks the small-goods construction. The proof is all-order; the finite tests are cross-checks. We did not locate this two-public sharp boundary in the related primary sources searched. This is not a resolution of ordinary EFX for arbitrary additive valuations without an order hypothesis.
