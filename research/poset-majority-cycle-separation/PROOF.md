# Comparable arcs can change the cycle spectrum of a linear-extension majority digraph

Gupta, *Balance Constants, Majority Cycles, and the Gold Partition Conjecture through Fourteen Elements*, arXiv:2607.23926v2, §8 Question 14, asks whether two directed graphs on a finite poset P always have the same directed simple-cycle lengths. Write x→y when x precedes y in strictly more than half of P's linear extensions; D retains all those arcs and Dinc retains only those between incomparable elements. Ties give neither arc. A simple cycle may have chords. This question on majority cycles is distinct from the 1/3–2/3 and Gold Partition conjectures.

**Counterexample and unbounded separation.** Take the disjoint union of chains A, B, C, of lengths 28, 5, M (each indexed starting from 1 and increasing in the partial order). At M=1,000,000, D has a simple 83-cycle while Dinc has no cycle longer than 66. More generally, for all sufficiently large M, D contains simple cycles of every length between 3 and (1/12500+o(1))M, while every cycle in Dinc still has length at most 66. The construction has width three.

**Counting a pair.** A uniform extension of disjoint chains is a uniform shuffle of their three fixed internal orders. Its projection to two chains is a uniform two-chain shuffle: each projected word has the same number of insertions of the discarded chain. For two chains of lengths a,b, let H(a,i;b,j) be the probability that the ith member of the first precedes the jth of the second. Of the uniformly chosen a positions of the first chain, at least i must occur within the first h=i+j−1 positions. Thus
```
 H(a,i;b,j) = sum_{v=i}^a binom(h,v) binom(a+b−h,a−v) / binom(a+b,a),
```
with an out-of-range binomial coefficient read as zero. In particular
H(28,4;5,1) = binom(28,4)/binom(33,4) = 1365/2728 > 1/2.

Set L=12947/100000, R=2591/20000, so R−L=1/12500. For M=1,000,000 put l=129470 and r=129550. Two more integer checks give
```
  1 − binom(M+5−l,5)/binom(M+5,5) > 1/2 + 1/20000,
  sum_{v=0}^3 binom(r+3,v) binom(M+25−r,28−v)/binom(M+28,28) > 1/2 + 1/5000.
```
The first probability is H(5,1;M,l); the second is 1−H(28,4;M,r). They certify the directed cycle A4 → B1 → C_l → C_(l+1) → … → C_r → A4. It is simple and has r−l+3=83 vertices. More generally choose any nonempty increasing subsequence of those C vertices: B1→C_j and C_j→A4 hold throughout the interval by monotonicity in the chain index. This realizes each length from 3 to r−l+3. In Dinc two members of C cannot be consecutive. Each C vertex of a simple cycle therefore has a distinct successor outside C; there are only 33 such vertices. This bounds the whole cycle by 66 vertices.

**All sufficiently large M.** Take l=ceil(LM), r=floor(RM). For fixed a and h/M→t, the chance that exactly v of a uniformly chosen positions among a+M are among the first h positions converges to binom(a,v)t^v(1−t)^(a−v). This follows directly by writing the preceding hypergeometric term as binom(a,v)(h)_v(a+M−h)_(a−v)/(a+M)_a with falling factorials; it does not require exchanging a growing sum and a limit. Hence the two pertinent endpoint probabilities tend respectively to
```
  1−(1−L)^5 > 1/2 + 1/20000,
  sum_{v=0}^3 binom(28,v)R^v(1−R)^(28−v) > 1/2 + 1/5000.
```
Both are strict rational inequalities. Eventually both endpoint probabilities exceed 1/2, with no exceptional subsequence, and the argument just given applies. More precisely the longest cycle exhibited in this way has length floor(RM)−ceil(LM)+3.

**Optimality of the width parameter (elementary context).** For a two-chain cover X,Y of any width-at-most-two poset, put k(y)=#{x in X : x→y}. These beating x form a prefix by comparability in X; the lengths k(y) are nondecreasing in the order on Y. Insert each y just after that prefix in the ordering of X, breaking equal k by the original Y order. The resulting total order respects every majority arc, even with exact ties. Thus neither majority digraph at width at most two has any cycle. This observation is contextual, not a claim of priority.

**The first possible disagreement is already at four.** With M=10,000 use l=1,295 and r=1,296 in the same shuffle formulas. They give H(5,1;M,l)>1/2 and 1−H(28,4;M,r)>1/2, so A4 → B1 → C1295 → C1296 → A4 is a full 4-cycle. In any Dinc 4-cycle x→y→z→w→x, adjacent vertices are incomparable by definition. The diagonals are incomparable as well: if x<z, then z→w implies x→w, contradicting w→x, and if z<x then x→y implies z→y, contradicting y→z. Rotate to handle the other diagonal. Such a cycle would require an antichain of size four, impossible in the three-chain example. Gupta's Proposition 7 already shows that no full directed triangle can use a comparable edge, so the two spectra always agree at length three. Four is therefore the smallest possible length of disagreement, not a claim about the minimum number of poset elements.
