# Scalar subset sums in four-term-free cactus realizations

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

For a finite simple graph G having b bridges and simple cycles of lengths
ell_i=3h_i+r_i, 0<=r_i<3, the minimum cardinality of the scalar subset-sum
set of its distinct positive edge distances, over distinct integer vertex
marks for which that set is four-term-AP-free, is

    7^floor(b/3) 2^(b mod 3) times the product over i of
    7^(h_i-1) (2^(3+r_i)-1).

The formula applies exactly to cactus graphs. All other simple graphs have
no such realization: the standard theta obstruction for non-cacti gives
three edge-disjoint paths with the same endpoints. Each path has a signed
sum equal to the mark difference. Since the paths are edge-disjoint,
flipping their selected subsets one at a time gives a nonconstant 4-AP.

## Lower bound

Use the signed relation decomposition of the prior workbench, [paper,
Section 2](https://github.com/KokunoYumeto/erdos-problem-817-workbench/blob/main/paper/ep817_k4_rate.tex):
minimal-support signed relations have pairwise disjoint supports up to
negation and every signed relation is the sum of some such blocks, each
with an overall sign. A short proof starts with c in {-2,-1,0,1,2}^A
and A·c=0, splitting c into magnitude-one and magnitude-two layers.
If the signed sum in the latter divided by two equals d, the disjoint
sign classes give a 4-AP of difference d (paper Lemma 2.1); thus both
layers are relations. Applying the split to r+s and r-s, with r minimal,
shows that any signed relation s meeting r agrees with r or -r on all
of its support, and subtracting a matching minimal block proves the
decomposition.

A minimal relation block of size s has s>=3, because edge weights are
positive and distinct. Its linked pair of complementary masks is the
only binary collision within the block, and across blocks the scalar
equivalence relation is a product of those separate equivalences.
Hence each block contributes 2^s-1 values and each unused edge
contributes 2. Every graph cycle produces a signed relation supported
on all and only its edges. Its support must therefore be partitioned
into whole relation blocks, with no relation block shared across
different cycles or crossing into bridges.

For a cycle of length ell=3h+r, the product over sizes >=3 is minimized
by h-1 blocks of size 3 and one of size 3+r. Indeed if 4<=a<=d,
replacing (a,d) by (a-1,d+1) does not increase
(2^a-1)(2^d-1). Thus at fixed part count all surplus belongs to the
largest part. If the part count is below h, this largest part has size
>=6 and splitting it decreases the product, proving the assertion.
For bridges, a block of size s=3j+t (j>=1, 0<=t<=2) contributes at least
7^j 2^t, since 2^s-1-7^j 2^t = 2^t(8^j-7^j)-1>=0.
Single edges contribute 2. Replacing factors 2^3 by 7 when residues
accumulate proves the bridge lower bound.

## Simultaneous attainment by distinct integer marks

Partition each cycle into the extremizing abstract labels of the given
sizes. On a cycle with h labels, assign its cyclic list of edges by
writing labels 1..h, 1..h, then their remaining occurrences in any
order. A proper nonempty contiguous segment in the cyclic order
cannot be exactly a union of full labels. Indeed either arc containing
the first and second occurrence of some label contains at least one
occurrence of each other label (the two prescribed rounds are in
identical order); if the segment were a union of labels, it would
therefore contain every occurrence of every label.

Partition bridge edges into triples and at most two singleton labels.
For one label of size s>=3 allocate s-1 private integer coordinates,
assign distinct unit vectors to s-1 edges and their sum to the final
edge, and give a singleton its own coordinate. Each weight vector is
nonnegative. Its only nonzero signed relation on that label is all
units plus and their sum minus, or the simultaneous negative.
Different labels use disjoint coordinates. Evaluate using successive
powers of 5; signed zero sums are exactly vector signed zero sums
(each coordinate in [-2,2]), and any scalar 4-AP in scalar subset sums
lifts to a vector 4-AP (second differences in [-4,4], so checking
successive residues modulo 5 rules out any cancellation). The vector
subset sums lie in {0,1,2} in each coordinate, forbidding nonconstant
vector 4-APs. All scalar edge weights are distinct by the coordinate
layout.

For each cycle, choose the signs along its cyclic traversal to give
its zero relation in every label, so the circulation is zero. For each
bridge triple choose signs so that no simple path using all three
bridges gives their signed zero relation. This choice is possible:
contract components connected through nonbridge edges; the bridge
graph is a forest. For each triple either there is no tree path
containing all three or their traversal directions on every such
tree path agree up to simultaneous reversal, so we may choose any
sign pattern except the two that produce zero. Every simple cycle
has zero circulation, so the signed values integrate along graph
paths to integer marks (one arbitrary origin in each component).
For two different vertices in the same component, a simple path
between them cannot have signed sum zero: its nonempty edge set
would have to be a union of full labels realizing their respective
relations. Its intersection with any cycle is a contiguous proper
segment, because a cactus has no external path between distinct
vertices of a given cycle; that segment cannot be a union of labels.
On any used bridge triple the chosen orientations exclude a zero
signed sum, and a singleton cannot cancel. Thus all marks within each
component are distinct. Finally translate whole components apart.
Each constructed edge's absolute mark difference is its intended
positive weight, and the signed relation cardinality argument gives
the displayed minimum.
