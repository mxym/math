# Every binary Sidon 29-set in ten dimensions has a 20-point affine half

Suppose every half of $S\subset V=\mathbb F_2^{10}$ has size at most 19, $|S|=29$. Translating by its XOR makes the new XOR zero (since its size is odd). Every character is then negative on an even number of $S$; its Walsh coefficient $w$ is 1 modulo 4. The bound on both parallel halves gives $w\in(-7,-3,1,5,9)$ off the principal character (i.e., one of the five listed values).

Let $h=1_{0\in S}$ and let $t$ count unordered triples of distinct elements summing to zero. If $h=1$ there cannot be any such triple: together with 0 it violates the Sidon property. Otherwise these triples are pairwise disjoint, because sharing one point would give two distinct pairs of the same sum. Thus $t\le9$. The first through fourth Walsh moments, including the principal character, divided by 1024, are $h,29,(3\cdot29-2)h+6t,3\cdot29^2-2\cdot29$. They count ordered zero-sum tuples, including repetitions. The zeroth moment counts 1024 characters. Subtract the principal terms $1,29,29^2,29^3,29^4$. Solving the five independent Vandermonde equations for off-principal multiplicities in increasing order of $w$ gives
* if $h=1$: $(238,-21,540,84,182)$, impossible;
* otherwise: $(386-12t,32t-229,724-24t,4,138+4t)$. Nonnegativity gives $8\le t\le9$.

At $t=9$ the remaining two different points would XOR to zero, impossible. At $t=8$ we consequently have eight disjoint triples, each all nonzero vectors of a two-dimensional linear space $P_i$, and five remaining singleton vectors whose XOR is zero. For any $k$ of the planes and $j$ of the singletons with $k+j\le4$, their sum is direct: a nontrivial relation, collected in these distinct blocks, would choose one nonzero element from each participating plane and each participating singleton. The resulting 1–4 distinct points of $S$ cannot sum to zero: 0 is absent, distinct pairs have nonzero sum, all zero triples have already been enumerated within individual planes, and a four-term sum is forbidden. This gives dimension $2k+j$ and independence of the linear tests used below.

For each character write $z$ for its number of annihilated planes, $l$ for the number of negative singleton values. The latter is even, hence 0, 2 or 4. Each plane contributes 3 or $-1$, giving $w=4z-3-2l$. Off the principal character there are fourteen possibilities. With $T_{kj}(z,l)=\binom zk\binom lj$, character orthogonality (or direct independence) gives
$$\sum_{u\ne0} T_{kj}(z_u,l_u) = \frac{1024\binom8k\binom5j}{4^k2^j} - {\bf1}_{j=0}\binom8k.$$
Indeed annihilating each selected plane imposes two independent zero bits, and a selected singleton must give a negative bit. Consider the integer polynomial
$$P=-25 T_{03}+25 T_{13}+18 T_{20}-18 T_{22}-50 T_{30}+30 T_{31}-40 T_{40}.$$
The consecutive entries (pair:value) at all possible $(z,l)$ are
$$(0,0):0,(0,2):0,(1,0):0,(1,2):0,(1,4):0,(2,0):18,(2,2):0,(2,4):10,(3,0):4,(3,2):10,(3,4):0,(4,2):0,(4,4):0,(5,4):0.$$
Yet the seven corresponding off-principal totals are $1280,2560,1764,4480,840,2240,210$, giving $\sum P=-88$. Contradiction. The script sidon29.py checks all numbers without an LP or a code catalogue.
