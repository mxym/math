# Linear-bit factorization certificates using only Lucas–Pratt checks

Given a complete factorization, each claimed factor's primality can be checked by a general deterministic primality test. Then the factor list itself is already a linear-bit certificate in the ordinary complexity-theoretic sense. The result here is different: the same linear bit bound can be achieved **within elementary recursive Lucas–Pratt verification**, with no general primality-testing subroutine. The tradeoff is that the checker may test multiple proposed bases at each node.

## Statement

For an integer N≥2 of bit length b, its complete factorization has a certificate of at most
```
9b + 2 ceil(log_2(64(b+1))) + 2
```
bits in the format below. The uniformly specified verifier is deterministic, checks products and modular powers only (besides parsing and range checks), and either rejects or returns the unique prime factorization. A simple implementation uses O(b^6) bit operations for checking. No procedure to find the unknown factors, or to construct the underlying Pratt trees in polynomial time, is claimed.

There are two separate compressions: the factor tree needs no explicit prime labels, and every Lucas base can be obtained from a single pair of shared integers.

## Encode the entire factor forest without prime labels

Use a virtual root representing the input N. Its children are the distinct prime factors of N, each edge annotated with its positive multiplicity. At any prime-labeled node p>2, the children are the distinct prime factors q of p−1; each edge to q has exponent e for q^e in p−1. A node labeled 2 has no children. Subtrees are repeated rather than shared, so the certificate is a tree with a virtual top; one need not assign identifiers to prime labels. A nonvirtual leaf is decoded as 2. Every nonvirtual internal node is decoded bottom-up by
```
p = 1 + product_(child edges) q^e.
```
The virtual root product has no added one, and must equal N. In particular the output factors are decoded, not separately written out.

To bound the total length, let L be the number of leaves. Summing base-two log-mass deficits from parent to children gives the exact identity
```
log_2 N = L
        + Σ_(odd prime nodes p) log_2(p/(p−1))
        + Σ_(all edges to q) (e−1) log_2 q.
```
The last sum includes the edges out of the virtual root. Indeed, a leaf contributes log_2 2=1; at an odd node the difference between its log-label and the sum of its children's log-labels equals the corresponding two terms on the right. At the virtual root the log-label difference is exactly the contribution from edge multiplicities. Contributions telescope over all node occurrences. This is a version of the classical log-mass accounting in [Ford–Konyagin–Luca, §3](https://arxiv.org/abs/0904.0473).

Each odd node has a distinct leaf occurrence labeled 2 as a child, so the number of odd nodes is at most L. Hence the number of nonvirtual nodes, also the number of edges, is at most 2b. Moreover Σ(e−1)≤b by the same identity. Encode the plane tree with balanced parentheses (two bits per node, including the virtual root). After opening every nonvirtual node write the incoming multiplicity as the unary word of e−1 ones followed by zero. This uses at most 4b+2 parenthesis bits plus Σe≤3b exponent bits. The format is parsed unambiguously since a node's exponent field is consumed before its child opens are read. Sibling order can be arbitrary; the verifier rejects repeated child labels at any parent, including the virtual root.

The tree by itself does *not* assert primality of its decoded labels: arbitrary trees might decode to composite internal labels. Primality is checked next.

## A shared affine list hits a primitive root at every true node

Let c=ceil(log_2(64(b+1))), let K=32(b+1)^2, and use two integers A,B of b+c bits apiece. At an internal node with decoded label q>K, the candidate bases are
```
(A+jB) mod q,   0 ≤ j < K.
```
For any q≤K, instead try all bases 1,…,q−1, requiring no additional certificate field.

Existence of good A,B is proved by choosing them independently uniformly from [0,2^(b+c)). For any true prime node q, its label is at most N<2^b. Each seed reduced modulo q is at total variation distance at most q/2^(b+c)≤2^(−c) from uniform: the q bucket sizes for the integer range differ by at most one. The pair's distance from two independent uniform residues is at most 2^(1−c). For the ideal pair of independent uniform residues, any two distinct candidate positions have independent uniform values modulo a prime q>K, since the linear map (A,B)↦(A+iB,A+jB) has nonzero determinant j−i modulo q. We do not assert independence of the whole list, or of the lists at different primes.

The proportion of primitive roots among the residues modulo prime q equals ρ_q=φ(q−1)/q. An elementary bound sufficient here is ρ_q≥1/[2(b+1)]: if an integer t has h distinct prime divisors, the i-th smallest one is at least i+1, so φ(t)/t≥ product_(i=1..h) i/(i+1)=1/(h+1), and h≤log_2 t. Apply this to t=q−1 and multiply by (q−1)/q≥1/2. Let X be the number of primitive roots found in the ideal affine list. Pairwise independence makes Var(X)≤E[X]=Kρ_q, so Chebyshev gives
```
Pr[X=0] ≤ 1/(Kρ_q) ≤ 1/[16(b+1)].
```
For the actual finite seed distribution add the total variation bound, at most 1/[32(b+1)]. A union bound over at most 2b distinct large labels gives failure probability less than 3/16. Thus some A,B serve the whole forest. Their combined 2b+2c bits, plus the tree and exponents, give the stated bound.

This uses randomness as a proof of existence, not at verification. One does not have to encode the successful index at each node: the verifier deterministically scans the specified list. No claim about short intervals containing primitive roots is assumed.

## Deterministic verification and soundness

For a claimed internal label q, first verify each child prime by induction. The children and their encoded exponents give the complete expansion of q−1. Check whether some candidate a satisfies the classical [Lucas–Pratt condition](https://doi.org/10.1137/0204018):
```
a^(q−1) = 1 mod q,
a^((q−1)/r) ≠ 1 mod q for every prime child r.
```
The first identity makes a invertible; its order divides q−1. The second set of checks rules out every proper divisor of q−1 as the order, by factoring the quotient (q−1)/ord(a). Thus the unit group modulo q has at least q−1 elements. Since any composite q≥2 has a nonunit in 1,…,q−1, this forces q to be prime. Checks at small q work by the same argument; only leaves need no check because they are exactly 2. Enforcing the exact top product gives a complete prime factorization, with distinct factors and their proper multiplicities. For any choice of seeds, including maliciously chosen ones, acceptance is sound.

Reject overlong or malformed forests, and reject computations that exceed the input value at any intermediate label or product. Since all exponent counts are encoded in unary, there is no hidden outsize power to evaluate. There are O(b) nodes and edges, and at most K=O(b²) bases tried at one node. The total number of modular exponentiations is at most K times (number of internal nodes plus number of edges), or O(b³). Each exponentiation uses O(b) modular products of O(b)-bit values. Schoolbook integer arithmetic gives the stated O(b^6) coarse bit bound. This bound is for a short verifier of a supplied certificate, not for factoring, finding the recursive decompositions, or obtaining suitable bases without them.

## Scope and prior work

* [Pratt's original proof](https://doi.org/10.1137/0204018) and the analysis of [Ford, Konyagin and Luca](https://arxiv.org/abs/0904.0473) provide the underlying recursive certificate and the log-mass accounting; we do not claim priority for those components. [Pomerance](https://math.dartmouth.edu/~carlp/PDF/paper62.pdf) gives a different primality-proof method with few modular multiplications. Here the goal is encoded bit length within the Lucas–Pratt family, not minimizing checker runtime. The shared affine witness list uses classical pairwise independence; the specific combination avoids storing one full-size base at every node.
* In an unrestricted proof system, [Agrawal–Kayal–Saxena](https://doi.org/10.4007/annals.2004.160.781) already lets the verifier check primality without any certificate field. An ordinary factor list has O(b) bits since its labels with multiplicity have total logarithm log_2 N. Thus there is no improvement claimed for the best abstract bit complexity of general certificates; the advance is the linear bound with an elementary, recursively certified checker. This is not related to the [restricted residue-state verification bound](FactorTaggedResidue.md), which measured state rather than proof length.

[Exact toy checks](verify-factor-linear-pratt.js) replay the explicit forest encoding on prescribed small factorizations, verify the affine pairwise independence and seed-distance estimate, exercise a large-node affine-base check, and reject a fake proof with a Carmichael internal label. The replay checks five prescribed forests (including one taking the large-node branch), 118 ordered-position affine pair tables, 35 seed-bias bounds, and seven exact second-moment examples. No input factorization or certificate mining is performed.
