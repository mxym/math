# Prior work and scope comparison

## Primary comparison

François Morain, Guénaël Renault, and Benjamin Smith,
“Deterministic factoring with oracles,”
*Applicable Algebra in Engineering, Communication and Computing*
34(4) (2023), 663–690.
DOI: https://doi.org/10.1007/s00200-021-00521-8
Preprint: https://arxiv.org/abs/1802.08444

Their Theorem 1.2 gives deterministic polynomial-time recovery for a
squarefree triprime \(N=p_1p_2p_3\), \(p_i=N^{\alpha_i}\), under
several open size-region inequalities, including
\(2\alpha_1+3\alpha_2\ge2\) or
\(\alpha_2>(\sqrt{17}-1)/8\). The present theorem is different: it
uses a thin additive-cluster promise and may enter portions of the
ordered exponent simplex outside those inequalities. It does not fill
an open two-dimensional exponent region. Any comparison with the grey
region in their figure must first intersect it with
\(\alpha_1>\alpha_2>\alpha_3\), \(\sum\alpha_i=1\).


The shell construction in PROOF.md has all three exponents
\(1/3+O(1/\log X)\), so for large \(X\) it satisfies none of the three
published sufficient inequalities. This comparison concerns theorem
hypotheses only; it is not a lower bound on the MRS algorithms.

## Geometric antecedent

Y. Narita, S. Saito, N. Saitoh, and K. Yoshida,
“On the behaviour of solutions to discrete time Lotka–Volterra
equation,” arXiv:nlin/0005059v2 (2000),
https://arxiv.org/abs/nlin/0005059 .

Their equation (18) studies intersections of the invariant surfaces
\(xyz=\mathrm{constant}\) and
\((1-x)(1-y)(1-z)=\mathrm{constant}\). This is a geometric antecedent
for the same two symmetric invariants. It does not state the endpoint
enumeration or additive-gap complexity bound here.

## Standard ingredient and claim policy

The proof also uses standard deterministic polynomial-time
factorization of fixed-degree integer polynomials via LLL and
fixed-degree real-root isolation.

Searches were made for triprime factoring from \(\varphi(N)\), balanced
or near-equal three-prime products, and the endpoint identities. No
source matching the exact additive-cluster theorem was located. This is
not an exhaustive priority search, so no first-proof or novelty claim is
made. The result remains on the research branch pending an
author-independent proof audit.
