# Ordinary matroid Z-polynomials need not be log-concave

**Research draft · 18 November 2026.** The proof and arithmetic have undergone independent AI-assisted internal review, not external peer review or formal verification. No worldwide priority claim is made.

**中文摘要。** Proudfoot、Xu、Young 的猜想 6.5 对平凡群蕴含普通拟阵 Z 多项式系数对数凹。本文在 Bérczi、Coron、Eur、Li 的既有秩七拟阵上精确算出 $z_2^2-z_1z_3<0$，并给出同类秩六构造。这里的 Z 是交叉上同调 Z 多项式，不是格的多链计数 zeta 多项式；该结论不要求也不声称例子可线性表示。

 This note uses an existing rank-seven abstract matroid of Bérczi–Coron–Eur–Li [BCEL] and their hyperplane-coalescence theorem. Our observation is about the ordinary (intersection-cohomology) Z-polynomial, not the four polynomials of their counterexamples. A rank-six adaptation is optional and is not needed for the main negative answer. Representability is not a hypothesis in the conjecture. The argument neither establishes nor rules out representability of these abstract matroids; it therefore does not decide the representable-only log-concavity question.

## The target and the answer

Write r for rank. For the ordinary matroid Kazhdan–Lusztig polynomial P, the invariant here is exactly the unmodified, unnormalized Proudfoot–Xu–Young polynomial
     
    Z_M(t) = ∑_{F flat} t^{rk F} P_{M/F}(t).

It is palindromic of degree r, with P=1 at rank zero, P(0)=1 for loopless matroids, and deg P<r/2 for positive ranks. We use the coefficients themselves, without binomial reweighting. [PXY, Conjecture 6.5 and Remark 6.6] predicts strong equivariant log-concavity; for the trivial group this gives ordinary log-concavity z_i² ≥ z_{i−1}z_{i+1}.

**Counterexample.** Let M=C(103,103³) be exactly the matroid in [BCEL, Definition 4.15]. It is a finite simple 3-connected rank-seven matroid. Its Z-polynomial, in ascending coefficient order, is (1,A,B,C,C,B,A,1), where

    A = 152131900215274922417147832846784067260
    B = 10030924901641766668820967869672611178790
    C = 673552605745815483293685742265690269253633.

In particular

    B²−AC = −1849383424683925149456861474552155431616617330030093369162543428798602925491480 < 0.

This disproves Conjecture 6.5 even for the trivial group. It does not contradict hard Lefschetz/unimodality; the displayed coefficients increase to the middle. It also implies non-real-rootedness, **not** claimed as a first: Eberhardt [E, Theorem 6.1] already gave a non-real-rooted Z-polynomial for a binary rank-12 matroid. His displayed Z coefficients do satisfy ordinary log-concavity. Cheng–Liu concern P, Badalov concerns inverse P, and Gao–Ruan–Xie concern inverse Z: these are different polynomials.

## 1. Rank-flag formula

For increasing rank lists S in {1,...,r−1}, let f(S) count strict flags of flats with those intermediate ranks; f(∅)=1. For general r≥6 put
     
    A = f(r−1)
    B = f(r−2) + f(r−3,r−1) − f(r−3,r−2)
    C = f(r−3) + f(r−4,r−1) − f(r−4,r−3)
        + f(r−5,r−2) − f(r−5,r−3)
        + f(r−5,r−3,r−1) − f(r−5,r−3,r−2)
        − f(r−5,r−4,r−1) + f(r−5,r−4,r−3).                 (1)

These are z₁,z₂,z₃. Indeed compute z_{r−j} in the defining sum and use palindromicity. For a rank-d interval N with d≥3 the coefficient [t]P_N equals (# coatoms)−(# atoms): compare opposite degree-one positions of Z_N. For a rank-five interval, [t²]Z_N = f_N(3)+f_N(2,4)−f_N(2,3) by the high coefficient; in its low coefficient the nonempty flat terms are f_N(2)+f_N(1,4)−f_N(1,2). Their difference is [t²]P_N. For j=1 only corank 1 contributes to [t^{r−1}]Z_M; for j=2 only coranks 2 and 3 contribute; for j=3 only coranks 3,4,5 contribute. Substitute the preceding rank-d formulas and concatenate the lower flat rank to its upper flag. This gives (1) including the middle coefficient when r=6.

## 2. Count the flags, including the coalesced hyperplanes

Write P_d(q) for the projective geometry of vector rank d, B_n for the free matroid on n elements, and F_{d,n}(S) for flags at ranks S of P_d(q) ⊕ B_n. End ranks 0,d+n are allowed when useful. With s=max S, the following recursion counts by the largest flat (Gaussian binomials use parameter q):

    F_{d,n}(∅)=1,
    F_{d,n}(S)=∑_{a+b=s} [d choose a]_q binom(n,b) F_{a,b}(S\{s}).        (2)

For rank seven, the hypotheses of [BCEL, Definition 4.15 and Proposition 4.16] hold: q=103 is prime, N=q³ meets the allowed range 4≤N≤q³, and N≥13. In particular a bijection from the cyclic group of size N to the underlying set of the cubic extension field exists, as required in Definition 4.15. Fix any such bijection. The resulting abstract matroid is simple and 3-connected; its flag counts are

    f(S)=F_{6,N}(S),                                            6∉S,
    f(T ∪ {6})=F_{6,N}(T ∪ {6}) + q⁶ binom(N,4)
                  [F_{3,4}(T)−F_{3,4}(T ∪ {6})].               (3)

Thus (1)–(3) are already a finite explicit formula for each asserted exact integer, with no enumerations of the large ground set or unstated oracle. In the primary witness z₁,z₂,z₃ are as displayed. Computational attachment characteristic_check.py independently obtains the same numbers without using (1), from the defining EPW characteristic-polynomial recursion.

## 3. Optional rank-six refinement of the same construction

For 3≤k≤4 put r=3+k. Let X be a cyclic group of size N=q³. Let V=U⊕K where U=F_q³ and K=F_{q³} as an F_q-vector space. Start with the rank-r truncation M₀ of P(V)⊕B_N (retain all flats of rank <r and replace the top by the full ground set). Fix a bijection ι:X→K, an F_q-basis e₁,e₂,e₃ of U, and an F_q-basis β₁,β₂,β₃ of K. The F_q-linear map

    Φ: Hom(U,K) → K,    A ↦ ∑ β_i A(e_i),

is surjective, has q⁶ maps per fiber, and its kernel has no nonzero rank-one map: such a map takes e_i to c_i v with c_i∈F_q and fixed nonzero v, and ∑β_i c_i v=0 forces all c_i=0. For each k-subset D of X select all blocks

    P(graph A) ⊔ D,     Φ(A)=ι(∑_{x∈D} x),

where the sum is in the cyclic group X. Each block is a proper rank-r flat before truncation, hence spanning in M₀, and the closure of every (r−1)-element independent subset of the block stays in the block (lower-rank closures agree with the pre-truncation). For distinct blocks: if A agrees then the distinct D have equal sums, hence intersection size ≤k−2; if D agrees then A−A' is nonzero in the kernel of Φ and the graphs intersect in dimension ≤1; if both differ, the graph intersection dimension ≤2 and the auxiliary intersection size ≤k−1. In all cases intersection rank ≤r−2. This verifies the hypotheses of [BCEL, Lemma 3.7]; see also their Lemma 3.9 for the general flag change: the coalescence exists, preserves all ranks below r−1, and replaces old hyperplanes contained in each block with one new hyperplane.

There are c=q⁶ binom(N,k) blocks. Each old block restriction was P₃(q)⊕B_k, so (3) is valid with r−1, k in place of 6,4 and with c as above. Indeed each removed hyperplane belongs to a unique block, and flag counting by the largest flat gives the correction. Rank-six simplicity follows because rank-one/two data are unchanged. For N≥2r−1 any bipartition has a part containing r auxiliary elements; these form a retained basis since no block contains r auxiliary elements. If each part has at least two elements, the connectivity value equals the rank of the nonspanning part (or equals r if both span), ≥2 by simplicity; singletons similarly give connectivity ≥1. Thus the examples are 3-connected.

At k=3,q=149 the complete coefficient sequence has the form (1,A,B,C,B,A,1), with exact values and a negative defect in certificate.json. This construction follows BCEL closely but replaces their four-element blocks by three-element blocks. Its matroid need not be representable for the negative statement. No statement about minimal rank is made.

## 4. The size of failure is unbounded in fixed rank

For N=q³, (1)–(3) make A,B,C rational polynomials in q. Each product-poset flag contribution is a sum of products of Gaussian multinomials for the geometric factor (degree at most binom(6,2)=15, by refinement to a full flag) and a multinomial for auxiliary choices (as polynomial in N, degree at most the largest rank ≤6, so degree ≤18 in q). The block adjustment has degree at most 6+3k+binom(3,2)≤21. Therefore all three coefficient polynomials have degree ≤33. Their exact degrees and leading terms, obtained by forward differences in (1)–(3), are:

    k=3 (rank 6): A ~ q^17/24;  B ~ (17/12) q^17;  C ~ q^18/3.
    k=4 (rank 7): A ~ q^20/120; B ~ (13/24) q^20;  C ~ q^21/3.

For reproducibility, forward_check.py evaluates the polynomials at q=1,...,35 as formal integer arguments; no field is assumed at those non-prime powers. A degree ≤33 polynomial's degree and leading coefficient are determined by its final nonzero constant row of forward differences divided by that row’s index factorial. At q=1 the Gaussian polynomial evaluates to the ordinary binomial; the formulas also make sense when q³<k by the convention binom(n,k)=0 for 0≤n<k. This gives an exhaustive finite identity check (not extrapolation from sample large primes). Consequently B²/(A C) ~ (289/2)/q in rank six, and ~ (845/8)/q in rank seven. In particular this ratio tends to zero as q→∞ through primes. The numerical certificate alone, independently of this strengthening, suffices for the negative answer.

## Checks, attribution and cautions

Run from this directory with Python 3.9+. The first two checks require only the standard library; the optional symbolic check uses SymPy and was tested with the version printed by the script.

```sh
python3 -B -O forward_check.py | diff -u certificate.json -
python3 -B -O characteristic_check.py
python3 -B -O symbolic_check.py
```

* forward_check.py counts flags going up by choosing new quotient subspaces/auxiliary elements and applies (1) explicitly; the Gaussian product is computed as a quotient of exact integers. Output is certificate.json.
* characteristic_check.py counts flags going down using (2), computes Gaussian values by Pascal recurrence, expands Möbius functions over chains, and takes high coefficients of the original EPW relation t^rP_M(1/t)=∑_F χ_{M|F}(t)P_{M/F}(t). It does not import the first implementation; uses the defining sum for the entire Z and checks the displayed Turán determinants. Controls: Boolean and projective matroid Z-polynomials through rank nine. Both scripts were run with Python optimized mode too.
* A third optional verifier, symbolic_check.py, works in the exact polynomial ring Q[q]. It enumerates rank increments by the product of a Gaussian multinomial and a falling factorial, then reconstructs P from the palindromicity of Z and the KL degree cutoff. It does not import the two other checkers, use formula (1), or interpolate. It confirms the complete coefficient lists and leading terms; in particular the leading terms of B²−AC are −q³⁵/72 and −q⁴¹/360 at ranks six and seven, respectively.
* All three implementations share the geometric flag count (3), a mathematical input supported by [BCEL]. None enumerates every flat of the final matroid. No Lean or external human review is claimed. AI assistance in the research, calculations and draft is disclosed.
* This is NOT a claim about the ordinary inverse polynomial Y_M, or the multichain-counting zeta polynomial of a poset (also called Z in [BCEL]); those are different invariants. No counterexample to Y log-concavity is claimed.
* Search in public arXiv, author and journal sources and recent announcement pages through 2026-11-18 located no earlier ordinary Z non-log-concavity result. That is a bounded priority check, not certification of worldwide novelty.

### Sources

[PXY] N. Proudfoot, Y. Xu, B. Young, *The Z-polynomial of a matroid*, Electronic Journal of Combinatorics 25 (2018), P1.26. Conjecture 5.1, Conjecture 6.5 and Remark 6.6. https://arxiv.org/abs/1706.05575

[EPW] B. Elias, N. Proudfoot, M. Wakefield, *The Kazhdan–Lusztig polynomial of a matroid*, Advances in Mathematics 299 (2016), 36–70. The degree condition and characteristic recurrence characterize P. https://arxiv.org/abs/1412.7408

[BCEL] G. Bérczi, B. Coron, C. Eur, S. Li, *Chow polynomials and chain polynomials of matroids are not log-concave*, 12 October 2026, arXiv:2610.17135v1, Lemmas 3.7 and 3.9, Definition 4.15, Proposition 4.16. https://arxiv.org/abs/2610.17135v1

[E] J. N. Eberhardt, *Condensed configurations and valuative matroid invariants*, 17 September 2026, Theorem 6.1. https://arxiv.org/abs/2609.20903

Cheng–Liu: https://arxiv.org/abs/2607.24186 (ordinary P); Badalov: https://arxiv.org/abs/2609.13417 (ordinary inverse Q); Gao–Ruan–Xie: https://doi.org/10.1016/j.jcta.2026.106220 (inverse Y).
