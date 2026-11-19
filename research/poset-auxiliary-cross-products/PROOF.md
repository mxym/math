# Five linear extensions test two auxiliary width-two cross-product inequalities

For a poset and three specified elements with ordered *labels* (x,y,z), let F(s,t) count linear extensions L with L(y)−L(x)=s and L(z)−L(y)=t. Chan–Pak–Panova's Canadian J. Math. paper, Corollary 7.3, asserts both auxiliary inequalities CPC1 and CPC2 at width two. CPC2 is

    F(k,ℓ+2) F(k+1,ℓ) ≤ F(k,ℓ+1) F(k+1,ℓ+1).            (A)

This note treats only these auxiliary assertions and two related assertions about signed gaps and rank counts. It is **not** a counterexample to the classical cross-product conjecture of Felsner–Trotter and Brightwell–Felsner–Trotter, which asks for

    F(k+1,ℓ) F(k,ℓ+1) ≥ F(k,ℓ) F(k+1,ℓ+1),   k,ℓ≥1.    (B)

## Five elements suffice

Let o be a least element below chains A₁<A₂ and B₁<B₂. Impose A₁<B₂ and no further comparabilities other than those implied. The two chains, with o included in the first, cover the poset; A₂ and B₂ are incomparable. Its width is exactly two. Mark (x,y,z)=(o,A₁,B₂), an ordered chain in the underlying partial order. After the initial o, the five linear extensions and positive gap pairs are

| word | gaps |
| ---- | ---- |
| AABB | (1,3) |
| ABAB | (1,3) |
| ABBA | (1,2) |
| BAAB | (2,2) |
| BABA | (2,1) |

These are all shuffles of two As and two Bs except BBAA, which places B₂ before A₁. Consequently (A) at k=ℓ=1 reads **2 ≤ 1**. Reversing both poset and triple swaps the two coordinates and gives the dual auxiliary CPC1 counterexample. These are two separate tests: a single instance need not fail both. The paper's Lemma 3.5 already bounds the left side of (A) by **twice** its right side for every poset, with the dual bound for CPC1. The constant 2 is thus exactly attained, even at width two. This does not show sharpness of any weakened form of (B).

## A minimal-size family at every choice of positive gaps

Fix integers k,ℓ≥1. Replace the chains by A₁<⋯<A_a and B₁<⋯<B_b, where a=ℓ+1 and b=k+1. Keep o least, impose A₁<B_b, and mark (o,A₁,B_b). Width remains two since A_a and B_b are incomparable. After deleting o, let i be the position of the first A and j the position of the last B, so F(s,t) counts i=s,j=s+t. For the four entries below one has i<j. The first i−1 positions are B, position i is A, position j is B, and all after j are A. Precisely b−i B's must occupy the j−i−1 interior slots, and the chain orders determine all labels. The number is therefore binom(j−i−1,b−i). Since i<j, every such word already obeys A₁<B_b. Substitution gives

    F(k,ℓ+2)=ℓ+1,   F(k+1,ℓ)=1,   F(k,ℓ+1)=ℓ,   F(k+1,ℓ+1)=1.

Thus (A) fails at each prescribed (k,ℓ); its RHS/LHS is ℓ/(ℓ+1). This is the same ratio as in the authors' width-three family (Proposition 7.1, there ℓ≥2). The present family has k+ℓ+3 points, the least possible at the prescribed pair: failure requires F(k,ℓ+2)>0 and hence ranks differing by k+ℓ+2 on the first and third marked elements. It also has the smallest possible width: on a chain the sole extension cannot realize both distinct gap pairs on the left of (A).

## Signed-gap and absolute-rank assertions

Use the very same five-element example but relabel the triple as (A₁,o,B₂). For its now-signed gap counts F′ the identity is F′(s,t)=F(−s,s+t). This is exactly the authors' change of labels in their Proposition 7.2. Take (s,t)=(−2,3). The signed adjacent rectangle has diagonal product

    F′(−2,3) F′(−1,4)=F(2,1) F(1,3)=2,

but antidiagonal product

    F′(−2,4) F′(−1,3)=F(2,2) F(1,2)=1.

All four entries are positive, all have s<0,t>0,s+t>0, and all counted extensions have the *same* order o<A₁<B₂. This is contrary to the signed rectangle of Theorem 3.3 / (3.1) as stated in the authors' version of their Transactions paper. It is not a positive-gap instance of Theorem 1.6 there.

On deleting o, mark x=A₁ and z=B₂ and let R(i,j) count extensions with absolute ranks L(x)=i,L(z)=j. The five words above give

                j=3  j=4
       i=1        1    2
       i=2        1    1

so the positive-minor assertion of Corollary 3.4 as stated there would read **1 ≥ 2**. Our marked pair is comparable, but this does not put it in the same constituent chain of a two-chain partition: if A₁ and B₂ were both in one chain, the incomparable A₂ and B₁ would have to be in the other. The downstream Graham–Yao–Yao correlation inequality is an established theorem by other proofs. Nothing here contradicts it. The classical positive-gap conjecture for arbitrary widths is not settled; in particular this note is not an objection to its existing width-two theorem.
