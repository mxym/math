# A padding proof of Pan–Skandera–Wang Conjecture 9.3

Date: 2026-10-08. This note proves the reduction from the cited balanced theorem; it does not independently re-prove that theorem. No priority claim is made.

## Precisely identified target and current source

Sihong Pan, Mark Skandera, Jiayuan Wang, *Permanental inequalities and unit interval orders*, arXiv:2610.04809v1 [math.CO], dated 3 October 2026.

- Authoritative full text: https://arxiv.org/html/2610.04809v1
- Stable abstract/version record: https://arxiv.org/abs/2610.04809
- Conjecture 9.3: for every n-by-n totally nonnegative matrix A and h in [n], putting I=[h] and J=[n] intersect 2Z, one has per(A[I,I]) per(A[I^c,I^c]) >= per(A[J,J]) per(A[J^c,J^c]).
- Theorem 8.18 in THE SAME PAPER proves this inequality when h=floor(n/2) or h=ceil(n/2).

## Definitions

For n a nonnegative integer, [n]={1,...,n}, with [0]=empty. A real n-by-n matrix is totally nonnegative (TNN) if every square submatrix has nonnegative determinant. For S subset [n], A[S] means the principal submatrix with rows and columns in S, ordered increasingly. The permanent of an m-by-m matrix C is sum over permutations sigma of [m] of the product over i in [m] of C[i,sigma(i)]. The empty permanent is 1. Write O_n for odd indices in [n] and E_n for even indices in [n]. For d>=0, I_d is the identity of order d, including the empty identity I_0.

## The one external mathematical theorem used

**Balanced permanent inequality (Pan–Skandera–Wang, Theorem8.18).** For every integer m>=2 and every TNN matrix B of order 2m,

per(B[[m]]) per(B[{m+1,...,2m}]) >= per(B[O_{2m}]) per(B[E_{2m}]).

The cited preprint statement covers arbitrary order and either balanced cut; only this even-order case is used. The m=1 case is equality and needs no external theorem. The proof in the source obtains this from its Theorems7.1 and8.17, the latter being the all-dimensional Bruhat-order comparison.

## Elementary lemmas, with proofs

**Lemma1 (ordered direct sums preserve total nonnegativity).** If C and D are TNN matrices, then C direct-sum D is TNN.

Proof. Choose an arbitrary square submatrix of C direct-sum D. Let r and s respectively be the numbers of selected rows and columns belonging to the C block. If r=s, the submatrix is block diagonal, in the inherited order, with one square submatrix of C and one of D; its determinant is the product of their nonnegative determinants. If r>s, the first r selected rows have all nonzero entries confined to s selected columns and are linearly dependent, so the determinant is zero. If r<s, apply the same argument to the first s selected columns, which have nonzero entries confined to r selected rows. In every case the determinant is nonnegative. This includes empty blocks. QED.

**Lemma2 (permanent factorization).** For arbitrary square matrices C,D, per(C direct-sum D)=per(C)per(D).

Proof. Any permutation that sends some index of the C block into the D block has a zero factor. Every surviving permutation preserves both blocks, and corresponds uniquely to a pair of permutations, one of each block. Its product factors accordingly; summing proves the identity. The argument remains valid if either block is empty. QED.

In particular, every principal submatrix of I_d has permanent1. By Lemma1, padding a TNN matrix on either end by I_d preserves total nonnegativity.

## Full theorem and proof

**Theorem.** For every integer n>=1, every real TNN matrix A of order n, and every integer h with 0<=h<=n,

per(A[[h]]) per(A[{h+1,...,n}]) >= per(A[O_n]) per(A[E_n]).

In particular, this proves the exact whole statement of Conjecture9.3.

Proof. First suppose 0<h<n.

Case1: 2h<=n. Set d=n-2h, m=n-h, and B=I_d direct-sum A. Then d>=0 and B has order d+n=2m. By Lemma1 it is TNN. Its leading principal block of order m=d+h is I_d direct-sum A[[h]], and its trailing principal block of order m is A[{h+1,...,n}]. Lemma2 therefore gives

per(B[[m]]) per(B[{m+1,...,2m}]) = per(A[[h]]) per(A[{h+1,...,n}]).

The original index i of A becomes d+i in B. If d is even, parity is unchanged; if d is odd, parity is exchanged. Each of B's two parity-selected principal submatrices is an ordered direct sum of a principal submatrix of I_d and one of A[O_n], A[E_n]. The identity parts have permanent1. It follows in either parity case that

per(B[O_{2m}]) per(B[E_{2m}]) = per(A[O_n]) per(A[E_n]).

For m>=2 apply the balanced theorem to B and substitute these two equalities. If m=1, the assumptions 0<h<n and 2h<=n force n=2,h=1; the claimed inequality is equality.

Case2: 2h>=n. Set d=2h-n, m=h, and B=A direct-sum I_d. Again B is TNN of order n+d=2m. Its two balanced principal blocks are A[[h]] and A[{h+1,...,n}] direct-sum I_d. Each parity-selected principal submatrix is A[O_n] or A[E_n], followed by an identity principal submatrix. Thus the same two product equalities hold. Apply the balanced theorem if m>=2; m=1 again reduces to n=2,h=1.

These cases exhaust all interior h; when 2h=n either argument has d=0.

Finally, if h=0 or h=n, the left side is per(A). Since all entries of A are nonnegative, the permanent is a sum of nonnegative monomials. The summands from permutations preserving O_n and E_n form exactly per(A[O_n])per(A[E_n]), a subset of all summands. The desired inequality follows. This also covers n=1, all possible h, and empty parity sets. QED.

## Scope, novelty, and limits

The proof is universal and exact; it does not infer anything from computation. It covers singular TNN matrices, entries equal to zero, all matrix orders, and every cut h. It relies on the already proved balanced theorem, not on a stronger unproved extension. The new argument is short: the general-cut conjecture is equivalent to the collection of balanced inequalities in all dimensions, through ordered identity padding. The substantive balanced work belongs to Pan–Skandera–Wang. This result should be described as a resolution/corollary by padding, not as an independent proof of their balanced theorem or as a major new inequality technique.

## Verification checklist

- Exact target Conjecture9.3 checked in latest primary text.
- Theorem8.18 explicitly quantifies over all TNN matrices, with no irreducibility, positivity, normalization, or fixed-order restriction.
- Identity direct sums are admissible TNN matrices, including singular minors.
- Parity shift under left padding either preserves or exchanges the two factors; their product is unchanged.
- Total dimension is even and the intended cut is exactly the middle.
- The boundary h=n in the original conjecture is explicitly handled; h=0 included as harmless strengthening.
- Small dimensions not covered by the source's n>=4 Bruhat theorem are proved directly.
- No data, simulation, or unverified source is used in the proof.
