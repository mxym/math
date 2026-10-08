# Independent audit: identity padding proves Conjecture 9.3 from Theorem 8.18

Audit date: 2026-10-08 (UTC)

## Verdict

**PASS.** The proposed identity-padding reduction is mathematically valid. Taking Theorem 8.18 of the verified paper as an established input, it proves every case of Conjecture 9.3, including odd matrix orders and the endpoint allowed in the actual conjecture. There is no positivity, irreducibility, nonsingularity, normalization, or dimension obstruction in the theorem statement. The proof below checks the reduction independently; it does not re-prove the paper's long combinatorial proof of Theorem 8.18.

## Primary-source identification and checks

The paper is **Sihong Pan, Mark Skandera, and Jiayuan Wang, _Permanental inequalities and unit interval orders_, arXiv:2610.04809v1**, submitted 2026-10-03 23:26:08 UTC. The live abstract page's submission history lists only v1.

Verified primary sources:

- [arXiv abstract and submission history](https://arxiv.org/abs/2610.04809)
- [Versioned full HTML](https://arxiv.org/html/2610.04809v1)
- [Current PDF, 56 pages](https://arxiv.org/pdf/2610.04809)

Theorem 8.18 is on printed PDF page 53; Conjecture 9.3 and its context are on printed page 54. The HTML and PDF text agree. Source verification was by HTML and PDF text; no screenshot verification is claimed.

Using the notation below, Theorem 8.18 asserts F_h(A) ≥ Q(A) for every real n×n TNN matrix when h is floor(n/2) or ceil(n/2). Theorem 8.17, used immediately before it, starts at n≥4; the small orders can be handled directly as below. Conjecture 9.3 asks the same inequality for I=[h], h∈[n]. It remains explicitly under “Open Problems.” This is about initial-segment cuts, not all subsets I. No padding argument is stated in that surrounding text; full-text searches for “padding,” “direct sum,” and “identity matrix” found no matches. This is not a general novelty search.

## Notation

For n≥1 let [n]={1,…,n}, E_n={i∈[n]: i is even}, and O_n=[n]\E_n. For S⊆[n], write A[S] for the principal submatrix A_{S,S}, with its indices in increasing order. Define

\[
F_h(A)=\operatorname{per}A[[h]]\;\operatorname{per}A[\{h+1,\ldots,n\}],
\qquad
Q(A)=\operatorname{per}A[E_n]\;\operatorname{per}A[O_n].
\]

Set per(A[∅])=1 and let I_0 denote the empty matrix. The desired assertion is F_h(A)≥Q(A), for h=1,…,n. The same argument also permits h=0.

## Two elementary facts, proved without additional assumptions

### 1. Ordered block diagonal sums preserve total nonnegativity

Let X and Y be square TNN matrices, of orders p and q, and let C=X⊕Y. Consider a k×k minor C[R,S], with rows and columns in increasing order. Let a be the number of selected rows in the X block and b the number of selected columns in that block.

If a≠b, every term in the determinant expansion is zero. Indeed, a nonzero term must match each selected row from X to a selected column from X, and each selected row from Y to a selected column from Y, because the off-diagonal blocks vanish. A bijection with these properties requires a=b.

If a=b, the selected matrix itself is an ordered block diagonal sum of two square submatrices. Its determinant is the product of their determinants, with no additional sign, and hence is nonnegative. Therefore every minor of C is nonnegative.

Every minor of I_d is either zero or one, so I_d is TNN. Consequently, I_d⊕A and A⊕I_d are TNN whenever A is TNN. Zeros in the off-diagonal blocks are permitted. Strict total positivity is not required.

### 2. Permanents factor over block diagonal sums

For arbitrary square matrices X and Y,

\[
\operatorname{per}(X\oplus Y)=\operatorname{per}(X)\operatorname{per}(Y).
\]

The only nonzero terms in the permanent expansion are the permutations preserving each block, and those permutations are independently chosen within the two blocks. In particular, per(I_d)=1, including d=0. The same reasoning applies to any principal submatrix of a block diagonal sum.

## Full padding proof

Let A be n×n and TNN. Assume first that n≥3, and fix h∈{1,…,n}. Put

\[
m=\max(h,n-h),\qquad p=m-h,\qquad q=m-(n-h).
\]

Then p,q≥0, at least one of p,q is zero, and

\[
B=I_p\oplus A\oplus I_q
\]

has order p+n+q=2m≥4 and is TNN by Fact 1. Its balanced cut after position m=p+h gives

\[
B[[m]]=I_p\oplus A[[h]],
\qquad
B[\{m+1,\ldots,2m\}]
=A[\{h+1,\ldots,n\}]\oplus I_q.
\]

Thus Fact 2 yields the exact equality

\[
F_m(B)=F_h(A). \tag{1}
\]

An original index i of A occurs at index p+i in B. If p is even, the original parity classes are preserved; if p is odd, they are exchanged. Each parity principal submatrix of B is an ordered block diagonal sum of one of A's two parity principal submatrices and principal submatrices of the two identity blocks. All identity factors have permanent one. Therefore, irrespective of p's parity,

\[
Q(B)=Q(A). \tag{2}
\]

Apply Theorem 8.18 to the 2m×2m TNN matrix B at its balanced cut m. Equations (1) and (2) then give

\[
F_h(A)=F_m(B)\ge Q(B)=Q(A).
\]

This proves the whole conjecture for n≥3.

For n=1, h=1, both sides equal a_{11}. For n=2, h=1, both sides equal a_{11}a_{22}; for h=2, the difference is a_{12}a_{21}≥0 because a TNN matrix has nonnegative entries. These observations remove any dependence on a possible implicit n≥4 lower bound inherited by Theorem 8.18 from its preceding combinatorial theorem. The case h=0, if desired, is the same as h=n.

### The two constructions exactly as proposed

- If h≤n/2, then m=n−h, p=n−2h, q=0. Thus B=I_{n−2h}⊕A has order 2(n−h). Its first balanced block is I_{n−2h}⊕A[[h]] and its second is A[{h+1,…,n}]. The shift n−2h may exchange E_n and O_n, but their permanent product is unchanged.
- If h≥n/2, then m=h, p=0, q=2h−n. Thus B=A⊕I_{2h−n} has order 2h. Its first balanced block is A[[h]] and its second is A[{h+1,…,n}]⊕I_{2h−n}. Original indices do not shift, so their parities are unchanged.

## Edge cases and scope

- **Odd n:** In the first construction n−2h is odd, so the A parity factors exchange places. Multiplication is commutative. In the second construction the original indices remain unchanged. In both cases the padded order is even.
- **Balanced even n:** Padding size is zero; this is exactly the cited balanced theorem.
- **h=n:** The actual conjecture permits this endpoint. Choose B=A⊕I_n. The second desired factor is the empty permanent, equal to one. One could also prove this endpoint directly by retaining the parity-preserving terms in per(A).
- **Zero entries, singular matrices, vanishing permanents:** No division, cancellation, perturbation, or limiting argument occurs, so no positivity of any permanent or determinant is needed.
- **No arbitrary reordering:** The padding respects the order of rows and columns. Arbitrary simultaneous permutations need not preserve total nonnegativity and are neither used nor needed.
- **Initial segments only:** This proves the precise Conjecture 9.3. It does not prove an inequality for every arbitrary subset I. The paper gives counterexamples to that broader form; there is no conflict because identity padding cannot change an arbitrary scattered subset into a single cut while preserving the needed order and parity identities.
- **Dependency and novelty:** The proof relies on Theorem 8.18; it is a short deduction from the paper's substantive balanced result. The audit establishes the deduction's correctness and the conjecture's label in the checked version, not priority over all other work or a complete independent verification of Theorem 8.18's internal proof.

## Bottom line

The exact implication is

\[
\text{balanced inequality for all even-order TNN matrices}
\Longrightarrow
\text{Conjecture 9.3 for all orders and all initial-segment cuts}.
\]

The forward implication is the identity-padding argument above. The reverse implication is immediate by specialization. Therefore, over the class of all finite square TNN matrices, the balanced statement and Conjecture 9.3 are equivalent. The checked version states the former as a theorem while retaining the latter as a conjecture.
