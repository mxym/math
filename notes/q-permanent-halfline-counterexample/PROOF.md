# A minimal counterexample to da Fonseca's extended q-permanent monotonicity conjecture

Research note, 8 October 2026. Exact arithmetic certificates and an independently implemented verification accompany the proof. No human peer review or Lean verification is claimed.

## Scope

This note disproves **da Fonseca's extension of monotonicity to a half-line ending at +infinity**, stated in Conjecture 1 of the 2010 paper [F10], p. 1259. It does **not** disprove or prove Bapat's original monotonicity conjecture on [-1,1].

The 2010 paper defines A>0 to mean real symmetric positive definite. Its conjecture asks for a left endpoint at or below -1 such that the q-permanent is strictly increasing to +infinity; the exact endpoint inequality glyph is not reliably preserved in the inspected mirror OCR. The displayed 2010/2018 statements omit the non-diagonal qualifier locally, while the 2020 restatement [M20, pp. 917–918, Remark] explicitly excludes diagonal matrices. We address that meaningful non-diagonal formulation. The 2018 manuscript [F18, Conjecture 2] explicitly uses a left endpoint strictly below -1. Our decrease between q=49 and q=50 contradicts either endpoint version.

We give an exact rational positive-definite counterexample of order four, prove that order four is minimal, and prove a stronger structural result: **for every t>1, some real symmetric positive-definite correlation matrix A has P'_t(A)<0.** Thus there is no dimension-independent enlargement of the right endpoint 1 on which all such q-permanents can be increasing.

## 1. Definition and exact counterexample

For a matrix A=(a_ij) of order n, define

P_q(A) = sum over sigma in S_n of q^{inv(sigma)} product_{i=1}^n a_{i,sigma(i)},

where inv(sigma) counts pairs i<j with sigma(i)>sigma(j). In particular, the order of the indices is part of the definition.

Let

A =
[ 1       -99/100   0   1/500 ]
[ -99/100  1        0   1/8   ]
[ 0        0        1   0     ]
[ 1/500    1/8      0   1     ].

Its successive leading principal minors are

1, 199/10000, 199/10000, 59/15625.

They are strictly positive, so Sylvester's criterion gives A>0. Equivalently, index 3 is an isolated identity block and the remaining 3-by-3 correlation block is positive definite.

Only the six permutations acting on {1,2,4} can contribute. Their contributions are:

- Identity: 1.
- (1 2), inversion number 1: (9801/10000) q.
- (2 4), inversion number 3: (1/64) q^3.
- (1 4), inversion number 5: (1/250000) q^5.
- (1 2 4) and (1 4 2), each of inversion number 4: together -(99/200000) q^4.

Consequently,

P_q(A) = 1 + (9801/10000)q + (1/64)q^3 - (99/200000)q^4 + (1/250000)q^5.

Direct rational arithmetic gives

P_49(A) = 81807513/500000,
P_50(A) = 7969/50,
P_49(A) - P_50(A) = 2117513/500000 > 0.

Since 49<50, strict increase fails. This is a complete counterexample to [F10, Conjecture 1] and [F18, Conjecture 2]. It does not depend on numerical optimization or a derivative criterion.

For an additional exact check,

P'_50(A) = -10831/2500 < 0.

## 2. Minimal order

We prove the following elementary fact, consistent with the known order-three result in [M20].

**Proposition.** If A is a non-diagonal Hermitian positive-definite matrix of order at most three, then P_q(A) is strictly increasing on the entire real line.

**Proof.** Multiplying A on both sides by a positive diagonal matrix changes every permutation monomial by the same positive factor. We may therefore normalize the diagonal to 1.

Order two is immediate: P_q(A)=1+|a_12|^2 q.

For order three write a=a_12, b=a_13, c=a_23, and r=Re(a c conjugate(b)). Then

P_q(A) = 1 + (|a|^2+|c|^2)q + 2r q^2 + |b|^2 q^3,
P'_q(A) = |a|^2+|c|^2+4rq+3|b|^2 q^2.

Positive semidefiniteness implies |a|,|c| <= 1. If b=0, the derivative is the positive constant |a|^2+|c|^2, since A is not diagonal.

If b is nonzero, completing the square yields

P'_q(A) = 3|b|^2(q+2r/(3|b|^2))^2
           + |a|^2+|c|^2 - 4r^2/(3|b|^2).

Using r^2 <= |a|^2|b|^2|c|^2 and 2xy <= x+y for 0<=x,y<=1, we obtain

|a|^2+|c|^2 - 4r^2/(3|b|^2)
>= |a|^2+|c|^2 - (4/3)|a|^2|c|^2
>= (|a|^2+|c|^2)/3.

Thus the derivative is everywhere positive if a or c is nonzero. In the remaining case a=c=0 and b is nonzero, P_q(A)=1+|b|^2 q^3, also strictly increasing. This proves the proposition. Therefore the order-four counterexample is dimensionally minimal. QED.

The proposition also holds for non-diagonal Hermitian PSD matrices with positive diagonal, by the same proof. No claim of novelty is made for the low-order positivity fact itself.

## 3. The mechanism: spacing a signed triangle

Let n>=4, and let A be the identity matrix except for

a_12=a_21=a,
a_1n=a_n1=b,
a_2n=a_n2=c.

All indices 3,...,n-1 are isolated identity coordinates. Put m=2n-5, which is odd and at least three. The six contributing permutations give the identity

P_q(A) = 1+a^2 q+c^2 q^m+2abc q^{m+1}+b^2 q^{m+2}.             (1)

To check the exponents directly:

- inv((1 2))=1;
- inv((2 n))=2(n-2)-1=m;
- inv((1 n))=2(n-1)-1=m+2;
- inv((1 2 n))=inv((1 n 2))=2n-4=m+1.

The scalar identity coordinates do not disappear from the inversion statistic. This is why deleting them or simultaneously permuting the triangle into contiguous coordinates would change the q-permanent.

For q>0, (1) may also be written

P_q(A)=1+a^2q+q^m[(c+abq)^2+(1-a^2)b^2q^2].                (2)

Our examples have |a|<1, so their q-permanents are positive for every q>0. The obstruction is genuine loss of monotonicity, not a sign change of the function.

## 4. No universal right extension past 1

**Theorem.** For every real number t>1 there are n>=4 and a real symmetric positive-definite correlation matrix A of order n such that P'_t(A)<0. A can have all but three off-diagonal pairs zero. It can alternatively be chosen to have rational entries and no zero off-diagonal entries.

**Proof.** Choose an odd integer m>=3 sufficiently large that

t^{m-1} > 32(m+1)^2(m+2).                                 (3)

Such an m exists because t>1 and exponential growth dominates any polynomial along the odd integers. Put

n=(m+5)/2,
delta=1/[2(m+1)^2],
a=-sqrt(1-delta),
c=sqrt(delta/8),
b= -a(m+1)c/[(m+2)t].

In particular a<0, b>0, c>0, and b/c<1. Define A by the spaced-triangle construction of Section 3.

We first verify positive definiteness, without any limiting or numerical argument. Permuting the indices only for this verification, A is the direct sum of an identity matrix and

C = [1 a b; a 1 c; b c 1].

The leading minors of C are 1, delta, and

det(C)=1-a^2-b^2-c^2+2abc
      =delta-[b^2+c^2+2|a|bc].

Since b<c and |a|<1,

b^2+c^2+2|a|bc < 4c^2 = delta/2.

Hence det(C)>delta/2>0, proving C>0 and A>0.

For differentiation, A is fixed; t is the chosen evaluation point, not a variable in its entries. From (1),

P'_t(A)=a^2+c^2 t^{m-1}[m+2(m+1)a x+(m+2)x^2],

where x=bt/c=-a(m+1)/(m+2). Substitution gives

m+2(m+1)a x+(m+2)x^2
=m-[(m+1)^2/(m+2)]a^2
=[-1+(m+1)^2 delta]/(m+2)
=-1/[2(m+2)].

Therefore

P'_t(A)=1-delta - t^{m-1}/[32(m+1)^2(m+2)] < -delta < 0,

where the strict inequality uses (3).

Finally, positive definiteness and P'_t(A)<0 are open conditions on the real symmetric matrix entries. Keeping the diagonal equal to 1, choose a sufficiently small rational perturbation of all off-diagonal entries, making each nonzero. The resulting rational correlation matrix remains positive definite and still has P'_t(A)<0. This proves the last assertion. QED.

**Corollary.** For every epsilon>0, there is a real symmetric positive-definite matrix whose q-permanent is not increasing on [1,1+epsilon], hence not on [-1,1+epsilon].

**Proof.** Apply the theorem at t=1+epsilon/2. By continuity of the derivative, the q-permanent decreases on a sufficiently small interval around t contained in (1,1+epsilon). QED.

This corollary rules out every uniform enlargement of the proposed Bapat interval to the right. It leaves the original interval [-1,1] unresolved.

## 5. Verification and limits

- The order-four polynomial, all leading minors, the values at 49 and 50, and the derivative at 50 are reproduced using exact rational arithmetic by `verify_exact.py`.
- The script independently enumerates all permutations; it does not call the numerical search implementation.
- The general theorem is a symbolic human-readable argument, not an extrapolation from experiments.
- The accompanying independent audit verifies the exact 4-by-4 counterexample, all 15 principal minors, the order-three argument, and the general t>1 construction. This is not a claim of formal Lean verification, human peer review, or established priority.
- The current literature search found no prior disproof of the stated real positive-definite half-line conjecture. That negative search is not proof that none exists. See `SOURCE_AUDIT.md` for precise scope and limitations.

## References

[F10] C. M. da Fonseca, The mu-permanent of a tridiagonal matrix, orthogonal polynomials, and chain sequences, Linear Algebra and its Applications 432 (2010), 1258–1266. DOI: https://doi.org/10.1016/j.laa.2009.10.036. Conjecture 1 is on p. 1259. The full journal-mirror OCR was inspected (the original-page endpoint inequality glyph was not verified) at https://www.academia.edu/103682178/The_%CE%BC_permanent_of_a_tridiagonal_matrix_orthogonal_polynomials_and_chain_sequences.

[F18] C. M. da Fonseca, The mu-permanent revisited, arXiv:1804.02231v1 (2018), Conjecture 2. https://arxiv.org/abs/1804.02231. We cite the nine-page arXiv manuscript for this conjecture, not the differently paginated two-page journal version.

[M20] L. Mitchell, A note on Bapat's q-permanent conjecture, Operators and Matrices 14 (2020), 915–919. DOI: https://doi.org/10.7153/oam-2020-14-56. Published PDF: https://files.ele-math.com/articles/oam-14-56.pdf. The remark across pp. 917–918 distinguishes the positive-definite half-line conjecture from its false singular extension.
