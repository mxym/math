# A positive-branch series test bounds every historical mixed exponent signature

Fix the complete exponent matrix A of an exceptional autonomous component (EAC) in [Bożek’s prime-factor graph](https://arxiv.org/abs/1909.09900): the distinct prime labels satisfy x_i+∏_j x_j^{A_ij}=N, and 3≤x_i≤N/3. Names such as x₃ below refer to indices of vertices in a **historical example**; the integer assigned to each index may change in another realization. Nothing here asserts that every EAC has one of these signatures. The cited paper reports six examples through 10⁸; all six centers have Goldbach representations.

**Theorem.** A fixed invertible exponent matrix A with every coordinate of w=A⁻¹1 strictly between 0 and 1 admits an effective height obstruction if the finite series test below succeeds. It succeeds on **all five mixed-row signatures** of the represented examples 128, 1718, 1862, 1928, 6142. Thus each of the six historical signatures, allowing all its prime labels to vary, has effectively bounded centers: for the remaining pure 2200 case see [the prime-power cycle height bound](EACPureCycleHeight.md), or Bożek’s much stronger Theorem 3.7, classifying the entire two-label case. We do not determine all centers realizing the five mixed signatures. A failed series test for a given polynomial is not a proof that a signature occurs.

Let D be the least denominator of w, d_i=D w_i ∈ {1,…,D−1}, and s=N^(−1/D). Put Y_i=s^{d_i}x_i. The exact log equations are
     
    ∏_j Y_j^{A_ij}=1−s^{D−d_i}Y_i,
    u_i=∑_j B_ij log(1−s^{D−d_j}exp u_j),   B=A⁻¹,  u_i=log Y_i.       (1)

There is a unique small holomorphic branch (Y_i(0)=1), with rational Taylor coefficients, containing every sufficiently large positive realization. Here are uniform effective controls for this fixed A. Write S=max_i∑_j|B_ij| and R=1/[16(1+S)]. On complex |s|≤R and ∥u∥∞≤1, each z=s^{D−d_j}exp u_j has |z|≤3R. Both |log(1−z)| and |z/(1−z)| are ≤4R (use the power series at zero). The right side of (1) maps the closed unit ball strictly inside itself and has derivative norm ≤4RS<1/4. Iteration from zero gives the unique fixed point in this ball, holomorphic inside the disk and uniformly bounded up to the boundary. The coefficients are rational by the recursive identity, since all D−d_j are positive. At a physical tuple (1) first gives |u_i|≤S log(3/2) because x_j/N≤1/3. Thus at positive s≤R(2/3)^{⌈S⌉}, each s^{D−d_j}Y_j≤R, and (1) once more gives |u_i|≤2RS<1. This places the *actual* tuple on the certified small branch; no completeness or geometric irreducibility of other complex branches is assumed.

For an integer polynomial P(X)=∑_ν c_ν X^ν, let H=max_ν∑d_iν_i. The function F(s)=s^H P(x(s)) is holomorphic there and |F(s)|≤K=∑|c_ν|3^{∑ν_i}. Check a finite Taylor expansion exactly: if F has its first nonzero term c s^{H+ℓ} for some ℓ≥1, equivalently P(x(s))=c s^ℓ+O(s^{ℓ+1}), it follows that N is bounded. Indeed Cauchy's estimate and summation of a geometric series give
     
    |P(x(s))−c s^ℓ| ≤ 2K R^{−(H+ℓ+1)}s^{ℓ+1}       (0<s≤R/2).

For s≤s₀=min(R/2, R(2/3)^{⌈S⌉}, |c|R^{H+ℓ+1}/(4K), 1/[4(1+|c|)]), this would give a nonzero integer of magnitude <1. Hence N<s₀^(−D) (allowing ≤ also suffices). It is legitimate to search for P by rational linear algebra on the truncated series of several monomials; the proof only uses the final specified P and its independently checkable series. This is a direct rational-branch Runge-type obstruction, not a universal claim about every invertible A.

### Exact controls

The following integer polynomials and leading terms are reconstructed by the companion checker from the even centers alone. Write z_p for the label in the position of the historical prime p. The final column gives a deliberately loose explicit power-of-ten bound using the stated formula, not the maximum realized center.

| Historical signature | D | integer P | first term | upper bound |
|:---|---:|:---|:---|:---|
|128|12|z₁₁−z₃²−z₃|−s|10^190|
|1718|14|3z₅−3z₃−4|(14/3)s²|10^168|
|1862|6|2z₅−2z₃−3|(11/4)s|10^45|
|1928|9|z₅−z₃²+2z₃−1|4s²|10^123|
|6142|54|2z₇z₁₇−4z₃²z₁₃−2z₅z₁₃+2z₃²z₇+2z₅³−4z₃−z₅z₁₇+z₃⁴|2s⁴|10^3987|

Run `python3 -O check_eac_historical_jets.py` (standard library). It factors every actual complement, rebuilds all strongly connected components and isolates the unique special component for each example. It computes B and the jets by exact rational arithmetic. As a distinct cross-check it literally multiplies the truncated polynomials on both sides of EACH defining equation in (1); uniqueness above then identifies those jets. Finally it substitutes the displayed integer P, verifies every preceding coefficient vanishes and the specified coefficient has the displayed sign and magnitude, and calculates the power-of-ten height bound by exact integer arithmetic. These are fixed-signature finiteness results, not a search ruling out other signatures or an unconditional Goldbach proof.

The six represented centers have, for example, the prime pairs 19+109, 19+1699, 31+1831, 61+1867, 47+2153 (the pure case), and 11+6131, respectively in increasing-center order. The [related Kelanemer 2026 graph record](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) addresses islands under a global hypothesis. Its full latest text was not accessible; neither the local series criterion nor the actual finite fixtures presume such a hypothesis or assert priority over that text.
