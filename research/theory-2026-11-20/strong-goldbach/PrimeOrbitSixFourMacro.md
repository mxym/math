# With four macroscopic labels, exactly one is near-linear

Fix p and F as in the [six-label smooth orbit theorem](PrimeOrbitSixSmoothTerminal.md). Along an unbounded six-label orbit at even F-smooth centers N, coprime to p, take any convergent subsequence of logarithmic weights with four positive limits. Then **exactly one of the four positive weights equals one**; the other three are strictly between zero and one. The two zero-weight labels are the fixed seed p and the smallest nonseed q, which tends to infinity by the [multi-seed minimum](PrimeOrbitMultiSeedMinimal.md). The other possible logarithmic sector, with three positive weights, is covered by the [balanced three-macro reduction](PrimeOrbitSixTripleMacro.md). This theorem is necessary, not an exclusion of the single-high four-macro sector or a proof of binary Goldbach.

At least one weight is one by the [extreme-label theorem](PrimeOrbitSixTerminalExtremeLabels.md). Write A for the component's exponent matrix, irreducible with nullity(I−A)=2. Every label appears in some composite row, hence is ≤(N−3)/3. We exclude two or more highs, where “high” means weight exactly one.

## Eliminate the high-only paths

Let R be the set of nonhigh labels. On rows with a high successor, the high occurs just once, no second high can occur, and its integral cofactor v≥3 is N^{o(1)} supported on R. There can be no directed cycle of length j entirely on the highs, as composition of the affine equations N−x_i=v_i x_{i+1} around it would give N|∏v_i−(−1)^j, a positive subpower integer. Thus the outside high block is nilpotent. Its first-return matrix K on R is irreducible with each row sum at least two, and C=K−I has nullity two by Schur elimination. Every entry of K is O(log N), since each retained row has at most one continued high path with multiplicity one on every continued arc, length at most six; the terminal small exponents along the path add, each O(log N).

For a path starting at x∈R, of length j≥0 through high successors ending at the first node with no high successor, its multiplicative row identity is

    ρ_x=∏_{y∈R} y^{C_xy}=(D_x N+σ_x x)/x,      σ_x=(-1)^{j+1}.              (1)

With V_0=1,A_0=0,V_i=v_i V_{i−1}, A_i=V_{i−1}−A_{i−1}, the i-th path label is (A_i N+(-1)^i x)/V_i. The return monomial before division by x is the product of V_j and the last complement, giving D_x=V_j−A_j. Always 0<D_x≤V_j=N^{o(1)}. At a zero-length path D_x=1. This identity does not require the retained labels to be subpower; cf. the [balanced-return argument](PrimeOrbitBalancedReturn.md).

If all four macros are high then |R|=2, so nullity C=2 forces C=0, contradicting K's row sums. If three are high, R={p,q,I} includes one intermediate label I of weight strictly between zero and one. Rank C=1 and the [positive rank-one argument](PrimeOrbitBalancedReturn.md) gives C=abᵀ with positive integral vectors. In particular ρ_I is integral. Thus (1) gives I|D_I, impossible since D_I>0 is subpower and I is macroscopic.

## Two highs and a first-order congruence

It remains to suppose R={p,q,I,J}, with I,J both intermediate and C of rank two. The rows at p,q cannot be independent. Otherwise some integral relation c_p C_p+c_q C_q+c_I C_I=0 has c_I≠0 and all |c_i|≪(log N)² by taking signed two-column minors witnessing independence on the small rows. Equation (1) gives ∏ρ_i^{c_i}=1. In the localization of Z at denominators coprime to N, reducing first mod N forces ∏σ_i^{c_i}=1 (N>2). Reduce next mod N² using (1), including any negative exponents by inversion, and divide by N:

    N divides c_p σ_p D_p/p + c_q σ_q D_q/q + c_I σ_I D_I/I.

Multiply by p q I to clear unit denominators. The resulting integer has size at most N^{w_I+o(1)}<N since p,q,D_i and the coefficient bounds are subpower. But it is nonzero modulo I: the last term is c_I σ_I D_I p q, with c_I,D_I nonzero and smaller in absolute value than I. This contradicts divisibility and proves dependence.

The rows C_p,C_q are both nonzero by irreducibility (also by row-sum bounds), and are scalar multiples. Some column Y in {I,J} has a positive entry in at least one small row, since otherwise {p,q} is closed under K, contradicting irreducibility. On that column both entries must be positive, being nonnegative off-diagonal. Then (1) implies Y|D_p N+σ_p p and Y|D_q N+σ_q q (p and q are not Y). Their integer combination D_p σ_q q−D_q σ_p p is subpower, hence zero. This gives σ_p=σ_q, D_p=h p and D_q=h q for some positive integer h. Neither small path has length zero. Therefore the small labels directly target distinct highs H_p,H_q (a common high would divide the small difference) and exhaust both highs. No high targets the other: writing N−p=v_pH_p, N−q=v_qH_q and, for instance, N−H_p=zH_q gives

    N[(v_p−1)v_q−zv_p]=−v_q p−zv_p q,

strictly negative of subpower size on the right. Thus both paths have length one, D_p=v_p−1 and D_q=v_q−1. Their subpower cofactors can only use the two small primes. Each is at least 3 and avoids its own small input, so

    1+hp=q^a,                  1+hq=p^b,                    a,b≥1.             (2)

## The two-prime multiplier cannot have an unbounded partner

From (2), q^{a+1}−q=p^{b+1}−p. Thus the even center N′=q^{a+1}+p=p^{b+1}+q has precisely the two complementary rows at p,q given by the powers q^{a+1} and p^{b+1}. These are composite as a,b≥1; neither label divides N′ and the two labels form a strongly connected, factor-closed nontrivial component. By [Bożek, Theorem 3.7, the classification of two-label exceptional autonomous components](https://arxiv.org/abs/1909.09900), N′=2200 and {p,q}={3,13}. This contradicts q→∞, excluding two highs. The conclusion about exactly one high follows.

**Dated comparison.** [Kelanemer's September 2026 revision](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) treats neighboring exponent matrices; its full text remained inaccessible. This is a restricted six-label shape theorem, not a solution of the remaining single-high branch, balanced branch, or binary Goldbach.
