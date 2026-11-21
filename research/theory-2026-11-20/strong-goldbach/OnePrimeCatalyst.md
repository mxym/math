# One prime suffices to stabilize every equal-weight fiber of the binary Goldbach ring

Write P for the positive odd primes. A binary move replaces a pair of entries of a multiset in P by two odd primes of the same sum. For any two FIXED multisets A,B in P of the same size d and the same sum n, a set of primes t of **relative density one** has the following property: A∪{t} can be taken to B∪{t} by at most 3d+2⌊(d+1)/3⌋ binary moves. Here union adds multiplicities. In particular the added multiset has just one entry, shared by both ends, not a growing list; the prime t is not fixed in advance. With P restricted to primes >3, the same assertion holds provided A,B have equal mod-3 residue counts, and without using the additional triple-conversion moves. There is no effectiveness claim for the density-one threshold.

Michael Nelson, [arXiv:2611.14580v2, Lemma 6.1 and Theorem 6.2](https://arxiv.org/html/2611.14580v2#S6.SS1), computes the integral group completion and builds a common auxiliary list of d primes in the matched-residue case. Neither that theorem nor the result here asserts that auxiliary factors can be cancelled inside the unsaturated ring. Nelson's B.5 asks for certain identities with NO auxiliary factor and for binary representations of every prime successor.

## 1. Three stages and their prime labels

For d≤2 the claim without any auxiliary move is immediate (at most one ordinary move). Write A=(p₁,…,p_d), B=(q₁,…,q_d), and P_i=Σ_{j≤i}p_j, Q_i=Σ_{j≤i}q_j. Fix separately the class t=1 or 2 mod 3. Below all lists, orders and conversion choices can depend on that class but are independent of the varying size of t.

**Unpack.** Put R₀=t. Sequentially replace (R_{i−1},p_i) by (U_i,R_i) where R_i=t+P_i−Σ_{j≤i}U_j. At the end set U_{d+1}=R_d. The d+1 labels U have sum t+n. The output side with q_i likewise admits sequential unpacking into W₁,…,W_d,S_d, where S_i=t+Q_i−Σ_{j≤i}W_j, S₀=t.

**Choose signatures and convert.** To prescribe the residues modulo 3 of U for the chosen t, use the following decisions, all on residues only. A nonzero input p_i passes straight through: U_i=p_i, R_i=R_{i−1} mod 3. An input p_i=3 splits with the nonzero carrier r=R_{i−1} as (r,0)→(−r,−r). All d+1 outputs are nonzero modulo 3. Apply the same rule to the q_i and record the target residues of W₁,…,W_d,S_d. Both resulting signatures have length d+1 and total t+n mod 3, so the counts of residue 1 differ by a multiple of three. Choose disjoint triples from the surplus sign in U until the counts agree; if U_{d+1} is chosen, take it as Z, not X or Y, in its triple. On each such triple (X,Y,Z), all initially of residue r, perform

    (X,Y) → (3,T=X+Y−3);     (3,Z) → (C,D=3+Z−C).

C is free (a separate parameter per triple); require C≡−r mod 3. The resulting labels T,C,D all have residue −r. Let V be the d+1-element list of unconverted U's and the triple outputs T,C,D. Permute V=(V₀,V₁,…,V_d) so that V_i agrees in residue with its output-side W_i for i≥1 and V₀ with S_d. In the >3 version choose matched orders of p_i,q_i so that no conversions are called for.

**Mix and repack.** Starting with F₀=V₀, for i=1,…,d use (F_{i−1},V_i)→(W_i,F_i) with
    F_i=V₀+⋯+V_i−Σ_{j≤i}W_j.
The W_i are fresh independent integer parameters. Since V and U both total t+n, F_d=S_d. The resulting list is precisely the q-side unpacking; run the latter in reverse. Conditional on the displayed labels being prime, these d unpacking moves, at most 2⌊(d+1)/3⌋ conversions, d mixing moves and d repacking moves prove the claimed path. The fixed label 3 is not counted by a varying prime weight.

## 2. The varying labels are a finite-complexity system

One integral affine coordinate system is (U₁,…,U_{d+1}, C's, W₁,…,W_d) with t=ΣU_j−n. Equivalently use (t,U₁,…,U_d,C's,W's): the change has determinant ±1. Count distinct occurrences of required labels only once: t; the U's; R_i for 1≤i<d; T,C,D of each conversion; the W's; F_i for 1≤i≤d; S_i for 1≤i<d. In particular F₀, R_d and S_d are already among them. Fixed endpoint primes and the constant conversion label 3 do not belong in the system.

Their linear parts are pairwise nonproportional over Q. In the first coordinate system t is the total of all U's, R_i a proper suffix containing the final U, and T a two-U sum never containing that final U. Unit vectors of U and these mutually distinct sums are nonproportional (d≥3). Each C has a new coordinate, D has linear part Z−C; these cannot coincide up to scaling with another label considered so far. The gradients of all d+1 V's are linearly independent: each conversion block maps (X,Y,Z,C) onto (X+Y,C,Z−C) with rank three, independently of all other blocks. Thus any nonempty sum of distinct V's has nonzero gradient, and no proper subset sum has the gradient of their total. Finally each F_i or S_i involves the negative prefix W₁+⋯+W_i plus a nonzero part in the earlier variables. Distinct prefix lengths distinguish them; at the same i<d the former contains a proper V-subsum, the latter the total. At i=d the two are a single counted label. This also separates all F/S labels from the standalone W_i. No variable label other than t depends on t alone, in the second chart.

For each fixed dyadic-type interval t∈[X,(1+ε)X] there is a box in the remaining variables of volume cX^m independent of t, all variable labels ≍_d X. Here m=d+#conversions+d and c>0 depends on d and the schedule. At the reference point set all U equal to X/(d+1), C=X/(2(d+1)), and W_i equal to the reference V_i ignoring O(n+1) shifts; all running labels are then positive multiples of X. For compact ranges choose sufficiently small ε>0 and sufficiently small fixed-width-as-a-fraction-of-X intervals around these independent U₁,…,U_d,C,W coordinates (U_{d+1} follows from t and the other U's); positivity and comparability persist for large X. One can use analogous scaled boxes on finitely many adjacent subintervals covering (X,2X].

## 3. Local admissibility for EVERY reduced class of the carrier

The specific extra constraints at 3 have already been arranged: choose the prescribed U residues and conversion C residues, then W_i=V_i modulo 3, so F_i=V₀ is nonzero and the q-side S_i are nonzero by its prescription. At 2 take odd U,C,W; every label is odd.

For any prime ℓ≥5 and any t≠0 mod ℓ, choose U₁,…,U_d in order. Exclude 0; exclude the one value giving R_i=0; if this U_i completes the (X,Y) pair of a conversion, exclude also its one value giving X+Y−3=0. No pair (X,Y) uses U_{d+1}=R_d, so this suffices for all U's, R_i and T's, including if ℓ divides some fixed p_i or q_i. Choose each C avoiding 0 and 3+Z. With V now known, choose W_i in order avoiding 0 and the up to two values making F_i or S_i zero. This excludes at most three residues at each stage. No hypothesis on which primes divide constants such as n,q_i+1, etc., is involved.

## 4. Relative density one, not just positive density

Here is the general fixed-fiber second-moment argument. In integral coordinates (t,z), dim z=m, let the forms be t and L_j(t,z) as above, distinct nonproportional, with each L_j having some z-dependence. Let λ(k)=1_{k prime}log k. For t in the short fixed-ratio interval set C_X(t)=Σ_{z in box}Π_j λ(L_j(t,z)). The system t, L_j(t,z), L_j(t,z') with two independent copies of z is again pairwise nonproportional: a nonshared form depends on its own copy of z. Apply the prime linear-forms theorem to both the one- and two-copy systems. A sufficient published formulation is Tao–Teräväinen [JEMS, Theorem 1.6](https://doi.org/10.4171/JEMS/1404), allowing bounded linear coefficients and affine intercepts O(X); prime powers in a specified form cost at most O_s(X^(D−1/2) log^(s+1)X) in D variables for either fixed system by slicing. The same applies if t is restricted to any fixed reduced residue class modulo H.

To make the variance small, fix w≥5 and H=∏_{ℓ≤w}ℓ and work one reduced r modulo H at a time, using the schedule for that r modulo 3. Give t≡r mod H in the interval probability proportional to λ(t); by the prime number theorem in fixed progressions this defines a normalized measure for large X. Put
    k_w(r)=Π_{ℓ≤w} E_{z mod ℓ} Π_j [ℓ/(ℓ−1)·1_{L_j(r,z) not 0 mod ℓ}].
Every factor is positive by §3. In the conditional first moment the factors at ℓ|H are exactly k_w(r), after the single prime t's measure is normalized away. In the two-copy moment they are exactly k_w(r)² by independence of z,z' at fixed t. This follows either by splitting all variables into classes or substituting t=r+Hz; the separate mean of λ(t) contributes H/φ(H). For ℓ>w the substitution in t is invertible. Excluding the finite bad primes (take w bigger than those for both fixed matrices), any two individual zero hyperplanes are independent mod ℓ. The local factors of both unconditional systems, INCLUDING t, are thus 1+O_d(ℓ^(−2)) by the first two inclusion–exclusion bounds, uniformly in the intercepts. Their respective tails beyond w equal 1+O_d(1/w).

Consequently, writing V_X=cX^m for the fixed section volume and E_r for the λ-probability above, for j=1,2,
    E_r[(C_X(t)/(V_X k_w(r)))^j] = 1+O_d(1/w)+o_{w,r,A,B}(1).
Here the constants in O_d(1/w) can be maximized over the two residue schedules; fixing w before X permits arbitrary growth of the constants in the o-term with w. The second moment is the full square; diagonal coincidences are permitted and already included. On C_X(t)=0 the squared normalized deviation from 1 is 1. Its expectation is O_d(1/w)+o(1), so the same bounds the relative bad mass in every reduced r and hence over all primes. Send X→∞ and then w→∞. On each fixed-ratio interval λ and unweighted relative densities have ratio 1+o(1); dyadic summation yields ordinary relative density one. Intersecting finitely many such density-one sets preserves the conclusion.

## 5. What the theorem says algebraically, and what it does not say

Over any field k put R=k[x_p:p∈P], let I be its binary-relation ideal, and J the kernel of x_p↦uv^p into k[u,v]. Then, for any finitely supported polynomial f,

    f∈J   iff   x_t f∈I for a relative-density-one set of primes t.

In fact if f∈J, within each bidegree its coefficients sum to zero, so it is a finite linear combination of differences of monomials of the same degree and weight. Apply the simultaneous finite-list result. Conversely for even one t, x_t f∈I implies f∈J since R/J is a domain and x_t≠0 in it. In particular the result describes exactly the prime-variable annihilation, in density, of J/I in the original unsaturated ring. It does **not** cancel any x_t in R/I, imply I=J, or construct any missing degree-two term. A prime successor that lacks a Goldbach pair has no y_q in Nelson's B.5; the one-variable theorem does not prove that y_q exists. The additional unstabilized positive-density-one assertion for B.5 identities is separate below.

### 6. Unstabilized cubic for almost every moving prime successor

Fix a prime q≥5 for which q+1=a+b with odd primes a,b, and write y_q for its quadratic monomial class in R/I. Then for a relative-density-one set of primes t, t+1 also has a prime-pair class y_t and the actual cubic identity

    x_q y_t = x_t y_q  in R/I

holds with at most three binary moves between suitable representatives. This has no extra variable on either side. It also holds simultaneously for any fixed finite list of represented q. In contrast, taking two FIXED represented q,q' in this sentence with a common moving t only kills the corresponding cubic difference AFTER multiplying it by x_t.

Indeed seek primes c=t+1−d, d, u, v=q+d−u, w=t+b−u. The five moving labels and the anchor t have nonproportional gradients (coordinates t,d,u). They give
    (q,c,d) → (c,u,v) → (u,a,w) → (a,b,t).
Choose t∈[X,2X], d∈[2X/5,X/2], u∈[3X/20,X/5], so all moving labels are positive and ≍X; the two other coordinates range independently of t. At 2 take d,u odd. At ℓ≥5, for EVERY nonzero t choose d avoiding 0,t+1, and u avoiding 0,q+d,t+b. For ℓ=3 swap a,b to avoid b≡0 unless both are 3, which occurs only for q=5. The table gives one pair (d,u) for each case, in F₃:
  
    (q,b)     t=1      t=2
    (1,1)    (1,1)    (1,1)
    (1,2)    (1,1)    (2,2)
    (2,0)    (1,2)    (1,1)
    (2,1)    (1,1)    (1,1)
    (2,2)    (1,1)    (1,2).

Thus §4 applies including q=5 and regardless of primes dividing q+1 or b. This settles an averaged row of [Nelson, Conjecture B.5](https://arxiv.org/html/2611.14580v2#A2.SS3), conditional ONLY on the fixed starting q+1 being represented; that condition is automatic for each q in the known finite verification range but not presently for every prime. It does not prove the full conjecture, does not show a single density-one set works simultaneously for all infinitely many q, and does not imply binary Goldbach.

[Exact symbolic and local controls](check_one_prime_catalyst.py) run with `python3 -O check_one_prime_catalyst.py`; the density-one statement is proved by the analytic argument in §4, not by the finite fixtures.
