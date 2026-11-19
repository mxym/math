# Exact global optimality of balanced flexibility at sufficiently high finite rates

Yongxian Zhang. AI-assisted research draft, not externally peer-reviewed. Uses the definitions and proved limiting theorem in CURVE.md, in turn conditional on Ameen–Sentenac–Yu (ASY), arXiv:2604.02295v2, Theorem 1 and Corollary 1. All asymptotic matching rates below already take n→∞ with each edge rate fixed. The new conclusion concerns these rates at **finite** flexibility parameter f; it is not inferred from uniform convergence alone.

**Theorem.** For every fixed 0<B<1 and α>0 there exists a finite f₀(α,B) such that for every f>f₀, the **unique** maximizing flexibility allocation among *all* b_L+b_R=B is b_L=b_R=B/2. The threshold here is existential, need not be uniform in B or α, and no assertion is made about lower finite rates, B=1, α=0, or finite-n optimizers. In particular this settles the full allocation question in one high-rate regime, not the global finite-parameter phase diagram.

Keep c=2α, s=1−B/2, p=s−δ, q=s+δ, d=α+f and e=2f. Denote the finite-f unmatched rate by M_f(δ). In the notation of (1) of CURVE.md it maximizes

    T_δ(y,z)=pX+(1−p)Z+q h(y)+(1−q)h(z)−1,
    X=exp[−c q y−d(1−q)z],  Z=exp[−d q y−e(1−q)z].         (1)

We work first on any fixed symmetric compact interior interval J=[−a,a], a<B/2, so the two class probabilities on both sides are bounded away from zero. Assume f>α. The maximization can be carried out on the common square [0,1]² without changing its value. In fact for y>0 the y derivative is −q[log y+p cX+(1−p)d Z]. It is strictly positive if y<exp[−pc−(1−p)d], the lower end of ASY's original interval. Likewise the z derivative is −(1−q)[log z+p dX+(1−p)eZ], strictly positive below exp[−pd−(1−p)e]. Thus clamping either coordinate up to the original lower end cannot worsen the objective. This is the weighted analogue of ASY's Equation (26). Continuity, the signs near zero and strict negativity of each coordinate derivative at 1 ensure every maximizer is in (0,1)² and satisfies

    y=exp[−p cX−(1−p)dZ],   z=exp[−p dX−(1−p)eZ].           (2)

**Transposed witnesses.** At a critical point the objective equals

    pX+(1−p)Z+q y+(1−q)z−1
    +p q c X y +p(1−q)d X z +(1−p)q d Z y +(1−p)(1−q)e Z z.

By (1)–(2) this is exactly T_{−δ}(X,Z), the roles of left and right interchanged. Since M_f is even by transposition of the original bipartite random graph, the paired point is a maximizer for the opposite split whenever (y,z) is a maximizer at δ. All such trials, including when evaluated at another split, are admissible using the common square. Neither the critical points nor their values need be unique.

**A positive-curvature witness lemma.** For all sufficiently large f (depending on J,B,α), at every δ∈J and every maximizing (y,z) at δ, at least one of the following two functions of v has strictly positive second derivative for **all** v∈J:

    v ↦ T_v(y,z),               v ↦ T_{−v}(X,Z).                (3)

Both functions equal M_f(δ) at v=δ, and are dominated by M_f(v) for all v. For the latter bound use evenness.

To prove the lemma, write p'=s−v, q'=s+v. For a fixed trial (y,z), set A=cy−dz, D=dy−ez. Its second derivative in the split variable v is exactly

    exp[−c q'y−d(1−q')z] [p' A²+2A]
      +exp[−d q'y−e(1−q')z] [(1−p')D²−2D].                 (4)

The h terms are affine. Reflection v↦−v does not change the second derivative sign when it is positive on symmetric J.

Suppose the lemma fails along f_j→∞; choose violating splits and maximizers and pass to a subsequence with δ_j→δ, (y_j,z_j)→(u,w). By CURVE.md's uniform convergence the limiting optimal value is U(δ)=max(0,H(δ)), with H the scalar maximum. We consider all limits.

* If w>0, both exponentials in (1) vanish (the flexible right proportion has a strictly positive lower bound). The limiting value q h(u)+(1−q)h(w)−1 can be nonnegative only if u=w=1, because h≤1 with equality just at 1. Then A/f_j→−1 and D/f_j→−1. For all large j both brackets in (4) are strictly positive for every v∈J: the first has A<−2/min_J(p'), and D<0 suffices for the second. This gives the first witness in (3).
* If w=0 and u>0, the second exponential in (1) vanishes. We must have f_j z_j→0. Otherwise on a further subsequence f_j z_j is at least some ε>0; the first exponential term then loses a strictly positive constant compared to p exp(−c q u), as p>0, 1−q>0. The limiting objective would be strictly less than G_δ(u)≤H(δ)≤U(δ), impossible. Thus A→c u>0 and the first exponential in (4) is uniformly bounded below by a positive constant on J. The second exponential is at most exp[−d min_J(q')u/2] for large j, while its bracket is bounded in absolute value by a constant times (1+f_j)². Hence (4) is uniformly strictly positive for large j. This also gives the first witness, without differentiating an unknown optimizer.
* If w=u=0, both h terms vanish. The limiting optimal value is nonnegative, whereas p_j X_j+(1−p_j)Z_j−1≤0. Since p and 1−p are positive, necessarily X_j,Z_j→1. Use the transposed witness (X_j,Z_j) in (4), evaluated at the opposite split: exactly as in the first case both of its brackets are strictly positive throughout J for all large j. This gives the second witness in (3).

Each case contradicts the assumed sequence. Compactness thus proves the lemma with a single f threshold for all splits in J and all their maximizing witnesses.

**From local witnesses to global optimality.** For any two distinct splits v₁,v₂ in J and any strict convex combination δ of them, choose a witness from (3) associated to a maximizer at δ. Its value there is M_f(δ). Its strict convexity on J bounds that value strictly below the weighted average of its own values at v₁,v₂, hence strictly below the corresponding weighted average of M_f(v₁),M_f(v₂). Thus M_f is even and strictly convex on J for all sufficiently large f. In particular its unique minimum there is zero *split* δ=0 (not necessarily zero unmatched rate).

By CURVE.md, H(B/2)>0 and H(B/2)>H(0). Choose once and for all 0<a<B/2 so that H(a)>max(0,H(0)); then U(v)≥H(a)>U(0) for |v|≥a. Uniform convergence on the entire split interval excludes all these v from minimizing M_f for all sufficiently large f. Combining this exclusion with the result on J gives the claimed unique balanced optimizer. ∎

**Prior scope.** This proof employs ASY's full variational matching identity and adapts its common-domain extension. FMZ's March 2026 paper highlights the possibility of a noncanonical optimizer at finite rates as an unresolved analytic question. ASY compare the two canonical allocations and partially address the high-f regime; neither a strict limiting endpoint comparison nor a limit curve with a plateau by itself implies eventual exact optimality over *all* splits. Producing stable strictly convex trial functions, sometimes by transferring a low-low witness to its transposed high-high partner, is what establishes this conclusion here.
